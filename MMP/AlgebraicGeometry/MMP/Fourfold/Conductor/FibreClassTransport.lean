module

public import MMP.AlgebraicGeometry.Variety.ParameterPoint
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFamilyTriviality
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFibreGeneric
public import MMP.AlgebraicTopology.BorelMoore.FibreClassConstancy
public import MMP.AlgebraicGeometry.CycleMap.Stacks.FibreClassConstancy
public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup
public import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.PrimeDivisorCurveFamily
import MMP.AlgebraicGeometry.Morphisms.GenericSmoothness
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ContractedEdgeInjectivity
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.Topology.KrullDimensionProperClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.IdealSheafSubscheme
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Transport of fibre curve classes along the exceptional family

Let `r : Z ⟶ Y` be a curve-and-point exceptional model with exceptional divisor `F = ∑ Fᵢ`, and
`T ⊆ Sing Y` a curve. Over a general open `T°` of `T`, the family `F^an ∩ r⁻¹(Δ) → Δ` over a small
disk `Δ ∋ b` is the product `F_b × Δ` by a homeomorphism `Φ` preserving every component `E` of `F`
(`MMP.Fourfold.exists_homeomorph_prod_exceptionalFibre`). For `t ∈ Δ` the slice `Φ_t = Φ(·, t)`
carries every component `G_b` of a fibre `E_b` onto a component `G_t` of `E_t`, and the induced
isomorphism `H_2(G_b, ℚ) ≅ H_2(G_t, ℚ)` sends the class of every double curve `C_b ⊆ G_b ∩ E'` to
the class of the double curve `Φ_t(C_b)`, and the class of the curves cut on `G_b` by a
`ℚ`-divisor of `E` to the class of the curves it cuts on `G_t`.

## Main definitions

* `MMP.Fourfold.IsExceptionalTrivialization`: a component-preserving product structure
  `F_b × Δ ≃ₜ F_Δ` over a preconnected `Δ ∋ b`, relatively open in `T(ℂ)`.
* `MMP.Fourfold.transportHomeomorph`: the homeomorphism `A ≃ₜ B` induced by a slice `Φ_t` between
  sets `A ⊆ F_b` and `B ⊆ F_t` it matches.
* `MMP.Fourfold.fibreComponentTransport`: the isomorphism `H_2(G_b, ℚ) ≃ₗ[ℚ] H_2(G_t, ℚ)` induced
  by `Φ_t`.

## Main results

* `MMP.Fourfold.exists_maximal_fibre_transport`: `Φ_t` carries fibre components to fibre
  components.
* `MMP.Fourfold.fibreComponentTransport_doubleCurve`: transport of double-curve classes.
* `MMP.Fourfold.PrimeDivisorFamily.fibreComponentTransport_eq`: along the algebraic family of a
  prime divisor `P` of `E`, the transport carries the curves cut by `P` on `G_b` to those cut on
  `G_t`.
* `MMP.Fourfold.fibreComponentTransport_restrictionClass`: transport of the classes cut by a
  `ℚ`-divisor.
* `MMP.Fourfold.exists_transport_fibreClasses`: the product germ together with the transport.

## Implementation notes

The fibre components and curves are compared through their complex points in `Z(ℂ)`, which a
closed immersion identifies with the complex points of the subvariety. The classes are
constant along the family: for a family `V → T°` of curves (a double curve family, or a component
of `P ∩ G_{T°}`), Fulton's Lemma 19.1.3 identifies `cl(V_t)` with `f^*u_t ∩ cl(V)`, and by
Lemma 19.2(c) its image under the trivialization does not depend on `t`. For a prime divisor `P`
of `E` the trivialization need not preserve `P`: the classes of the fibres of `P` are read in
`E_b(ℂ)` through the product structure of the family of fibres of `E`, and the part over the
clopen piece `G_b(ℂ)` is kept (the components of the general fibres of `E` are disjoint).

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1–19.2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP Topology
open MMP.Intersection.Scheme (Subvariety dimension)
open MMP.UnderlyingSpace
open scoped MMP.SubschemeOver

namespace MMP.Fourfold

open MMP.Mori

/-! ### The homeomorphism induced by a slice -/

section Slice

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  {r : Z ⟶ Y} [r.IsOver (Spec (.of ℂ))] {F : Divisor Z}
  {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)}

/-- The point of `F_b × Δ` over a point `w` of `F_Δ` lies over `r(w)`. -/
theorem snd_symm_apply_of_mapFun_eq
    (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
    (hΦ : ∀ p, mapFun r (Φ p : UnderlyingSpace ℂ Z) = p.2)
    (w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)) :
    ((Φ.symm w).2 : UnderlyingSpace ℂ Y) = mapFun r (w : UnderlyingSpace ℂ Z) := by
  rw [← hΦ, Φ.apply_symm_apply]

/-- **The homeomorphism induced by a slice.** For `t ∈ Δ`, if the slice `Φ_t` of a product
structure `Φ : F_b × Δ ≃ₜ F_Δ` over `Δ` carries `A ⊆ F_b` exactly onto `B ⊆ F_t`, then it
restricts to a homeomorphism `A ≃ₜ B`. -/
noncomputable def transportHomeomorph
    (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
    (hΦ : ∀ p, mapFun r (Φ p : UnderlyingSpace ℂ Z) = p.2) (t : Δ)
    {A B : Set (UnderlyingSpace ℂ Z)}
    (hA : A ⊆ pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b})
    (hB : B ⊆ pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {(t : UnderlyingSpace ℂ Y)})
    (hAB : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈ A ↔ (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ B) :
    A ≃ₜ B where
  toFun a := ⟨Φ (⟨a, hA a.2⟩, t), (hAB _).1 a.2⟩
  invFun w := ⟨(Φ.symm ⟨w, (hB w.2).1, by
      change mapFun r (w : UnderlyingSpace ℂ Z) ∈ Δ
      rw [(hB w.2).2]; exact t.2⟩).1, by
    set p := Φ.symm ⟨w, (hB w.2).1, by
      change mapFun r (w : UnderlyingSpace ℂ Z) ∈ Δ
      rw [(hB w.2).2]; exact t.2⟩ with hp
    have h2 : p.2 = t := Subtype.ext ((snd_symm_apply_of_mapFun_eq Φ hΦ _).trans (hB w.2).2)
    refine (hAB p.1).2 ?_
    have : Φ (p.1, t) = Φ p := by rw [← h2]
    rw [this, hp, Φ.apply_symm_apply]
    exact w.2⟩
  left_inv a := by
    apply Subtype.ext
    simp only
    have : Φ.symm (Φ (⟨a, hA a.2⟩, t)) = (⟨a, hA a.2⟩, t) := Φ.symm_apply_apply _
    simp only [Subtype.coe_eta, this]
  right_inv w := by
    apply Subtype.ext
    simp only
    set q : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ) := ⟨w, (hB w.2).1, by
      change mapFun r (w : UnderlyingSpace ℂ Z) ∈ Δ
      rw [(hB w.2).2]; exact t.2⟩
    have h2 : (Φ.symm q).2 = t :=
      Subtype.ext ((snd_symm_apply_of_mapFun_eq Φ hΦ _).trans (hB w.2).2)
    have : Φ ((Φ.symm q).1, t) = Φ (Φ.symm q) := by rw [← h2]
    change ((Φ ((Φ.symm q).1, t) : _) : UnderlyingSpace ℂ Z) = w
    rw [this, Φ.apply_symm_apply]
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_subtype_val.comp (Φ.continuous.comp ?_)) _
    exact (Continuous.subtype_mk (continuous_subtype_val) _).prodMk continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_subtype_val.comp (continuous_fst.comp
      (Φ.symm.continuous.comp ?_))) _
    exact continuous_subtype_val.subtype_mk _

/-- On a point `a` of `A`, the slice `transportHomeomorph Φ hΦ t hA hB hAB` is `Φ (a, t)`. -/
@[simp]
theorem coe_transportHomeomorph_apply
    (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
    (hΦ : ∀ p, mapFun r (Φ p : UnderlyingSpace ℂ Z) = p.2) (t : Δ)
    {A B : Set (UnderlyingSpace ℂ Z)}
    (hA : A ⊆ pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b})
    (hB : B ⊆ pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {(t : UnderlyingSpace ℂ Y)})
    (hAB : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈ A ↔ (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ B) (a : A) :
    (transportHomeomorph Φ hΦ t hA hB hAB a : UnderlyingSpace ℂ Z) = Φ (⟨a, hA a.2⟩, t) :=
  rfl

end Slice

/-! ### Smooth schemes are reduced -/

/-- **A scheme smooth over a field is reduced**: its local rings are regular local rings, hence
domains. Applied to the general fibres of a family of curves, it makes their fundamental cycles
the sums of their components. -/
theorem isReduced_of_smooth {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [Smooth f] : IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x ↦ by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field f x
    haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
    exact isReduced_of_noZeroDivisors
  exact isReduced_of_isReduced_stalk X

/-! ### Exceptional trivializations -/

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] {r : Z ⟶ Y} [r.IsOver (Spec (.of ℂ))] {F D : Divisor Z}

/-- An *exceptional trivialization* over `Δ ∋ b`: a product structure `Φ : F_b × Δ ≃ₜ F_Δ` over
`Δ`, the identity over `b`, preserving every component of `F`, with `Δ ⊆ U(ℂ)` preconnected and
relatively open in `T(ℂ)`. -/
structure IsExceptionalTrivialization (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] (F : Divisor Z)
    (T : IrreducibleCloseds Y) (U : Y.Opens) {b : UnderlyingSpace ℂ Y}
    {Δ : Set (UnderlyingSpace ℂ Y)} (hbΔ : b ∈ Δ)
    (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)) : Prop where
  subset : Δ ⊆ pointsOver (K := ℂ) (U : Set Y)
  isOpen : ∃ O, IsOpen O ∧ Δ = O ∩ pointsOver (K := ℂ) (T : Set Y)
  isPreconnected : IsPreconnected Δ
  mapFun_eq : ∀ p, mapFun r (Φ p : UnderlyingSpace ℂ Z) = p.2
  apply_base : ∀ z, (Φ (z, ⟨b, hbΔ⟩) : UnderlyingSpace ℂ Z) = z
  mem_iff : ∀ E ∈ F.support, ∀ p, (Φ p : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) ↔
    (p.1 : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z)

/-! ### The isomorphism of fibre-component homology -/

/-- The isomorphism of rational Borel–Moore homology induced by a homeomorphism: push-forward
along `e`, with inverse push-forward along `e.symm`. -/
noncomputable def homologyEquivOfHomeomorph {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (j : ℤ) :
    borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) j ≃ₗ[ℚ]
      borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B) j where
  toLinearMap := (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (e : C(A, B))) e.isProperMap j).hom
  invFun := (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (e.symm : C(B, A))) e.symm.isProperMap j).hom
  left_inv := fun a ↦ by
    change (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (e.symm : C(B, A))) e.symm.isProperMap j).hom
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (e : C(A, B))) e.isProperMap j).hom a) = a
    rw [← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp]
    have : TopCat.ofHom (e : C(A, B)) ≫ TopCat.ofHom (e.symm : C(B, A)) = 𝟙 _ :=
      TopCat.ext fun x ↦ e.symm_apply_apply x
    simp only [this, borelMooreHomology.pushforward_id]
    rfl
  right_inv := fun a ↦ by
    change (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (e : C(A, B))) e.isProperMap j).hom
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (e.symm : C(B, A))) e.symm.isProperMap j).hom a) = a
    rw [← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp]
    have : TopCat.ofHom (e.symm : C(B, A)) ≫ TopCat.ofHom (e : C(A, B)) = 𝟙 _ :=
      TopCat.ext fun x ↦ e.apply_symm_apply x
    simp only [this, borelMooreHomology.pushforward_id]
    rfl

/-- `homologyEquivOfHomeomorph e j` is the push-forward along `e`. -/
theorem homologyEquivOfHomeomorph_apply {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (j : ℤ) (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) j) :
    homologyEquivOfHomeomorph e j a = (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (e : C(A, B))) e.isProperMap j).hom a :=
  rfl

/-- The complex points of a closed subscheme `i : X ⟶ Z` are homeomorphic to the points of `Z(ℂ)`
over its image. -/
noncomputable def homeomorphPointsOverRange {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    (i : X ⟶ Z) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] :
    UnderlyingSpace ℂ X ≃ₜ pointsOver (K := ℂ) (Set.range i) :=
  ((isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) i).isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (range_map_of_isClosedImmersion (K := ℂ) i))

/-- The image in `Z` of a closed subvariety `G` of a component `E` of `F`. -/
theorem range_ι_comp_subschemeι {E : Mori.PrimeDivisor Z}
    (G : Subvariety E.idealSheaf.subscheme) :
    Set.range (G.ι ≫ E.idealSheaf.subschemeι) =
      E.idealSheaf.subschemeι.base '' (G.support : Set _) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.IdealSheafData.range_subschemeι, Subvariety.support_eq]

/-- **The isomorphism `H_2(G_b) ≅ H_2(G_t)` induced by a slice `Φ_t`**, for fibre components
`G_b ⊆ E_b`, `G_t ⊆ E_t` whose complex points `Φ_t` matches. -/
noncomputable def fibreComponentTransport [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    {T : IrreducibleCloseds Y} {U : Y.Opens}
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) (t : Δ) {E : Mori.PrimeDivisor Z}
    (hE : E ∈ F.support) {Gb Gt : Subvariety E.idealSheaf.subscheme}
    (hGb : (Gb.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {b.toHom (IsLocalRing.closedPoint ℂ)})
    (hGt : (Gt.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
    (hGbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈
        pointsOver (E.idealSheaf.subschemeι.base '' (Gb.support : Set _)) ↔
      (Φ (z, t) : UnderlyingSpace ℂ Z) ∈
        pointsOver (E.idealSheaf.subschemeι.base '' (Gt.support : Set _))) (n : ℕ) :
    RationalHomology Gb.toScheme n ≃ₗ[ℚ] RationalHomology Gt.toScheme n :=
  let e : UnderlyingSpace ℂ Gb.toScheme ≃ₜ UnderlyingSpace ℂ Gt.toScheme :=
    ((homeomorphPointsOverRange (Gb.ι ≫ E.idealSheaf.subschemeι)).trans
      (Homeomorph.setCongr (by rw [range_ι_comp_subschemeι]))).trans
    ((transportHomeomorph Φ hΦ.mapFun_eq t (pointsOver_image_subset_fibre hE hGb)
      (pointsOver_image_subset_fibre hE hGt) hGbt).trans
      ((Homeomorph.setCongr (by rw [range_ι_comp_subschemeι])).trans
        (homeomorphPointsOverRange (Gt.ι ≫ E.idealSheaf.subschemeι)).symm))
  homologyEquivOfHomeomorph e (n : ℤ)

/-- An exceptional trivialization over `U` is one over every larger open. -/
theorem IsExceptionalTrivialization.mono {T : IrreducibleCloseds Y} {U U' : Y.Opens}
    (hUU' : U ≤ U') {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) :
    IsExceptionalTrivialization r F T U' hbΔ Φ where
  subset := hΦ.subset.trans (pointsOver_mono hUU')
  isOpen := hΦ.isOpen
  isPreconnected := hΦ.isPreconnected
  mapFun_eq := hΦ.mapFun_eq
  apply_base := hΦ.apply_base
  mem_iff := hΦ.mem_iff

/-! ### Transport of fibre components and of their curve classes -/

/-- **Fibre components are transported.** Over a general open `U` of `T`, for every exceptional
trivialization `Φ` over `Δ ∋ b` and `t ∈ Δ`, every component `G_b` of a fibre `E_b` is carried by
`Φ_t` onto a component `G_t` of `E_t`: the components of the general fibres are disjoint, so they
are the connected components of `E_t(ℂ)`, which the homeomorphism `E_b(ℂ) ≃ₜ E_t(ℂ)` permutes. -/
theorem exists_maximal_fibre_transport
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ (b : UnderlyingSpace ℂ Y) (Δ : Set (UnderlyingSpace ℂ Y)) (hbΔ : b ∈ Δ)
        (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
          ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)),
        IsExceptionalTrivialization r F T U hbΔ Φ →
        ∀ (t : Δ) (E : F.support) (Gb : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2}),
          Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
            {b.toHom (IsLocalRing.closedPoint ℂ)}) (Gb.1.support : Set _) →
          ∃ Gt : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
            Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
              {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
              (Gt.1.support : Set _) ∧
            ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
              (z : UnderlyingSpace ℂ Z) ∈
                pointsOver (E.1.idealSheaf.subschemeι.base '' (Gb.1.support : Set _)) ↔
              (Φ (z, t) : UnderlyingSpace ℂ Z) ∈
                pointsOver (E.1.idealSheaf.subschemeι.base '' (Gt.1.support : Set _)) := by
  obtain ⟨U, hU, hc⟩ := exists_maximal_fibre_transport_of_homeomorph hM T hT1
  refine ⟨U, hU, fun b Δ hbΔ Φ hΦ t E Gb hGb ↦ ?_⟩
  have hmem : ∀ s ∈ Δ, s.toHom (IsLocalRing.closedPoint ℂ) ∈ (U : Set Y) ∩ T := fun s hs ↦ by
    obtain ⟨O, -, hO⟩ := hΦ.isOpen
    exact ⟨hΦ.subset hs, (hO ▸ hs).2⟩
  have hFt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b} ↔
      (Φ (z, t) : UnderlyingSpace ℂ Z) ∈
        pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {(t : UnderlyingSpace ℂ Y)} :=
    fun z ↦ iff_of_true z.2 ⟨(Φ (z, t)).2.1, hΦ.mapFun_eq (z, t)⟩
  obtain ⟨Gt, hGt, hiff⟩ := hc b t (hmem b hbΔ) (hmem t t.2)
    (transportHomeomorph Φ hΦ.mapFun_eq t subset_rfl subset_rfl hFt)
    (fun E hE z ↦ hΦ.mem_iff E hE _) E
    ⟨⟨Gb.1.ideal, Gb.1.isIntegral⟩, by obtain ⟨n, h1, h2⟩ := Gb.2; exact ⟨n, h1, h2⟩⟩ hGb
  exact ⟨⟨⟨Gt.1.ideal, Gt.1.isIntegral⟩, by obtain ⟨n, h1, h2⟩ := Gt.2; exact ⟨n, h1, h2⟩⟩,
    hGt, hiff⟩

/-- **The homeomorphism of matched curves.** For closed subschemes `j_b : C_b ⟶ Z` and
`j_t : C_t ⟶ Z` inside the fibres `F_b` and `F_t` whose complex points the slice `Φ_t` matches,
the induced homeomorphism `C_b(ℂ) ≃ₜ C_t(ℂ)`. -/
noncomputable def curveTransportHomeomorph {b : UnderlyingSpace ℂ Y}
    {Δ : Set (UnderlyingSpace ℂ Y)}
    (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
    (hΦ : ∀ p, mapFun r (Φ p : UnderlyingSpace ℂ Z) = p.2) (t : Δ)
    {Cb Ct : Scheme.{0}} [Cb.Over (Spec (.of ℂ))] [Ct.Over (Spec (.of ℂ))]
    (jb : Cb ⟶ Z) (jt : Ct ⟶ Z) [IsClosedImmersion jb] [IsClosedImmersion jt]
    [jb.IsOver (Spec (.of ℂ))] [jt.IsOver (Spec (.of ℂ))]
    (hb : pointsOver (K := ℂ) (Set.range jb) ⊆
      pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b})
    (ht : pointsOver (K := ℂ) (Set.range jt) ⊆
      pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {(t : UnderlyingSpace ℂ Y)})
    (hbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (Set.range jb) ↔
        (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (Set.range jt)) :
    UnderlyingSpace ℂ Cb ≃ₜ UnderlyingSpace ℂ Ct :=
  (homeomorphPointsOverRange jb).trans
    ((transportHomeomorph Φ hΦ t hb ht hbt).trans (homeomorphPointsOverRange jt).symm)

/-- The image in `Z(ℂ)` of `curveTransportHomeomorph Φ hΦ t jb jt hb ht hbt x` is
`Φ (jb x, t)`. -/
theorem map_curveTransportHomeomorph_apply {b : UnderlyingSpace ℂ Y}
    {Δ : Set (UnderlyingSpace ℂ Y)}
    (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
    (hΦ : ∀ p, mapFun r (Φ p : UnderlyingSpace ℂ Z) = p.2) (t : Δ)
    {Cb Ct : Scheme.{0}} [Cb.Over (Spec (.of ℂ))] [Ct.Over (Spec (.of ℂ))]
    (jb : Cb ⟶ Z) (jt : Ct ⟶ Z) [IsClosedImmersion jb] [IsClosedImmersion jt]
    [jb.IsOver (Spec (.of ℂ))] [jt.IsOver (Spec (.of ℂ))]
    (hb : pointsOver (K := ℂ) (Set.range jb) ⊆
      pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b})
    (ht : pointsOver (K := ℂ) (Set.range jt) ⊆
      pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {(t : UnderlyingSpace ℂ Y)})
    (hbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (Set.range jb) ↔
        (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (Set.range jt))
    (x : UnderlyingSpace ℂ Cb) :
    mapFun jt (curveTransportHomeomorph Φ hΦ t jb jt hb ht hbt x) =
      (Φ (⟨mapFun jb x, hb ((range_map_of_isClosedImmersion (K := ℂ) jb).symm ▸
        Set.mem_range_self x)⟩, t) : UnderlyingSpace ℂ Z) := by
  have := ((homeomorphPointsOverRange jt).apply_symm_apply
    ((transportHomeomorph Φ hΦ t hb ht hbt) (homeomorphPointsOverRange jb x)))
  exact congrArg Subtype.val this

/-! ### The algebraic family of a double surface -/

/-- **The algebraic family of a double surface over a general open `U` of `T`**: a dominant
morphism `f : V → B` from a complex surface to a non-singular complex curve, with `B(ℂ)`
embedded onto `(U ∩ T)(ℂ)` and `V(ℂ)` onto the points of the double surface `S` over `U`,
compatibly with `r`, whose fibres are reduced with pairwise disjoint one-dimensional components,
every curve of `S` over a point of `B` being one of them. -/
structure DoubleSurfaceFamily (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] (F : Divisor Z)
    (T : IrreducibleCloseds Y) (σ : DoubleSurface F) (U : Y.Opens) where
  /-- The base curve. -/
  B : Scheme.{0}
  [overB : B.Over (Spec (.of ℂ))]
  [smoothB : IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))]
  /-- The base is a curve. -/
  dim_B : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ))
  /-- The total space, a complex surface. -/
  V : Scheme.{0}
  [overV : V.Over (Spec (.of ℂ))]
  [complexV : IsComplexScheme V]
  [integralV : IsIntegral V]
  /-- The total space is a surface. -/
  dimension_V : ((1 + 1 : ℕ) : WithBot ℕ∞) = dimension V
  /-- The family. -/
  f : V ⟶ B
  [isOver_f : f.IsOver (Spec (.of ℂ))]
  [isDominant_f : IsDominant f]
  /-- The base mapped to `Y`. -/
  jB : B ⟶ Y
  [isOver_jB : jB.IsOver (Spec (.of ℂ))]
  /-- The total space mapped to `Z`. -/
  jV : V ⟶ Z
  [isOver_jV : jV.IsOver (Spec (.of ℂ))]
  /-- The family is compatible with `r`. -/
  comm : f ≫ jB = jV ≫ r
  /-- `jB` is a topological embedding on complex points. -/
  isEmbedding_jB : Topology.IsEmbedding (mapFun (K := ℂ) jB)
  /-- The complex points of `B` map onto `(U ∩ T)(ℂ)`. -/
  range_jB : Set.range (mapFun (K := ℂ) jB) = pointsOver (K := ℂ) ((U : Set Y) ∩ T)
  /-- `jV` is a topological embedding on complex points. -/
  isEmbedding_jV : Topology.IsEmbedding (mapFun (K := ℂ) jV)
  /-- The complex points of `V` map onto the points of `S` over `U`. -/
  range_jV : Set.range (mapFun (K := ℂ) jV) =
    pointsOver (K := ℂ) σ.carrier ∩ mapFun r ⁻¹' pointsOver (K := ℂ) (U : Set Y)
  /-- Every fibre `V_s` is reduced. -/
  isReduced_fibre : ∀ s : ParameterPoint B, IsReduced (ParameterPoint.fibre f s)
  /-- Distinct irreducible components of a fibre `V_s` are disjoint. -/
  disjoint_fibre : ∀ s : ParameterPoint B, ∀ A ∈ irreducibleComponents (ParameterPoint.fibre f s),
    ∀ A' ∈ irreducibleComponents (ParameterPoint.fibre f s), A ≠ A' → Disjoint A A'
  /-- Every irreducible component of a fibre `V_s` is one-dimensional. -/
  hasDim_fibre : ∀ (s : ParameterPoint B) (ξ : genericPoints (ParameterPoint.fibre f s)),
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) ξ.1 = (1 : ℕ)
  /-- A curve of `S` over a point `s` of `B` is a component of the fibre `V_s`. -/
  exists_component : ∀ (s : ParameterPoint B) (C : Scheme.{0}) [C.Over (Spec (.of ℂ))]
    [IsIntegral C] [LocallyOfFiniteType (C ↘ Spec (.of ℂ))] [QuasiCompact (C ↘ Spec (.of ℂ))]
    (c : C ⟶ Z) [IsClosedImmersion c] [c.IsOver (Spec (.of ℂ))],
    ((1 : ℕ) : WithBot ℕ∞) = dimension C →
    pointsOver (K := ℂ) (Set.range c) ⊆ pointsOver (K := ℂ) σ.carrier →
    pointsOver (K := ℂ) (Set.range c) ⊆ mapFun r ⁻¹' {mapFun (K := ℂ) jB s.complexPoint} →
    ∃ (y : ParameterPoint.fibre f s) (_ : y ∈ genericPoints (ParameterPoint.fibre f s))
      (_ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) y = (1 : ℕ))
      (g : C ⟶ (Stacks.Chow.integralComponentAt y).subscheme) (_ : IsIso g)
      (_ : g.IsOver (Spec (.of ℂ))),
      g ≫ (Stacks.Chow.integralComponentAt y).subschemeι ≫ ParameterPoint.fibreι f s ≫ jV = c

attribute [instance] DoubleSurfaceFamily.overB DoubleSurfaceFamily.smoothB
  DoubleSurfaceFamily.overV DoubleSurfaceFamily.complexV DoubleSurfaceFamily.integralV
  DoubleSurfaceFamily.isOver_f DoubleSurfaceFamily.isDominant_f DoubleSurfaceFamily.isOver_jB
  DoubleSurfaceFamily.isOver_jV

section familyProduct

variable [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] [TopologicalSpace.NoetherianSpace Z]
  {T : IrreducibleCloseds Y} {σ : DoubleSurface F} {U : Y.Opens}

/-- The complex points of a double surface lie over the support of `F`. -/
theorem mem_pointsOver_supp_of_mem_carrier (σ : DoubleSurface F) {z : UnderlyingSpace ℂ Z}
    (hz : z ∈ pointsOver (K := ℂ) σ.carrier) : z ∈ pointsOver (K := ℂ) (F.supp : Set Z) := by
  change z.toHom _ ∈ (F.supp : Set Z)
  rw [DivisorWithCoeffs.coe_supp]
  exact Set.mem_iUnion₂.2 ⟨σ.fst, σ.fst_mem, (σ.carrier_subset hz).1⟩

/-- On complex points, `r ∘ jV = jB ∘ f`. -/
theorem DoubleSurfaceFamily.mapFun_r_jV (𝔉 : DoubleSurfaceFamily r F T σ U)
    (v : UnderlyingSpace ℂ 𝔉.V) :
    mapFun r (mapFun (K := ℂ) 𝔉.jV v) = mapFun (K := ℂ) 𝔉.jB (mapFun (K := ℂ) 𝔉.f v) := by
  apply UnderlyingSpace.ext
  change (v.toHom ≫ 𝔉.jV) ≫ r = (v.toHom ≫ 𝔉.f) ≫ 𝔉.jB
  rw [Category.assoc, Category.assoc, 𝔉.comm]

/-- The open of `B(ℂ)` over an open `O` of `Y(ℂ)`. -/
def DoubleSurfaceFamily.baseOpens (𝔉 : DoubleSurfaceFamily r F T σ U)
    {O : Set (UnderlyingSpace ℂ Y)} (hO : IsOpen O) :
    TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ 𝔉.B)) :=
  ⟨mapFun (K := ℂ) 𝔉.jB ⁻¹' O, hO.preimage (continuous_mapFun _)⟩

/-- A point `w` of `B(ℂ)` lies in `baseOpens hO` exactly when `jB w` lies in `O ∩ T(ℂ)`. -/
theorem DoubleSurfaceFamily.mem_baseOpens_iff (𝔉 : DoubleSurfaceFamily r F T σ U)
    {O : Set (UnderlyingSpace ℂ Y)} (hO : IsOpen O) (w : UnderlyingSpace ℂ 𝔉.B) :
    w ∈ 𝔉.baseOpens hO ↔ mapFun (K := ℂ) 𝔉.jB w ∈ O ∩ pointsOver (K := ℂ) (T : Set Y) := by
  refine ⟨fun h ↦ ⟨h, ?_⟩, fun h ↦ h.1⟩
  have h1 : mapFun (K := ℂ) 𝔉.jB w ∈ pointsOver (K := ℂ) ((U : Set Y) ∩ T) :=
    𝔉.range_jB ▸ Set.mem_range_self w
  rw [pointsOver_inter] at h1
  exact h1.2

/-- A point `w` of `B(ℂ)` lies in `baseOpens hO` exactly when `jB w` lies in `Δ`. -/
theorem DoubleSurfaceFamily.mem_baseOpens_iff' (𝔉 : DoubleSurfaceFamily r F T σ U)
    {Δ O : Set (UnderlyingSpace ℂ Y)} (hO : IsOpen O)
    (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y)) (w : UnderlyingSpace ℂ 𝔉.B) :
    w ∈ 𝔉.baseOpens hO ↔ mapFun (K := ℂ) 𝔉.jB w ∈ Δ := by
  rw [hΔO]
  exact 𝔉.mem_baseOpens_iff hO w

omit [IsComplexScheme Z] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
  [TopologicalSpace.NoetherianSpace Z] in
/-- Every point of the base `Δ` of an exceptional trivialization is a complex point of `B`. -/
theorem DoubleSurfaceFamily.mem_range_jB_of_mem (𝔉 : DoubleSurfaceFamily r F T σ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {O : Set (UnderlyingSpace ℂ Y)}
    (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y)) {s : UnderlyingSpace ℂ Y} (hs : s ∈ Δ) :
    s ∈ Set.range (mapFun (K := ℂ) 𝔉.jB) := by
  rw [𝔉.range_jB, pointsOver_inter]
  exact ⟨hΦ.subset hs, (hΔO ▸ hs).2⟩

/-- The open of the base curve over the base `Δ` of an exceptional trivialization is
connected. -/
theorem DoubleSurfaceFamily.connectedSpace_baseOpens (𝔉 : DoubleSurfaceFamily r F T σ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {O : Set (UnderlyingSpace ℂ Y)}
    (hO : IsOpen O) (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y)) :
    ConnectedSpace (𝔉.baseOpens hO) := by
  obtain ⟨wb, hwb⟩ := 𝔉.mem_range_jB_of_mem hΦ hΔO hbΔ
  have himg : mapFun (K := ℂ) 𝔉.jB '' (𝔉.baseOpens hO : Set (UnderlyingSpace ℂ 𝔉.B)) = Δ := by
    ext s
    refine ⟨fun ⟨w, hw, hws⟩ ↦ hws ▸ (𝔉.mem_baseOpens_iff' hO hΔO w).1 hw, fun hs ↦ ?_⟩
    obtain ⟨w, rfl⟩ := 𝔉.mem_range_jB_of_mem hΦ hΔO hs
    exact ⟨w, (𝔉.mem_baseOpens_iff' hO hΔO w).2 hs, rfl⟩
  exact Subtype.connectedSpace
    ⟨⟨wb, (𝔉.mem_baseOpens_iff' hO hΔO wb).2 (hwb ▸ hbΔ)⟩,
      𝔉.isEmbedding_jB.isInducing.isPreconnected_image.1 (himg ▸ hΦ.isPreconnected)⟩

/-- The point of `F_Δ` given by `x ∈ S_b` and `w ∈ B(ℂ)` over `Δ`. -/
theorem DoubleSurfaceFamily.mem_range_jV (𝔉 : DoubleSurfaceFamily r F T σ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ)
    (x : {x : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) //
      (x : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier}) (δ : Δ) :
    (Φ (x.1, δ) : UnderlyingSpace ℂ Z) ∈ Set.range (mapFun (K := ℂ) 𝔉.jV) := by
  rw [𝔉.range_jV]
  refine ⟨(mem_pointsOver_carrier_iff_of_homeomorph hΦ.isPreconnected hbΔ Φ hΦ.apply_base
    hΦ.mem_iff σ _).2 x.2, ?_⟩
  change mapFun r (Φ (x.1, δ) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (U : Set Y)
  rw [hΦ.mapFun_eq]
  exact hΦ.subset δ.2

/-- **The product structure of a double-surface family**, from an exceptional trivialization:
`S_b × W ≃ₜ f⁻¹(W)`, `(x, w) ↦ Φ(x, w)` read in `V(ℂ)`. -/
noncomputable def DoubleSurfaceFamily.prodHomeomorph (𝔉 : DoubleSurfaceFamily r F T σ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {O : Set (UnderlyingSpace ℂ Y)}
    (hO : IsOpen O) (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y)) :
    (TopCat.of {x : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) //
      (x : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier}) × 𝔉.baseOpens hO ≃ₜ
      preimageOpens (TopCat.ofHom (map (K := ℂ) 𝔉.f)) (𝔉.baseOpens hO) :=
  let eV := 𝔉.isEmbedding_jV.toHomeomorph
  have hV : ∀ y, mapFun (K := ℂ) 𝔉.jV (eV.symm y) = y.1 := fun y ↦
    congrArg Subtype.val (eV.apply_symm_apply y)
  have hWΔ : ∀ w, w ∈ 𝔉.baseOpens hO ↔ mapFun (K := ℂ) 𝔉.jB w ∈ Δ :=
    𝔉.mem_baseOpens_iff' hO hΔO
  have hz : ∀ v : preimageOpens (TopCat.ofHom (map (K := ℂ) 𝔉.f)) (𝔉.baseOpens hO),
      mapFun (K := ℂ) 𝔉.jV v.1 ∈ pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ ∧
      mapFun (K := ℂ) 𝔉.jV v.1 ∈ pointsOver (K := ℂ) σ.carrier := fun v ↦ by
    have h1 : mapFun (K := ℂ) 𝔉.jV v.1 ∈ Set.range (mapFun (K := ℂ) 𝔉.jV) := ⟨v.1, rfl⟩
    rw [𝔉.range_jV] at h1
    refine ⟨⟨mem_pointsOver_supp_of_mem_carrier σ h1.1, ?_⟩, h1.1⟩
    change mapFun r (mapFun (K := ℂ) 𝔉.jV v.1) ∈ Δ
    rw [𝔉.mapFun_r_jV]
    exact (hWΔ _).1 v.2
  { toFun := fun p ↦ ⟨eV.symm ⟨_, 𝔉.mem_range_jV hΦ p.1 ⟨_, (hWΔ _).1 p.2.2⟩⟩, by
      change mapFun (K := ℂ) 𝔉.f _ ∈ 𝔉.baseOpens hO
      rw [hWΔ, ← 𝔉.mapFun_r_jV]
      have h := congrArg Subtype.val (eV.apply_symm_apply
        ⟨_, 𝔉.mem_range_jV hΦ p.1 ⟨_, (hWΔ _).1 p.2.2⟩⟩)
      change mapFun (K := ℂ) 𝔉.jV _ = _ at h
      rw [h, hΦ.mapFun_eq]
      exact (hWΔ _).1 p.2.2⟩
    invFun := fun v ↦ (⟨(Φ.symm ⟨_, (hz v).1⟩).1, by
        have h := (mem_pointsOver_carrier_iff_of_homeomorph hΦ.isPreconnected hbΔ Φ
          hΦ.apply_base hΦ.mem_iff σ (Φ.symm ⟨_, (hz v).1⟩)).1
        rw [Φ.apply_symm_apply] at h
        exact h (hz v).2⟩, ⟨mapFun (K := ℂ) 𝔉.f v.1, v.2⟩)
    left_inv := by
      rintro ⟨x, w⟩
      have hv := hV ⟨_, 𝔉.mem_range_jV hΦ x ⟨_, (hWΔ _).1 w.2⟩⟩
      have key : ∀ q : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ),
          (q : UnderlyingSpace ℂ Z) = Φ (x.1, ⟨_, (hWΔ _).1 w.2⟩) →
          (Φ.symm q).1 = x.1 := fun q hq ↦ by
        rw [show q = Φ (x.1, ⟨_, (hWΔ _).1 w.2⟩) from Subtype.ext hq, Φ.symm_apply_apply]
      refine Prod.ext (Subtype.ext (key _ hv)) (Subtype.ext ?_)
      apply 𝔉.isEmbedding_jB.injective
      change mapFun (K := ℂ) 𝔉.jB (mapFun (K := ℂ) 𝔉.f _) = _
      rw [← 𝔉.mapFun_r_jV, hv, hΦ.mapFun_eq]
    right_inv := by
      intro v
      apply Subtype.ext
      apply 𝔉.isEmbedding_jV.injective
      refine (hV _).trans ?_
      have key : ∀ (q : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ)
          (δ : Δ), (δ : UnderlyingSpace ℂ Y) = mapFun r (Φ q : UnderlyingSpace ℂ Z) →
          (Φ (q.1, δ) : UnderlyingSpace ℂ Z) = Φ q := fun q δ h ↦ by
        rw [show (q.1, δ) = q from Prod.ext rfl (Subtype.ext (h.trans (hΦ.mapFun_eq q)))]
      refine (key _ _ ?_).trans ?_
      · rw [Φ.apply_symm_apply]
        exact (𝔉.mapFun_r_jV v.1).symm
      · rw [Φ.apply_symm_apply]
    continuous_toFun := by
      refine Continuous.subtype_mk (eV.symm.continuous.comp (Continuous.subtype_mk
        (continuous_subtype_val.comp (Φ.continuous.comp ?_)) _)) _
      exact (continuous_subtype_val.comp continuous_fst).prodMk (Continuous.subtype_mk
        ((continuous_mapFun _).comp (continuous_subtype_val.comp continuous_snd)) _)
    continuous_invFun := by
      refine Continuous.prodMk (Continuous.subtype_mk (continuous_fst.comp
        (Φ.symm.continuous.comp (Continuous.subtype_mk
          ((continuous_mapFun _).comp continuous_subtype_val) _))) _)
        (Continuous.subtype_mk ((continuous_mapFun _).comp continuous_subtype_val) _) }

/-- The image under `jV` of `prodHomeomorph hΦ hO hΔO p` is `Φ (p.1, jB p.2)`. -/
theorem DoubleSurfaceFamily.exists_mapFun_jV_prodHomeomorph (𝔉 : DoubleSurfaceFamily r F T σ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {O : Set (UnderlyingSpace ℂ Y)}
    (hO : IsOpen O) (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y))
    (p : (TopCat.of {x : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) //
      (x : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier}) × 𝔉.baseOpens hO) :
    ∃ h : mapFun (K := ℂ) 𝔉.jB p.2 ∈ Δ,
      mapFun (K := ℂ) 𝔉.jV (𝔉.prodHomeomorph hΦ hO hΔO p : UnderlyingSpace ℂ 𝔉.V) =
        Φ (p.1.1, ⟨_, h⟩) :=
  ⟨_, congrArg Subtype.val (𝔉.isEmbedding_jV.toHomeomorph.apply_symm_apply _)⟩

/-- The image under `f` of `prodHomeomorph hΦ hO hΔO p` is `p.2`. -/
theorem DoubleSurfaceFamily.mapFun_f_prodHomeomorph (𝔉 : DoubleSurfaceFamily r F T σ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {O : Set (UnderlyingSpace ℂ Y)}
    (hO : IsOpen O) (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y))
    (p : (TopCat.of {x : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) //
      (x : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier}) × 𝔉.baseOpens hO) :
    map (K := ℂ) 𝔉.f (𝔉.prodHomeomorph hΦ hO hΔO p : UnderlyingSpace ℂ 𝔉.V) =
      (p.2 : UnderlyingSpace ℂ 𝔉.B) := by
  obtain ⟨h, hp⟩ := 𝔉.exists_mapFun_jV_prodHomeomorph hΦ hO hΔO p
  apply 𝔉.isEmbedding_jB.injective
  change mapFun (K := ℂ) 𝔉.jB (mapFun (K := ℂ) 𝔉.f _) = _
  rw [← 𝔉.mapFun_r_jV, hp, hΦ.mapFun_eq]

/-- A complex point of the fibre `V_u`, read in `Z` through `jV`, is `Φ` of its transport through
`prodHomeomorph hΦ hO hΔO` over the image of `u` in `Δ`. -/
theorem DoubleSurfaceFamily.exists_mapFun_jV_fibreι (𝔉 : DoubleSurfaceFamily r F T σ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {O : Set (UnderlyingSpace ℂ Y)}
    (hO : IsOpen O) (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y))
    (u : ParameterPoint 𝔉.B) (hu : u.complexPoint ∈ 𝔉.baseOpens hO)
    (v₀ : UnderlyingSpace ℂ (ParameterPoint.fibre 𝔉.f u)) :
    ∃ h, mapFun (K := ℂ) 𝔉.jV (mapFun (K := ℂ) (ParameterPoint.fibreι 𝔉.f u) v₀) =
      Φ ((fibrePointsTransportHom (𝔉.prodHomeomorph hΦ hO hΔO)
        (𝔉.mapFun_f_prodHomeomorph hΦ hO hΔO) u hu v₀).1,
        ⟨mapFun (K := ℂ) 𝔉.jB u.complexPoint, h⟩) := by
  set ψ := 𝔉.prodHomeomorph hΦ hO hΔO
  have hψ := 𝔉.mapFun_f_prodHomeomorph hΦ hO hΔO
  set v : ((TopCat.ofHom (map (K := ℂ) 𝔉.f)).hom ⁻¹' {u.complexPoint} : Set _) :=
    ParameterPoint.fibreComplexPointsHom 𝔉.f u v₀
  have hv : (ψ ((fibreHomeomorphOfProd ψ hψ hu) v, ⟨_, hu⟩) : UnderlyingSpace ℂ 𝔉.V) = v.1 :=
    congrArg Subtype.val ((fibreHomeomorphOfProd ψ hψ hu).symm_apply_apply v)
  obtain ⟨h, hp⟩ := 𝔉.exists_mapFun_jV_prodHomeomorph hΦ hO hΔO
    ((fibreHomeomorphOfProd ψ hψ hu) v, ⟨_, hu⟩)
  exact ⟨h, by rwa [hv] at hp⟩

end familyProduct

/-- In a `T₀` space, a set of points whose closures lie in a finite family of sets is finite. -/
theorem finite_of_closure_singleton_mem {X : Type*} [TopologicalSpace X] [T0Space X]
    {p : X → Prop} {S : Set (Set X)} (hS : S.Finite) {J : Set (Subtype p)}
    (hJ : ∀ y ∈ J, closure {y.1} ∈ S) : J.Finite :=
  Set.Finite.of_finite_image (f := fun y : Subtype p ↦ closure {y.1})
    (hS.subset (by rintro _ ⟨y, hy, rfl⟩; exact hJ y hy))
    fun _ _ _ _ h ↦ Subtype.ext (inseparable_iff_closure_eq.mpr h).eq

/-- The image of the closure of a point `x` of `X` under `h : X ⟶ X'` is the range of the
integral closed subscheme `closure {x}` (Stacks, `integralComponentAt`) followed by `h`. -/
private theorem range_subschemeι_integralComponentAt_comp {X X' : Scheme.{0}} (x : X) (h : X ⟶ X') :
    Set.range ((Stacks.Chow.integralComponentAt x).subschemeι ≫ h).base =
      h.base '' closure {x} := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.IdealSheafData.range_subschemeι, Stacks.Chow.coe_support_integralComponentAt]

/-- Over `ℂ`, a point whose closure has dimension `n` has relative dimension `n` (Stacks, Tag
02QO). -/
private theorem relativeDimension_eq_of_topologicalKrullDim_closure_eq {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType p] (x : X) (n : ℕ)
    (h : topologicalKrullDim (closure ({x} : Set X)) = (n : WithBot ℕ∞)) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction p x =
      n := by
  have hnn := Stacks.Chow.relativeDimension_nonneg (Stacks.Chow.fieldChowSituation ℂ)
    (fun _ _ ↦ rfl) p x
  rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ p x] at h
  have h' : (Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      p x).toNat = n := by
    exact_mod_cast h
  omega

/-- A double surface whose image under `r` contains a curve `T` maps onto `T`. -/
theorem image_carrier_eq_of_subset (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1) (σ : DoubleSurface F)
    (hTS : (T : Set Y) ⊆ r.base '' σ.carrier) : r.base '' σ.carrier = (T : Set Y) := by
  set K : Set Y := r.base '' (σ.fst.support : Set Z)
  have hKirr : IsIrreducible K := by
    have : IsIrreducible (σ.fst.support : Set Z) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
    exact this.image _ r.continuous.continuousOn
  have hσK : r.base '' σ.carrier ⊆ K :=
    Set.image_mono (σ.carrier_subset.trans Set.inter_subset_left)
  have hKT : K = T := by
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hKirr T.isClosed
      (hTS.trans hσK) (Ne.symm hne) (ne_top_of_le_ne_top (by decide)
        (hM.topologicalKrullDim_image_le σ.fst σ.fst_mem))
    rw [hT1] at hlt
    exact absurd (hlt.trans_le (hM.topologicalKrullDim_image_le σ.fst σ.fst_mem)) (lt_irrefl _)
  exact le_antisymm (hKT ▸ hσK) hTS

/-- In an irreducible space of nonzero dimension, a closed point is not the generic point. -/
theorem ne_genericPoint_of_isClosed_singleton {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [IrreducibleSpace X] (hX : 0 < topologicalKrullDim X) {d : X} (hd : IsClosed {d}) :
    d ≠ genericPoint X := by
  intro h
  have huniv := (genericPoint_spec X).def
  rw [← h, hd.closure_eq] at huniv
  haveI : Subsingleton X := ⟨fun a b ↦ by
    have ha : a ∈ ({d} : Set X) := huniv ▸ trivial
    have hb : b ∈ ({d} : Set X) := huniv ▸ trivial
    exact ha.trans hb.symm⟩
  exact (hX.trans_le (topologicalKrullDim_zero_of_discreteTopology X)).false

/-- A double surface of an snc divisor on a fourfold is two-dimensional. -/
theorem topologicalKrullDim_carrier_eq_two [IsIntegral Z] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))]
    [IsProper (Z ↘ Spec (.of ℂ))]
    (hsnc : DivisorWithCoeffs.IsSNC (Z ↘ Spec (.of ℂ)) F) (hdimZ : topologicalKrullDim Z = 4)
    (σ : DoubleSurface F) : topologicalKrullDim σ.carrier = ((2 : ℕ) : WithBot ℕ∞) := by
  have hE3 : ∀ i : F.support, topologicalKrullDim i.1.idealSheaf.subscheme = (3 : ℕ) := by
    intro i
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
    exact ConductorBlowup.topologicalKrullDim_support_eq_three hdimZ i.1
  have h := MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity.dim_surfI_eq hsnc hE3 σ
  rwa [MMP.Mori.topologicalKrullDim_subscheme_eq,
    MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity.surfI,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_closure,
    (ConductorBlowup.isClosed_carrier σ).closure_eq] at h

/-- If `ι` has range `A` and `s ⊆ A`, the open `V = ι⁻¹((A \ s)ᶜ)` maps onto `s`. -/
theorem range_ι_comp_of_eq_preimage_compl_diff {X S : Scheme.{0}} (ι : X ⟶ S) {A s : Set S}
    (hA : Set.range ι.base = A) (hs : s ⊆ A) (V : X.Opens)
    (hV : (V : Set X) = ι.base ⁻¹' (A \ s)ᶜ) : Set.range (V.ι ≫ ι).base = s := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, hV]
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    by_contra h
    exact hu ⟨hA ▸ ⟨u, rfl⟩, h⟩
  · intro hw
    obtain ⟨u, rfl⟩ : w ∈ Set.range ι.base := hA ▸ hs hw
    exact ⟨u, fun h ↦ h.2 hw, rfl⟩

/-- A lift through a closed immersion of a morphism with the same image is surjective. -/
theorem surjective_lift_of_range_eq {X W S : Scheme.{0}} (j : X ⟶ S) [IsClosedImmersion j]
    (g : W ⟶ S) (hker : j.ker ≤ g.ker) (hrange : Set.range g.base = Set.range j.base) :
    Function.Surjective (IsClosedImmersion.lift j g hker).base := by
  intro t
  obtain ⟨x, hx⟩ : j.base t ∈ Set.range g.base := hrange ▸ ⟨t, rfl⟩
  refine ⟨x, j.isClosedEmbedding.injective ?_⟩
  change (IsClosedImmersion.lift j g hker ≫ j).base x = j.base t
  rw [IsClosedImmersion.lift_fac]
  exact hx

/-- The restriction of a surjective morphism over an open is surjective. -/
theorem surjective_morphismRestrict {X S : Scheme.{0}} {p : X ⟶ S}
    (hp : Function.Surjective p.base) (U : S.Opens) : Function.Surjective (p ∣_ U).base := by
  intro y
  obtain ⟨x, hx⟩ := hp y.1
  refine ⟨⟨x, show p.base x ∈ U from hx ▸ y.2⟩, U.ι.isOpenEmbedding.injective ?_⟩
  change ((p ∣_ U) ≫ U.ι).base _ = _
  rw [morphismRestrict_ι]
  exact hx

/-- **A double surface dominating `T` has an algebraic family over a general open of `T`**:
the smooth surface `S = E ∩ E'` (snc), over the normalization-free base `T°` where `T` is smooth
and `S → T°` is smooth (generic smoothness). -/
theorem exists_doubleSurfaceFamily [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1) (σ : DoubleSurface F)
    (hTS : (T : Set Y) ⊆ r.base '' σ.carrier) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ Nonempty (DoubleSurfaceFamily r F T σ U) := by
  classical
  have hres := hM.isResolution
  haveI : MMP.Mori.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hres.1
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hres.2.2.2.1).isProper
  haveI : MMP.Mori.IsVariety ℂ (r ≫ Y ↘ Spec (.of ℂ)) := hres.2.1
  have hdimZ : topologicalKrullDim Z = 4 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (Y ↘ Spec (.of ℂ))
      (r ≫ Y ↘ Spec (.of ℂ)) hres.2.2.2.2]
    exact hM.topologicalKrullDim_eq
  haveI : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]
    exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have := noetherianSpace_of_isComplexScheme (X := Z)
  haveI : IsProper (Y ↘ Spec (.of ℂ)) :=
    (IsProjectiveMorphism.isProjective hM.isProjectiveVariety.isProjective).isProper
  haveI : IsProper (Z ↘ Spec (.of ℂ)) := by rw [← hM.comp_eq]; infer_instance
  have hsnc : DivisorWithCoeffs.IsSNC (Z ↘ Spec (.of ℂ)) F := hM.comp_eq ▸ hM.isSNC
  have hσT := image_carrier_eq_of_subset hM T hT1 σ hTS
  set E₁ := σ.fst
  set E₂ := σ.snd
  set K : Z.IdealSheafData := E₁.idealSheaf ⊔ E₂.idealSheaf with hKdef
  have hKsupp : (K.support : Set Z) = (E₁.support : Set Z) ∩ E₂.support := by
    rw [hKdef, Scheme.IdealSheafData.support_sup]; rfl
  set ι := K.subschemeι with hι
  haveI : Smooth (ι ≫ Z ↘ Spec (.of ℂ)) :=
    smooth_sup_idealSheaf_of_isSNC (Z ↘ Spec (.of ℂ)) hsnc σ.fst_mem σ.snd_mem
  have hrangeι : Set.range ι.base = (E₁.support : Set Z) ∩ E₂.support := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι, hKsupp]
  have hsupp : ∀ E : MMP.Mori.PrimeDivisor Z, IsClosed (E.support : Set Z) := fun E ↦ by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isClosed_closure
  have hE₁₂ : IsClosed ((E₁.support : Set Z) ∩ E₂.support) := (hsupp _).inter (hsupp _)
  -- the open subscheme over `σ`
  obtain ⟨x₀, hx₀, hσx₀⟩ := σ.isComponent
  have hσopen : IsOpen (ι.base ⁻¹' (((E₁.support : Set Z) ∩ E₂.support) \ σ.carrier)ᶜ) := by
    refine (isOpen_compl_iff.2 ?_).preimage ι.base.hom.continuous
    rw [← hσx₀]
    exact isClosed_diff_connectedComponentIn'' hE₁₂ x₀
  set V₀ : K.subscheme.Opens := ⟨_, hσopen⟩ with hV₀
  set φ : V₀.toScheme ⟶ Z := V₀.ι ≫ ι with hφ
  have hrangeφ : Set.range φ.base = σ.carrier :=
    range_ι_comp_of_eq_preimage_compl_diff ι hrangeι σ.carrier_subset V₀ rfl
  have hφemb : Topology.IsEmbedding φ.base :=
    (ι.isClosedEmbedding.isEmbedding).comp V₀.ι.isOpenEmbedding.isEmbedding
  have hσirr : IsIrreducible σ.carrier :=
    MMP.Fourfold.ConductorBlowup.isIrreducible_carrier (Z ↘ Spec (.of ℂ)) hsnc σ
  letI : V₀.toScheme.Over (Spec (.of ℂ)) := ⟨V₀.ι ≫ K.subscheme ↘ Spec (.of ℂ)⟩
  haveI : V₀.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : φ.IsOver (Spec (.of ℂ)) := by rw [hφ]; infer_instance
  haveI : Smooth (V₀.toScheme ↘ Spec (.of ℂ)) := by
    change Smooth (V₀.ι ≫ ι ≫ Z ↘ Spec (.of ℂ)); infer_instance
  haveI : IsReduced K.subscheme := isReduced_of_smooth (ι ≫ Z ↘ Spec (.of ℂ))
  haveI : IrreducibleSpace V₀.toScheme := by
    rw [irreducibleSpace_def]
    have h := isIrreducible_preimage_of_isEmbedding' hφemb hσirr hrangeφ.symm.subset
    rwa [← hrangeφ, Set.preimage_range] at h
  haveI : IsIntegral V₀.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : CompactSpace K.subscheme := ι.isClosedEmbedding.compactSpace
  haveI : LocallyOfFiniteType (V₀.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (V₀.ι ≫ ι ≫ Z ↘ Spec (.of ℂ)); infer_instance
  haveI : QuasiCompact (V₀.toScheme ↘ Spec (.of ℂ)) := by
    change QuasiCompact (V₀.ι ≫ ι ≫ Z ↘ Spec (.of ℂ)); infer_instance
  -- `σ ⟶ T` and generic smoothness
  let Tc : Closeds Y := ⟨(T : Set Y), T.isClosed⟩
  set j := curveι T with hj
  have hrangej : Set.range j.base = (T : Set Y) := by
    rw [hj, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hrangef : Set.range (φ ≫ r).base = (T : Set Y) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrangeφ, hσT]
  have hker : j.ker ≤ (φ ≫ r).ker := by
    rw [hj, Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine le_of_eq (congrArg _ (TopologicalSpace.Closeds.ext ?_))
    rw [TopologicalSpace.Closeds.coe_closure, hrangef, T.isClosed.closure_eq]
    rfl
  let p := IsClosedImmersion.lift j (φ ≫ r) hker
  have hp : p ≫ j = φ ≫ r := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIntegral (curveScheme T) :=
    MMP.Fourfold.isIntegral_subscheme_vanishingIdeal Tc T.isIrreducible
  haveI : p.IsOver (Spec (.of ℂ)) := ⟨by
    change p ≫ j ≫ Y ↘ Spec (.of ℂ) = φ ≫ Z ↘ Spec (.of ℂ)
    rw [← Category.assoc, hp, Category.assoc, hM.comp_eq]⟩
  haveI : LocallyOfFiniteType ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (j ≫ Y ↘ Spec (.of ℂ)); infer_instance
  haveI : QuasiCompact ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change QuasiCompact (j ≫ Y ↘ Spec (.of ℂ)); infer_instance
  haveI : IsSeparated ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change IsSeparated (j ≫ Y ↘ Spec (.of ℂ)); infer_instance
  obtain ⟨U', hU'd, hU's, hU'sm, -⟩ := MMP.exists_dense_smooth_restrict_of_smooth (K := ℂ) p
  have hpsurj : Function.Surjective p.base :=
    surjective_lift_of_range_eq j (φ ≫ r) hker (hrangef.trans hrangej.symm)
  haveI : IsDominant p := ⟨hpsurj.denseRange⟩
  have hdT : topologicalKrullDim (curveScheme T) = 1 := by
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hT1
  haveI : JacobsonSpace (curveScheme T) :=
    LocallyOfFiniteType.jacobsonSpace ((curveScheme T) ↘ Spec (.of ℂ))
  obtain ⟨d, hdU', hdcl⟩ := nonempty_inter_closedPoints hU'd.nonempty U'.isOpen.isLocallyClosed
  have hdη := ne_genericPoint_of_isClosed_singleton (by rw [hdT]; decide) hdcl
  letI : U'.toScheme.Over (Spec (.of ℂ)) := ⟨U'.ι ≫ (curveScheme T) ↘ Spec (.of ℂ)⟩
  obtain ⟨hBns, hBdim⟩ := isSmoothVariety_opens_of_le_smoothLocus ℂ hdT U' hU's hdU' hdη
  haveI := hBns
  haveI : U'.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  set Vo : V₀.toScheme.Opens := p ⁻¹ᵁ U' with hVo
  letI : Vo.toScheme.Over (Spec (.of ℂ)) := ⟨Vo.ι ≫ V₀.toScheme ↘ Spec (.of ℂ)⟩
  haveI : Vo.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have hVone : (Vo : Set V₀.toScheme).Nonempty := by
    obtain ⟨x, hx⟩ := hpsurj d
    exact ⟨x, show p.base x ∈ U' from hx ▸ hdU'⟩
  haveI : Nonempty Vo.toScheme := hVone.to_subtype
  haveI : IsIntegral Vo.toScheme := isIntegral_of_isOpenImmersion Vo.ι
  haveI : IsComplexScheme K.subscheme := IsComplexScheme.of_isClosedImmersion ι
  haveI : IsComplexScheme V₀.toScheme := isComplexScheme_opens V₀
  haveI : IsComplexScheme Vo.toScheme := isComplexScheme_opens Vo
  set f : Vo.toScheme ⟶ U'.toScheme := p ∣_ U' with hf
  haveI : f.IsOver (Spec (.of ℂ)) := ⟨by
    change f ≫ U'.ι ≫ _ = Vo.ι ≫ _
    rw [← Category.assoc, hf, morphismRestrict_ι, Category.assoc, comp_over p (Spec (.of ℂ))]⟩
  have hfsurj : Function.Surjective f.base := surjective_morphismRestrict hpsurj U'
  haveI : IsDominant f := ⟨hfsurj.denseRange⟩
  set jB : U'.toScheme ⟶ Y := U'.ι ≫ j with hjB
  set jV : Vo.toScheme ⟶ Z := (Vo.ι ≫ V₀.ι) ≫ ι with hjV
  have hjV' : jV = Vo.ι ≫ φ := by rw [hjV, hφ, Category.assoc]
  have hφr : ∀ u, r.base (φ.base u) = j.base (p.base u) := fun u ↦ by
    change (φ ≫ r).base u = (p ≫ j).base u
    rw [hp]
  obtain ⟨W, hW, hWU⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.1 U'.2
  have hmemW : ∀ t, j.base t ∈ W ↔ t ∈ U' := fun t ↦ by
    rw [← Set.mem_preimage, hWU]; rfl
  have hrangejB : Set.range jB.base = W ∩ (T : Set Y) := by
    rw [hjB, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    change j.base '' U'.carrier = _
    rw [← hWU, Set.image_preimage_eq_inter_range, hrangej]
  have hrangejV : Set.range jV.base = σ.carrier ∩ r.base ⁻¹' W := by
    have hVoW : (Vo : Set V₀.toScheme) = φ.base ⁻¹' (r.base ⁻¹' W) := by
      ext u
      exact (hmemW (p.base u)).symm.trans (by rw [Set.mem_preimage, Set.mem_preimage, hφr])
    rw [hjV', Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, hVoW,
      Set.image_preimage_eq_inter_range, hrangeφ, Set.inter_comm]
  have hdσ := topologicalKrullDim_carrier_eq_two hsnc hdimZ σ
  have hdV₀ : topologicalKrullDim V₀.toScheme = ((2 : ℕ) : WithBot ℕ∞) := by
    rw [← hdσ]
    exact (hφemb.toHomeomorph.trans (Homeomorph.setCongr hrangeφ)).isHomeomorph
      |>.topologicalKrullDim_eq
  have hdVo : topologicalKrullDim Vo.toScheme = ((2 : ℕ) : WithBot ℕ∞) :=
    (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ _ (_ ↘ Spec (.of ℂ)) _
      (TopologicalSpace.Opens.isOpen Vo) hVone).symm.trans hdV₀
  have hdB : topologicalKrullDim U'.toScheme = ((1 : ℕ) : WithBot ℕ∞) := by
    haveI := hBdim
    exact topologicalKrullDim_eq_of_smoothOfRelativeDimension (K := ℂ) 1
  have hfib := fibre_props_of_smooth f hdB hdVo
  have hcomm : f ≫ jB = jV ≫ r := by
    change (p ∣_ U') ≫ U'.ι ≫ j = ((Vo.ι ≫ V₀.ι) ≫ ι) ≫ r
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hp, hφ]
    simp only [Category.assoc]
    rfl
  have hjBinj : Function.Injective jB.base :=
    j.isClosedEmbedding.injective.comp U'.ι.isOpenEmbedding.injective
  have hrangeV : σ.carrier ∩ r.base ⁻¹' Set.range jB.base ⊆ Set.range jV.base := by
    rw [hrangejV, hrangejB]
    exact fun z hz ↦ ⟨hz.1, hz.2.1⟩
  have hjBpts := range_mapFun_comp_eq_pointsOver (K := ℂ) U'.ι j
  have hjVpts := range_mapFun_comp_eq_pointsOver (K := ℂ) (Vo.ι ≫ V₀.ι) ι
  refine ⟨⟨W, hW⟩, ⟨j.base d, (hmemW d).2 hdU', hrangej ▸ ⟨d, rfl⟩⟩, ⟨{
    B := U'.toScheme
    dim_B := hBdim
    V := Vo.toScheme
    dimension_V := ?_
    f := f
    jB := jB
    jV := jV
    comm := hcomm
    isEmbedding_jB := hjBpts.2
    range_jB := ?_
    isEmbedding_jV := hjVpts.2
    range_jV := ?_
    isReduced_fibre := fun s ↦ (hfib s).1
    disjoint_fibre := fun s ↦ (hfib s).2.1
    hasDim_fibre := ?_
    exists_component := fun s C _ _ _ _ c _ _ hC1 hcS hcr ↦
      exists_component_of_immersion_of_le (ConductorBlowup.isClosed_carrier σ) f jB
        hjBinj jV (Vo.ι ≫ V₀.ι) ι rfl hcomm hrangeV s (fun A hA ↦ ((hfib s).2.2 A hA).le) C c
        hC1 hcS hcr }⟩⟩
  · change _ = topologicalKrullDim _
    rw [hdVo]
  · rw [hjBpts.1, hrangejB]; rfl
  · rw [hjVpts.1, hrangejV, pointsOver_inter]
    congr 1
  · intro s ξ
    haveI : LocallyOfFiniteType (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) := by
      change LocallyOfFiniteType (ParameterPoint.fibreι f s ≫ Vo.toScheme ↘ Spec (.of ℂ))
      infer_instance
    exact relativeDimension_eq_of_topologicalKrullDim_closure_eq _ ξ.1 1
      ((hfib s).2.2 _ ξ.2)

/-- The complex points of a composite are read through both maps. -/
private theorem topCatOfHom_map_comp {A B D : Scheme.{0}} [A.Over (Spec (.of ℂ))]
    [B.Over (Spec (.of ℂ))] [D.Over (Spec (.of ℂ))] (e : A ⟶ B) (i : B ⟶ D)
    [e.IsOver (Spec (.of ℂ))] [i.IsOver (Spec (.of ℂ))] :
    TopCat.ofHom (map (K := ℂ) (e ≫ i)) =
      TopCat.ofHom (map (K := ℂ) e) ≫ TopCat.ofHom (map (K := ℂ) i) := by
  ext p : 1
  apply UnderlyingSpace.ext
  change (mapFun (K := ℂ) (e ≫ i) p).toHom = (mapFun (K := ℂ) i (mapFun (K := ℂ) e p)).toHom
  rw [toHom_mapFun, toHom_mapFun, toHom_mapFun, Category.assoc]

/-- **The fundamental class of a closed complex variety is the cycle class of its generic
point.** For a closed immersion `h : C ⟶ Y` of a complex variety of dimension `k` onto the
closure of a point `y` of delta-dimension `k`, `h_*[C] = cl_Y(y)`. -/
private theorem pushforward_fundamentalClass_eq_pointCycleClass {Cv Yv : Scheme.{0}}
    [Cv.Over (Spec (.of ℂ))] [Yv.Over (Spec (.of ℂ))] [IsComplexScheme Cv] [IsComplexScheme Yv]
    [IsIntegral Cv] (h : Cv ⟶ Yv) [IsClosedImmersion h] [h.IsOver (Spec (.of ℂ))] {k : ℕ}
    (hk : (k : WithBot ℕ∞) = dimension Cv)
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Cv)) (2 * k : ℕ)}
    (hμ : IsVarietyFundamentalClass ℚ hk μ) (y : Yv)
    (hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Yv ↘ Spec (.of ℂ)) y = k)
    (hry : Set.range h.base = closure {y}) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) h))
        (isProperMap_map (K := ℂ) h) (2 * k : ℕ)).hom μ = Chow.pointCycleClass ℚ y hy := by
  haveI : IrreducibleSpace Cv := irreducibleSpace_of_isIntegral Cv
  have hη := Chow.relativeDimension_genericPoint_eq ℂ (Cv ↘ Spec (.of ℂ)) (n := k) hk.symm
  have h1 := Chow.pointCycleClass_eq_of_closure_eq_univ (R := ℚ) (genericPoint Cv) hη
    (genericPoint_spec Cv).def hk hμ
  rw [← h1]
  refine (Chow.pushforward_pointCycleClass ℚ h (genericPoint Cv) hη).trans ?_
  have hgy : h.base (genericPoint Cv) = y := by
    have hc : closure ({h.base (genericPoint Cv)} : Set Yv) = closure {y} := by
      rw [← hry, ← Set.image_singleton, h.isClosedMap.closure_image_eq_of_continuous h.continuous,
        (genericPoint_spec Cv).def, Set.image_univ]
    exact (inseparable_iff_closure_eq.mpr hc).eq
  rw [Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion, Nat.cast_one, one_smul, hgy,
    Chow.pointCycleClassOrZero, dif_pos hy]

/-- The fundamental class of a complex variety `C`, carried along an isomorphism `e` onto an
integral closed subscheme and pushed into `Y` along its closed immersion `i` onto the closure of
a point `y` of delta-dimension `k`, is `cl_Y(y)`. -/
private theorem pushforward_pushforward_fundamentalClass_eq_pointCycleClass {Cv Sv Yv : Scheme.{0}}
    [Cv.Over (Spec (.of ℂ))] [Sv.Over (Spec (.of ℂ))] [Yv.Over (Spec (.of ℂ))]
    [IsComplexScheme Cv] [IsComplexScheme Yv] [LocallyOfFiniteType (Sv ↘ Spec (.of ℂ))]
    [IsIntegral Cv] (e : Cv ⟶ Sv) [IsIso e]
    [e.IsOver (Spec (.of ℂ))] (i : Sv ⟶ Yv) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))]
    {k : ℕ} (hk : (k : WithBot ℕ∞) = dimension Cv)
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Cv)) (2 * k : ℕ)}
    (hμ : IsVarietyFundamentalClass ℚ hk μ) (y : Yv)
    (hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Yv ↘ Spec (.of ℂ)) y = k)
    (hry : Set.range i.base = closure {y}) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) i))
        (isProperMap_map (K := ℂ) i) (2 * k : ℕ)).hom
        ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) e))
          (isProperMap_map (K := ℂ) e) (2 * k : ℕ)).hom μ) =
      Chow.pointCycleClass ℚ y hy := by
  rw [borelMooreHomology.pushforward_comp_apply ℚ _ _ (isProperMap_map (K := ℂ) e)
      (isProperMap_map (K := ℂ) i)
      ((isProperMap_map (K := ℂ) i).comp (isProperMap_map (K := ℂ) e)),
    ← borelMooreHomology.pushforward_apply_congr ℚ (topCatOfHom_map_comp e i)
      (isProperMap_map (K := ℂ) (e ≫ i))]
  exact pushforward_fundamentalClass_eq_pointCycleClass (e ≫ i) hk hμ y hy
    (by rw [range_comp_of_isIso, hry])

/-- A set matched by the slice `Φ_t` to a set of complex points of a double surface `S` lies in
`S` too. -/
theorem IsExceptionalTrivialization.pointsOver_subset_carrier [NoetherianSpace Z]
    {T : IrreducibleCloseds Y} {U : Y.Opens} {b : UnderlyingSpace ℂ Y}
    {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) (σ : DoubleSurface F) (t : Δ)
    {A B : Set Z}
    (hB : pointsOver (K := ℂ) B ⊆
      pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {(t : UnderlyingSpace ℂ Y)})
    (hAB : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) A ↔
        (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) B)
    (hA : pointsOver (K := ℂ) A ⊆ pointsOver (K := ℂ) σ.carrier) :
    pointsOver (K := ℂ) B ⊆ pointsOver (K := ℂ) σ.carrier := by
  intro x hx
  set q := Φ.symm ⟨x, (hB hx).1, by
    change mapFun r x ∈ Δ
    rw [(hB hx).2]
    exact t.2⟩ with hq
  have hq2 : q.2 = t :=
    Subtype.ext ((snd_symm_apply_of_mapFun_eq Φ hΦ.mapFun_eq _).trans (hB hx).2)
  have hΦq : (Φ (q.1, t) : UnderlyingSpace ℂ Z) = x := by
    rw [← hq2, Prod.mk.eta, hq, Φ.apply_symm_apply]
  rw [← hΦq]
  exact (mem_pointsOver_carrier_iff_of_homeomorph hΦ.isPreconnected hbΔ Φ hΦ.apply_base
    hΦ.mem_iff σ _).2 (hA ((hAB q.1).2 (hΦq ▸ hx)))

/-- A complex point of the base curve of a double-surface family over an open `O` is the complex
point of a parameter point in `baseOpens hO`. -/
theorem DoubleSurfaceFamily.exists_parameterPoint {T : IrreducibleCloseds Y}
    {σ : DoubleSurface F} {U : Y.Opens} (𝔉 : DoubleSurfaceFamily r F T σ U)
    {O : Set (UnderlyingSpace ℂ Y)} (hO : IsOpen O) {s : UnderlyingSpace ℂ Y}
    (hs : s ∈ Set.range (mapFun (K := ℂ) 𝔉.jB)) (hsO : s ∈ O) :
    ∃ u : ParameterPoint 𝔉.B, u.complexPoint ∈ 𝔉.baseOpens hO ∧
      mapFun (K := ℂ) 𝔉.jB u.complexPoint = s := by
  obtain ⟨w, rfl⟩ := hs
  refine ⟨ParameterPoint.ofIsClosed (w.toHom (IsLocalRing.closedPoint ℂ))
    (equivClosedPoints (K := ℂ) 𝔉.B w).2
    (isRegularLocalRing_stalk_of_smooth_over_field (𝔉.B ↘ Spec (.of ℂ)) _), ?_⟩
  have hw : (ParameterPoint.ofIsClosed (w.toHom (IsLocalRing.closedPoint ℂ))
      (equivClosedPoints (K := ℂ) 𝔉.B w).2
      (isRegularLocalRing_stalk_of_smooth_over_field (𝔉.B ↘ Spec (.of ℂ)) _)).complexPoint = w :=
    UnderlyingSpace.eq_iff_toHom_closedPoint_eq.2
      ((ParameterPoint.complexPoint_toHom_closedPoint _).trans
        (ParameterPoint.point_ofIsClosed _ _ _))
  rw [hw]
  exact ⟨hsO, rfl⟩

/-- A curve `c : C ⟶ Z` matched with a fibre component `closure {y}` of a double-surface family
by `g` has its complex points read in `Z` through the fibre. -/
theorem DoubleSurfaceFamily.mapFun_jV_fibreι_map {T : IrreducibleCloseds Y}
    {σ : DoubleSurface F} {U : Y.Opens} (𝔉 : DoubleSurfaceFamily r F T σ U)
    (s : ParameterPoint 𝔉.B) {C : Scheme.{0}} [C.Over (Spec (.of ℂ))] (c : C ⟶ Z)
    [c.IsOver (Spec (.of ℂ))] (y : ParameterPoint.fibre 𝔉.f s)
    (g : C ⟶ (Stacks.Chow.integralComponentAt y).subscheme) [g.IsOver (Spec (.of ℂ))]
    (hg : g ≫ (Stacks.Chow.integralComponentAt y).subschemeι ≫ ParameterPoint.fibreι 𝔉.f s ≫
      𝔉.jV = c) (x : UnderlyingSpace ℂ C) :
    mapFun (K := ℂ) 𝔉.jV (mapFun (K := ℂ) (ParameterPoint.fibreι 𝔉.f s)
      (map (K := ℂ) (g ≫ (Stacks.Chow.integralComponentAt y).subschemeι) x)) =
        mapFun (K := ℂ) c x := by
  apply UnderlyingSpace.ext
  change ((x.toHom ≫ g ≫ (Stacks.Chow.integralComponentAt y).subschemeι) ≫
    ParameterPoint.fibreι 𝔉.f s) ≫ 𝔉.jV = x.toHom ≫ c
  rw [← hg]
  simp only [Category.assoc]

/-- **Transport of curve classes along a double-surface family.** Given the algebraic family of
a double surface `S` over `U`, the homeomorphism `C_b(ℂ) ≃ₜ C_t(ℂ)` induced by an exceptional
trivialization carries the fundamental class of a curve `C_b ⊆ S_b` to that of `C_t`
(`MMP.Fourfold.pushforward_fibrePointsTransportHom_pointCycleClass_eq_of_range_eq`). -/
theorem DoubleSurfaceFamily.homologyEquivOfHomeomorph_curveTransportHomeomorph
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {T : IrreducibleCloseds Y} {σ : DoubleSurface F}
    {U : Y.Opens} (𝔉 : DoubleSurfaceFamily r F T σ U)
    (b : UnderlyingSpace ℂ Y) (Δ : Set (UnderlyingSpace ℂ Y)) (hbΔ : b ∈ Δ)
    (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) (t : Δ)
    (Cb Ct : Scheme.{0}) [Cb.Over (Spec (.of ℂ))] [Ct.Over (Spec (.of ℂ))]
    [IsIntegral Cb] [IsIntegral Ct] [IsComplexScheme Cb] [IsComplexScheme Ct]
    (jb : Cb ⟶ Z) (jt : Ct ⟶ Z) [IsClosedImmersion jb] [IsClosedImmersion jt]
    [jb.IsOver (Spec (.of ℂ))] [jt.IsOver (Spec (.of ℂ))]
    (hb1 : ((1 : ℕ) : WithBot ℕ∞) = dimension Cb)
    (ht1 : ((1 : ℕ) : WithBot ℕ∞) = dimension Ct)
    (hbσ : Set.range jb ⊆ σ.carrier)
    (hb : pointsOver (K := ℂ) (Set.range jb) ⊆
      pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b})
    (ht : pointsOver (K := ℂ) (Set.range jt) ⊆
      pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {(t : UnderlyingSpace ℂ Y)})
    (hbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (Set.range jb) ↔
        (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (Set.range jt))
    (μb : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Cb))
      (2 * 1 : ℕ))
    (μt : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Ct))
      (2 * 1 : ℕ))
    (hμb : IsVarietyFundamentalClass ℚ hb1 μb) (hμt : IsVarietyFundamentalClass ℚ ht1 μt) :
    homologyEquivOfHomeomorph (curveTransportHomeomorph Φ hΦ.mapFun_eq t jb jt hb ht hbt)
      ((2 * 1 : ℕ) : ℤ) μb = μt := by
  classical
  haveI : TopologicalSpace.NoetherianSpace Z := noetherianSpace_of_isComplexScheme
  obtain ⟨O, hO, hΔO⟩ := hΦ.isOpen
  set W := 𝔉.baseOpens hO with hWdef
  set ψ := 𝔉.prodHomeomorph hΦ hO hΔO with hψdef
  have hψ := 𝔉.mapFun_f_prodHomeomorph hΦ hO hΔO
  haveI : ConnectedSpace W := 𝔉.connectedSpace_baseOpens hΦ hO hΔO
  have hpp : ∀ s ∈ Δ, ∃ u : ParameterPoint 𝔉.B, u.complexPoint ∈ W ∧
      mapFun (K := ℂ) 𝔉.jB u.complexPoint = s := fun s hs ↦
    𝔉.exists_parameterPoint hO (𝔉.mem_range_jB_of_mem hΦ hΔO hs) (hΔO ▸ hs).1
  obtain ⟨sb, hsbW, hsb⟩ := hpp b hbΔ
  obtain ⟨st, hstW, hst⟩ := hpp t t.2
  have hbS : pointsOver (K := ℂ) (Set.range jb) ⊆ pointsOver (K := ℂ) σ.carrier :=
    pointsOver_mono hbσ
  have htS := hΦ.pointsOver_subset_carrier σ t ht hbt hbS
  obtain ⟨yb, hybg, hyb1, gb, hgbi, hgbo, hgb⟩ := 𝔉.exists_component sb Cb jb hb1 hbS
    (fun x hx ↦ by rw [hsb]; exact (hb hx).2)
  obtain ⟨yt, hytg, hyt1, gt, hgti, hgto, hgt⟩ := 𝔉.exists_component st Ct jt ht1 htS
    (fun x hx ↦ by rw [hst]; exact (ht hx).2)
  haveI := hgbi
  haveI := hgbo
  haveI := hgti
  haveI := hgto
  haveI := 𝔉.isReduced_fibre sb
  haveI := 𝔉.isReduced_fibre st
  have hmapb := 𝔉.mapFun_jV_fibreι_map sb jb yb gb hgb
  have hmapt := 𝔉.mapFun_jV_fibreι_map st jt yt gt hgt
  set hb' := gb ≫ (Stacks.Chow.integralComponentAt yb).subschemeι with hhb'
  set ht' := gt ≫ (Stacks.Chow.integralComponentAt yt).subschemeι with hht'
  have hrangeb : Set.range hb'.base = closure {yb} := by
    rw [hhb', range_comp_of_isIso, Scheme.IdealSheafData.range_subschemeι,
      Stacks.Chow.coe_support_integralComponentAt]
  have hranget : Set.range ht'.base = closure {yt} := by
    rw [hht', range_comp_of_isIso, Scheme.IdealSheafData.range_subschemeι,
      Stacks.Chow.coe_support_integralComponentAt]
  set κb := TopCat.ofHom (map (K := ℂ) hb') ≫ fibrePointsTransportHom ψ hψ sb hsbW with hκb
  set κt := TopCat.ofHom (map (K := ℂ) ht') ≫ fibrePointsTransportHom ψ hψ st hstW with hκt
  have hκ : ∀ (u : ParameterPoint 𝔉.B) (hu : u.complexPoint ∈ W)
      (v₀ : UnderlyingSpace ℂ (ParameterPoint.fibre 𝔉.f u)),
      ∃ h, mapFun (K := ℂ) 𝔉.jV (mapFun (K := ℂ) (ParameterPoint.fibreι 𝔉.f u) v₀) =
        Φ ((fibrePointsTransportHom ψ hψ u hu v₀).1,
          ⟨mapFun (K := ℂ) 𝔉.jB u.complexPoint, h⟩) :=
    𝔉.exists_mapFun_jV_fibreι hΦ hO hΔO
  set cT := curveTransportHomeomorph Φ hΦ.mapFun_eq t jb jt hb ht hbt with hcT
  have hcomp : TopCat.ofHom (cT : C(UnderlyingSpace ℂ Cb, UnderlyingSpace ℂ Ct)) ≫ κt = κb := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    obtain ⟨h1, e1⟩ := hκ sb hsbW (map (K := ℂ) hb' x)
    obtain ⟨h2, e2⟩ := hκ st hstW (map (K := ℂ) ht' (cT x))
    rw [hmapb] at e1
    rw [hmapt, map_curveTransportHomeomorph_apply Φ hΦ.mapFun_eq t jb jt hb ht hbt x] at e2
    have hδb : (⟨mapFun (K := ℂ) 𝔉.jB sb.complexPoint, h1⟩ : Δ) = ⟨b, hbΔ⟩ := Subtype.ext hsb
    have hδt : (⟨mapFun (K := ℂ) 𝔉.jB st.complexPoint, h2⟩ : Δ) = t := Subtype.ext hst
    rw [hδb, hΦ.apply_base] at e1
    rw [hδt] at e2
    refine Subtype.ext (Subtype.ext ?_)
    change (((fibrePointsTransportHom ψ hψ st hstW (map (K := ℂ) ht' (cT x))).1 : _) :
        UnderlyingSpace ℂ Z) =
      ((fibrePointsTransportHom ψ hψ sb hsbW (map (K := ℂ) hb' x)).1 : _)
    rw [← e1]
    exact (congrArg (fun q ↦ ((q.1 : _) : UnderlyingSpace ℂ Z))
      (Φ.injective (Subtype.ext e2))).symm
  have hrb : Set.range κb = Set.range (componentTransportHom ψ hψ sb hsbW yb) := by
    rw [range_componentTransportHom]
    change Set.range ((fibrePointsTransportHom ψ hψ sb hsbW) ∘ (map (K := ℂ) hb')) = _
    rw [Set.range_comp, range_map_of_isClosedImmersion, hrangeb]
  have hrt : Set.range κt = Set.range (componentTransportHom ψ hψ st hstW yt) := by
    rw [range_componentTransportHom]
    change Set.range ((fibrePointsTransportHom ψ hψ st hstW) ∘ (map (K := ℂ) ht')) = _
    rw [Set.range_comp, range_map_of_isClosedImmersion, hranget]
  have hrbt : Set.range κb = Set.range κt := by
    rw [← hcomp]
    change Set.range (κt ∘ cT) = _
    exact cT.surjective.range_comp _
  have hCC' : Set.range (componentTransportHom ψ hψ sb hsbW yb) =
      Set.range (componentTransportHom ψ hψ st hstW yt) := by
    rw [← hrb, ← hrt, hrbt]
  haveI : TopologicalSpace.MetrizableSpace (TopCat.of
      {x : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) //
        (x : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier}) := by
    haveI : TopologicalSpace.MetrizableSpace (UnderlyingSpace ℂ Z) :=
      UnderlyingSpace.metrizableSpace_of_isComplexScheme Z
    exact (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).metrizableSpace
  have hB := pushforward_fibrePointsTransportHom_pointCycleClass_eq_of_range_eq (R := ℚ) 𝔉.dim_B
    (n := 1) 𝔉.dimension_V ψ hψ sb st hsbW hstW (𝔉.disjoint_fibre sb) (𝔉.disjoint_fibre st)
    hybg hyb1 hytg hyt1 hCC'
  rw [← pushforward_fundamentalClass_eq_pointCycleClass hb' hb1 hμb yb hyb1 hrangeb,
    ← pushforward_fundamentalClass_eq_pointCycleClass ht' ht1 hμt yt hyt1 hranget] at hB
  have hκb_emb : Topology.IsClosedEmbedding κb :=
    (isClosedEmbedding_fibrePointsTransportHom ψ hψ sb hsbW).comp
      (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) hb')
  have hκt_emb : Topology.IsClosedEmbedding κt :=
    (isClosedEmbedding_fibrePointsTransportHom ψ hψ st hstW).comp
      (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) ht')
  have hκt_open : IsOpen (Set.range κt) := by
    rw [hrt]
    exact isOpen_range_componentTransportHom ψ hψ st hstW (𝔉.disjoint_fibre st) hytg
  apply pushforward_injective_of_isOpen_range (R := ℚ) κt hκt_emb hκt_open
  rw [homologyEquivOfHomeomorph_apply, borelMooreHomology.pushforward_comp_apply ℚ _ _ _ _
      (by rw [hcomp]; exact hκb_emb.isProperMap),
    borelMooreHomology.pushforward_apply_congr ℚ hcomp _ hκb_emb.isProperMap]
  rwa [borelMooreHomology.pushforward_comp_apply ℚ (TopCat.ofHom (map (K := ℂ) hb')) _
      (isProperMap_map (K := ℂ) hb') _ hκb_emb.isProperMap,
    borelMooreHomology.pushforward_comp_apply ℚ (TopCat.ofHom (map (K := ℂ) ht')) _
      (isProperMap_map (K := ℂ) ht') _ hκt_emb.isProperMap] at hB

/-- **Transport of the fundamental classes of the curves of a double surface.** Let `S` be a
double surface of `F`. Over a general open `U` of `T`, for every exceptional trivialization `Φ`
over `Δ ∋ b`, `t ∈ Δ`, and closed curves `j_b : C_b ⟶ Z`, `j_t : C_t ⟶ Z` lying in the fibres
over `b` and `t`, with `C_b ⊆ S`, whose complex points `Φ_t` matches, the homeomorphism
`C_b(ℂ) ≃ₜ C_t(ℂ)` induced by `Φ_t` carries the fundamental class of `C_b` to that of `C_t`. The
curve `C_b` lies in a double surface `S`; the cycle classes of the fibres `S_s` of `S → T°` are
constant along the trivialization (`MMP.Fourfold.pushforward_fibreTransportHom_cycleClass_eq`),
the general fibres are smooth, so reduced, with disjoint components, and `C_b`, `C_t` are matched
components. -/
theorem exists_open_pushforward_curveTransportHomeomorph_of_doubleSurface
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) (σ : DoubleSurface F) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ (b : UnderlyingSpace ℂ Y) (Δ : Set (UnderlyingSpace ℂ Y)) (hbΔ : b ∈ Δ)
        (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
          ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
        (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) (t : Δ)
        (Cb Ct : Scheme.{0}) [Cb.Over (Spec (.of ℂ))] [Ct.Over (Spec (.of ℂ))]
          [IsIntegral Cb] [IsIntegral Ct] [IsComplexScheme Cb] [IsComplexScheme Ct]
          (jb : Cb ⟶ Z) (jt : Ct ⟶ Z) [IsClosedImmersion jb] [IsClosedImmersion jt]
          [jb.IsOver (Spec (.of ℂ))] [jt.IsOver (Spec (.of ℂ))]
          (hb1 : ((1 : ℕ) : WithBot ℕ∞) = dimension Cb)
          (ht1 : ((1 : ℕ) : WithBot ℕ∞) = dimension Ct)
          (hbσ : Set.range jb ⊆ σ.carrier)
          (hb : pointsOver (K := ℂ) (Set.range jb) ⊆
            pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b})
          (ht : pointsOver (K := ℂ) (Set.range jt) ⊆
            pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {(t : UnderlyingSpace ℂ Y)})
          (hbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
            (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (Set.range jb) ↔
              (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (Set.range jt))
          (μb : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Cb))
            (2 * 1 : ℕ))
          (μt : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Ct))
            (2 * 1 : ℕ)),
          IsVarietyFundamentalClass ℚ hb1 μb → IsVarietyFundamentalClass ℚ ht1 μt →
          homologyEquivOfHomeomorph (curveTransportHomeomorph Φ hΦ.mapFun_eq t jb jt hb ht hbt)
            ((2 * 1 : ℕ) : ℤ) μb = μt := by
  haveI : IsProper r :=
    (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  by_cases hTS : (T : Set Y) ⊆ r.base '' σ.carrier
  · obtain ⟨U, hU, ⟨𝔉⟩⟩ := exists_doubleSurfaceFamily hM T hT1 σ hTS
    exact ⟨U, hU, fun b Δ hbΔ Φ hΦ t Cb Ct _ _ _ _ _ _ jb jt _ _ _ _ hb1 ht1 hbσ hb ht hbt μb μt
      hμb hμt ↦ 𝔉.homologyEquivOfHomeomorph_curveTransportHomeomorph b Δ hbΔ Φ hΦ t Cb Ct jb jt
        hb1 ht1 hbσ hb ht hbt μb μt hμb hμt⟩
  -- `T ⊄ r(S)`: off the closed set `r(S)`, the fibres of `S` are empty.
  have hσc : IsClosed σ.carrier := by
    obtain ⟨x, hxS, hx⟩ := σ.isComponent
    have hS : IsClosed ((σ.fst.support : Set Z) ∩ σ.snd.support) :=
      σ.fst.idealSheaf.support.isClosed.inter σ.snd.idealSheaf.support.isClosed
    rw [← hx]
    refine closure_subset_iff_isClosed.1 ?_
    exact (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hxS))
      (closure_minimal (connectedComponentIn_subset _ x) hS)
  have hcl : IsClosed (r.base '' σ.carrier) := r.isClosedMap _ hσc
  refine ⟨⟨(r.base '' σ.carrier)ᶜ, hcl.isOpen_compl⟩, ?_, ?_⟩
  · obtain ⟨y, hyT, hyS⟩ := Set.not_subset.1 hTS
    exact ⟨y, hyS, hyT⟩
  intro b Δ hbΔ Φ hΦ t Cb Ct _ _ _ _ _ _ jb jt _ _ _ _ hb1 ht1 hbσ hb ht hbt μb μt hμb hμt
  exfalso
  haveI : CompactSpace Cb := QuasiCompact.compactSpace_of_compactSpace (Cb ↘ Spec (.of ℂ))
  obtain ⟨c, -, hc⟩ := (isClosed_univ (X := Cb)).exists_closed_singleton Set.univ_nonempty
  set x := (equivClosedPoints (K := ℂ) Cb).symm ⟨c, hc⟩
  have hx : mapFun jb x ∈ pointsOver (K := ℂ) (Set.range jb) := ⟨_, rfl⟩
  have hxb : mapFun r (mapFun jb x) = b := (hb hx).2
  apply hΦ.subset hbΔ
  refine ⟨jb.base (x.toHom.base (IsLocalRing.closedPoint ℂ)), hbσ ⟨_, rfl⟩, ?_⟩
  rw [← hxb]
  rfl

/-- **Transport of the fundamental classes of double curves.** Over a general open `U` of `T`,
for every exceptional trivialization `Φ` over `Δ ∋ b`, `t ∈ Δ`, and closed curves
`j_b : C_b ⟶ Z`, `j_t : C_t ⟶ Z` lying in the intersection `E ∩ E'` of two distinct components
of `F` and in the fibres over `b` and `t`, whose complex points `Φ_t` matches, the homeomorphism
`C_b(ℂ) ≃ₜ C_t(ℂ)` induced by `Φ_t` carries the fundamental class of `C_b` to that of `C_t`. The
curve `C_b` lies in a double surface `S`; the cycle classes of the fibres `S_s` of `S → T°` are
constant along the trivialization (`MMP.Fourfold.pushforward_fibreTransportHom_cycleClass_eq`),
the general fibres are smooth, so reduced, with disjoint components, and `C_b`, `C_t` are matched
components. -/
theorem exists_open_pushforward_curveTransportHomeomorph
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ (b : UnderlyingSpace ℂ Y) (Δ : Set (UnderlyingSpace ℂ Y)) (hbΔ : b ∈ Δ)
        (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
          ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
        (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) (t : Δ) (E E' : F.support), E ≠ E' →
        ∀ (Cb Ct : Scheme.{0}) [Cb.Over (Spec (.of ℂ))] [Ct.Over (Spec (.of ℂ))]
          [IsIntegral Cb] [IsIntegral Ct] [IsComplexScheme Cb] [IsComplexScheme Ct]
          (jb : Cb ⟶ Z) (jt : Ct ⟶ Z) [IsClosedImmersion jb] [IsClosedImmersion jt]
          [jb.IsOver (Spec (.of ℂ))] [jt.IsOver (Spec (.of ℂ))]
          (hb1 : ((1 : ℕ) : WithBot ℕ∞) = dimension Cb)
          (ht1 : ((1 : ℕ) : WithBot ℕ∞) = dimension Ct)
          (hbE : Set.range jb ⊆ (E.1.support : Set Z) ∩ E'.1.support)
          (hb : pointsOver (K := ℂ) (Set.range jb) ⊆
            pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b})
          (ht : pointsOver (K := ℂ) (Set.range jt) ⊆
            pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {(t : UnderlyingSpace ℂ Y)})
          (hbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
            (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (Set.range jb) ↔
              (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (Set.range jt))
          (μb : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Cb))
            (2 * 1 : ℕ))
          (μt : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Ct))
            (2 * 1 : ℕ)),
          IsVarietyFundamentalClass ℚ hb1 μb → IsVarietyFundamentalClass ℚ ht1 μt →
          homologyEquivOfHomeomorph (curveTransportHomeomorph Φ hΦ.mapFun_eq t jb jt hb ht hbt)
            ((2 * 1 : ℕ) : ℤ) μb = μt := by
  classical
  haveI : AlgebraicGeometry.IsNoetherian Z := AlgebraicGeometry.IsNoetherian.mk
  haveI : Finite (DoubleSurface F) := DoubleSurface.finite
  letI := Fintype.ofFinite (DoubleSurface F)
  choose Uσ hUσ hσ using fun σ : DoubleSurface F ↦
    exists_open_pushforward_curveTransportHomeomorph_of_doubleSurface hM T hTs hT1 σ
  have hne : ∀ s : Finset (DoubleSurface F), (((s.inf Uσ : Y.Opens) : Set Y) ∩ T).Nonempty := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
      exact ⟨x, by simp, hx⟩
    | insert a s _ ih =>
      rw [Finset.inf_insert]
      exact inter_inter_nonempty_of_irreducibleCloseds T (hUσ a) ih
  refine ⟨Finset.univ.inf Uσ, hne _, fun b Δ hbΔ Φ hΦ t E E' hEE' Cb Ct _ _ _ _ _ _ jb jt _ _ _ _
    hb1 ht1 hbE hb ht hbt μb μt hμb hμt ↦ ?_⟩
  have hirr : IsIrreducible (Set.range jb) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ jb.base.hom.continuous.continuousOn
  have hne' : (Set.range jb).Nonempty := hirr.nonempty
  exact hσ (DoubleSurface.through E.2 E'.2 (fun h ↦ hEE' (Subtype.ext h)) hne' hbE) b Δ hbΔ Φ
    (hΦ.mono (Finset.inf_le (Finset.mem_univ _))) t Cb Ct jb jt hb1 ht1
    (DoubleSurface.subset_through _ _ _ hne' hbE
      (_root_.IsIrreducible.isConnected hirr).isPreconnected)
    hb ht hbt μb μt hμb hμt

/-- The closed subscheme `closure {x}` of a subvariety `G` of `E` lies over `G`. -/
private theorem range_subschemeι_integralComponentAt_subset {E : Mori.PrimeDivisor Z}
    (G : Subvariety E.idealSheaf.subscheme) (x : G.toScheme) :
    Set.range ((Stacks.Chow.integralComponentAt x).subschemeι ≫ G.ι ≫
        E.idealSheaf.subschemeι).base ⊆ E.idealSheaf.subschemeι.base '' (G.support : Set _) := by
  rw [range_subschemeι_integralComponentAt_comp, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.image_comp]
  refine Set.image_mono ?_
  rintro _ ⟨y, -, rfl⟩
  rw [Subvariety.support_eq, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨y, rfl⟩

/-- A point of a subvariety `G` of `E` is determined by the image of its closure in `Z`. -/
private theorem eq_of_range_subschemeι_integralComponentAt_eq {E : Mori.PrimeDivisor Z}
    {G : Subvariety E.idealSheaf.subscheme} {x₁ x₂ : G.toScheme}
    (h : Set.range ((Stacks.Chow.integralComponentAt x₁).subschemeι ≫ G.ι ≫
        E.idealSheaf.subschemeι).base =
      Set.range ((Stacks.Chow.integralComponentAt x₂).subschemeι ≫ G.ι ≫
        E.idealSheaf.subschemeι).base) : x₁ = x₂ := by
  rw [range_subschemeι_integralComponentAt_comp, range_subschemeι_integralComponentAt_comp] at h
  exact (inseparable_iff_closure_eq.mpr ((Set.image_injective.2
    (G.ι ≫ E.idealSheaf.subschemeι).isClosedEmbedding.injective) h)).eq

/-- The complex points of a curve `closure {x}` in a fibre component `G` of `E` over `y` lie in
the fibre of `F` over `y`. -/
theorem pointsOver_range_integralComponentAt_subset_fibre
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {E : Mori.PrimeDivisor Z} (hE : E ∈ F.support)
    {y : UnderlyingSpace ℂ Y} {G : Subvariety E.idealSheaf.subscheme}
    (hG : (G.support : Set _) ⊆
      (E.idealSheaf.subschemeι ≫ r).base ⁻¹' {y.toHom (IsLocalRing.closedPoint ℂ)})
    (x : G.toScheme) :
    pointsOver (K := ℂ) (Set.range ((Stacks.Chow.integralComponentAt x).subschemeι ≫
      G.ι ≫ E.idealSheaf.subschemeι)) ⊆
      pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y} := by
  rw [range_subschemeι_integralComponentAt_comp, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.image_comp]
  refine pointsOver_image_subset_fibre hE (subset_trans ?_ hG)
  rintro _ ⟨z, -, rfl⟩
  rw [Subvariety.support_eq, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨z, rfl⟩

/-- **(i) Transport of the double curves.** Over a general open `U` of `T`, for every exceptional
trivialization `Φ` over `Δ ∋ b`, `t ∈ Δ` and fibre components `G_b`, `G_t` matched by `Φ_t`, the
isomorphism `H_2(G_b) ≅ H_2(G_t)` induced by `Φ_t` sends the class of every curve `C_b ⊆ G_b`
lying in another component `E'` of `F` to the class of the curve `C_t = Φ_t(C_b)`: by Fulton's
Lemma 19.1.3 the classes `cl(C_s)` are the specializations `f^*u_s ∩ cl(S)` of the double
surface `S ⊇ C_s` over `T°`, constant in `s` along the trivialization (Lemma 19.2(c)). -/
theorem fibreComponentTransport_doubleCurve
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ (b : UnderlyingSpace ℂ Y) (Δ : Set (UnderlyingSpace ℂ Y)) (hbΔ : b ∈ Δ)
        (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
          ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
        (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ)
        (t : Δ) (E : F.support) (Gb Gt : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2})
        (hGb : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
          {b.toHom (IsLocalRing.closedPoint ℂ)}) (Gb.1.support : Set _))
        (hGt : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
          {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) (Gt.1.support : Set _))
        (hGbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
          (z : UnderlyingSpace ℂ Z) ∈
            pointsOver (E.1.idealSheaf.subschemeι.base '' (Gb.1.support : Set _)) ↔
          (Φ (z, t) : UnderlyingSpace ℂ Z) ∈
            pointsOver (E.1.idealSheaf.subschemeι.base '' (Gt.1.support : Set _)))
        (E' : F.support), E' ≠ E →
        ∀ (Cb : {x : Gb.1.toScheme // Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (Gb.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (Ct : {x : Gt.1.toScheme // Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (Gt.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)}),
          (Gb.1.ι ≫ E.1.idealSheaf.subschemeι).base '' closure {Cb.1} ⊆
            (E'.1.support : Set Z) →
          (∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
            (z : UnderlyingSpace ℂ Z) ∈ pointsOver
              ((Gb.1.ι ≫ E.1.idealSheaf.subschemeι).base '' closure {Cb.1}) ↔
            (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver
              ((Gt.1.ι ≫ E.1.idealSheaf.subschemeι).base '' closure {Ct.1})) →
          fibreComponentTransport hΦ t E.2 hGb.1.2 hGt.1.2 hGbt (2 * 1)
              (Chow.pointCycleClass ℚ Cb.1 Cb.2) =
            Chow.pointCycleClass ℚ Ct.1 Ct.2 := by
  obtain ⟨U, hU, hC⟩ := exists_open_pushforward_curveTransportHomeomorph hM T hTs hT1
  refine ⟨U, hU, fun b Δ hbΔ Φ hΦ t E Gb Gt hGb hGt hGbt E' hE' Cb Ct hCb hCbt ↦ ?_⟩
  have hrange : ∀ {G : Subvariety E.1.idealSheaf.subscheme} (x : G.toScheme),
      Set.range ((Stacks.Chow.integralComponentAt x).subschemeι ≫ G.ι ≫
          E.1.idealSheaf.subschemeι) =
        (G.ι ≫ E.1.idealSheaf.subschemeι).base '' closure {x} := fun x ↦
    range_subschemeι_integralComponentAt_comp x _
  have hE_sub : ∀ {G : Subvariety E.1.idealSheaf.subscheme} (x : G.toScheme),
      Set.range ((Stacks.Chow.integralComponentAt x).subschemeι ≫ G.ι ≫
        E.1.idealSheaf.subschemeι) ⊆ (E.1.support : Set Z) :=
    fun {G} x ↦ by
    rintro _ ⟨y, rfl⟩
    have : E.1.idealSheaf.subschemeι.base
        (((Stacks.Chow.integralComponentAt x).subschemeι ≫ G.ι).base y) ∈
        (E.1.idealSheaf.support : Set Z) :=
      E.1.idealSheaf.range_subschemeι ▸ ⟨_, rfl⟩
    exact this
  have hb := pointsOver_range_integralComponentAt_subset_fibre E.2 hGb.1.2 Cb.1
  have ht := pointsOver_range_integralComponentAt_subset_fibre E.2 hGt.1.2 Ct.1
  have hbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ)
        (Set.range ((Stacks.Chow.integralComponentAt Cb.1).subschemeι ≫ Gb.1.ι ≫
          E.1.idealSheaf.subschemeι)) ↔
      (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ)
        (Set.range ((Stacks.Chow.integralComponentAt Ct.1).subschemeι ≫ Gt.1.ι ≫
          E.1.idealSheaf.subschemeι)) := by
    rw [hrange, hrange]
    exact hCbt
  obtain ⟨cb, hcb, hcbα⟩ := Chow.isCycleClassOf_pointCycleClass ℚ Cb.1 Cb.2
  obtain ⟨ct, hct, hctα⟩ := Chow.isCycleClassOf_pointCycleClass ℚ Ct.1 Ct.2
  have key := hC b Δ hbΔ Φ hΦ t E E' hE'.symm (Stacks.Chow.integralComponentAt Cb.1).subscheme
    (Stacks.Chow.integralComponentAt Ct.1).subscheme
    ((Stacks.Chow.integralComponentAt Cb.1).subschemeι ≫ Gb.1.ι ≫ E.1.idealSheaf.subschemeι)
    ((Stacks.Chow.integralComponentAt Ct.1).subschemeι ≫ Gt.1.ι ≫ E.1.idealSheaf.subschemeι)
    _ _ (Set.subset_inter (hE_sub Cb.1) ((hrange Cb.1).trans_subset hCb)) hb ht hbt cb ct hcb hct
  rw [← hcbα, ← hctα, ← key]
  simp only [fibreComponentTransport, homologyEquivOfHomeomorph_apply]
  rw [borelMooreHomology.pushforward_comp_apply ℚ _ _ _ _ (by
      exact (Homeomorph.isProperMap _).comp
        (isProperMap_map (K := ℂ) (Stacks.Chow.integralComponentAt Cb.1).subschemeι)),
    borelMooreHomology.pushforward_comp_apply ℚ _ _ _ _ (by
      exact (isProperMap_map (K := ℂ) (Stacks.Chow.integralComponentAt Ct.1).subschemeι).comp
        (Homeomorph.isProperMap _))]
  refine borelMooreHomology.pushforward_apply_congr ℚ ?_ _ _ _ _
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  apply (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
    (Gt.1.ι ≫ E.1.idealSheaf.subschemeι)).injective
  have h1 := map_curveTransportHomeomorph_apply Φ hΦ.mapFun_eq t _ _ hb ht hbt x
  have h2 : ∀ {G : Subvariety E.1.idealSheaf.subscheme} {c : G.toScheme}
      (y : UnderlyingSpace ℂ (Stacks.Chow.integralComponentAt c).subscheme),
      mapFun ((Stacks.Chow.integralComponentAt c).subschemeι ≫ G.ι ≫
          E.1.idealSheaf.subschemeι) y =
        map (K := ℂ) (G.ι ≫ E.1.idealSheaf.subschemeι)
          (map (K := ℂ) (Stacks.Chow.integralComponentAt c).subschemeι y) := fun y ↦
    UnderlyingSpace.ext (Category.assoc _ _ _).symm
  rw [h2] at h1
  refine Eq.trans ?_ h1.symm
  refine (congrArg Subtype.val ((homeomorphPointsOverRange
    (Gt.1.ι ≫ E.1.idealSheaf.subschemeι)).apply_symm_apply _)).trans ?_
  exact congrArg (fun w ↦ (Φ (w, t) : UnderlyingSpace ℂ Z)) (Subtype.ext (h2 x).symm)

/-! ### Transport of the curves cut by a prime divisor of `E` -/

section primeDivisorCurves

open MMP.borelMooreHomology

section primeDivisorFamilyProduct

variable {T : IrreducibleCloseds Y} {E : Mori.PrimeDivisor Z}
  {P : Mori.PrimeDivisor E.idealSheaf.subscheme} {U : Y.Opens}

/-- The point of `F_Δ` given by `x ∈ E_b` and `w ∈ B(ℂ)` over `Δ` lies in `G(ℂ)`. -/
theorem PrimeDivisorFamily.mem_range_jG (𝔉 : PrimeDivisorFamily r T E P U)
    (hE : E ∈ F.support) {U'' : Y.Opens} (hU'' : U'' ≤ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U'' hbΔ Φ)
    (x : fibrePointsIn F r (E.support : Set Z) b) (δ : Δ) :
    (Φ (⟨x.1, x.2.2⟩, δ) : UnderlyingSpace ℂ Z) ∈ Set.range (mapFun (K := ℂ) 𝔉.jG) := by
  rw [𝔉.range_jG]
  refine ⟨(hΦ.mem_iff E hE _).2 x.2.1, ?_⟩
  change mapFun r (Φ (⟨x.1, x.2.2⟩, δ) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (U : Set Y)
  rw [hΦ.mapFun_eq]
  exact pointsOver_mono hU'' (hΦ.subset δ.2)

/-- **The product structure of the family of fibres of `E`**, from an exceptional
trivialization: `E_b × W ≃ₜ g⁻¹(W)`, `(x, w) ↦ Φ(x, w)` read in `G(ℂ)`. -/
noncomputable def PrimeDivisorFamily.prodHomeomorph (𝔉 : PrimeDivisorFamily r T E P U)
    (hE : E ∈ F.support) {U'' : Y.Opens} (hU'' : U'' ≤ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U'' hbΔ Φ) {O : Set (UnderlyingSpace ℂ Y)}
    (hO : IsOpen O) (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y)) :
    (TopCat.of (fibrePointsIn F r (E.support : Set Z) b)) × 𝔉.baseOpens hO ≃ₜ
      preimageOpens (TopCat.ofHom (map (K := ℂ) 𝔉.g)) (𝔉.baseOpens hO) :=
  let eG := 𝔉.isEmbedding_jG.toHomeomorph
  have hG : ∀ y, mapFun (K := ℂ) 𝔉.jG (eG.symm y) = y.1 := fun y ↦
    congrArg Subtype.val (eG.apply_symm_apply y)
  have hWΔ : ∀ w, w ∈ 𝔉.baseOpens hO ↔ mapFun (K := ℂ) 𝔉.jB w ∈ Δ := fun w ↦ by
    rw [hΔO]
    exact 𝔉.mem_baseOpens_iff hO w
  have hz : ∀ v : preimageOpens (TopCat.ofHom (map (K := ℂ) 𝔉.g)) (𝔉.baseOpens hO),
      mapFun (K := ℂ) 𝔉.jG v.1 ∈ pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ ∧
      mapFun (K := ℂ) 𝔉.jG v.1 ∈ pointsOver (K := ℂ) (E.support : Set Z) := fun v ↦ by
    have h1 : mapFun (K := ℂ) 𝔉.jG v.1 ∈ Set.range (mapFun (K := ℂ) 𝔉.jG) := ⟨v.1, rfl⟩
    rw [𝔉.range_jG] at h1
    refine ⟨⟨?_, ?_⟩, h1.1⟩
    · change (mapFun (K := ℂ) 𝔉.jG v.1).toHom _ ∈ (F.supp : Set Z)
      rw [DivisorWithCoeffs.coe_supp]
      exact Set.mem_iUnion₂.2 ⟨E, hE, h1.1⟩
    · change mapFun r (mapFun (K := ℂ) 𝔉.jG v.1) ∈ Δ
      rw [𝔉.mapFun_r_jG]
      exact (hWΔ _).1 v.2
  { toFun := fun p ↦ ⟨eG.symm ⟨_, 𝔉.mem_range_jG hE hU'' hΦ p.1 ⟨_, (hWΔ _).1 p.2.2⟩⟩, by
      change mapFun (K := ℂ) 𝔉.g _ ∈ 𝔉.baseOpens hO
      rw [hWΔ, ← 𝔉.mapFun_r_jG]
      have h := congrArg Subtype.val (eG.apply_symm_apply
        ⟨_, 𝔉.mem_range_jG hE hU'' hΦ p.1 ⟨_, (hWΔ _).1 p.2.2⟩⟩)
      change mapFun (K := ℂ) 𝔉.jG _ = _ at h
      rw [h, hΦ.mapFun_eq]
      exact (hWΔ _).1 p.2.2⟩
    invFun := fun v ↦ (⟨(Φ.symm ⟨_, (hz v).1⟩).1, by
        have h := (hΦ.mem_iff E hE (Φ.symm ⟨_, (hz v).1⟩)).1
        rw [Φ.apply_symm_apply] at h
        exact ⟨h (hz v).2, (Φ.symm ⟨_, (hz v).1⟩).1.2⟩⟩, ⟨mapFun (K := ℂ) 𝔉.g v.1, v.2⟩)
    left_inv := by
      rintro ⟨x, w⟩
      have hv := hG ⟨_, 𝔉.mem_range_jG hE hU'' hΦ x ⟨_, (hWΔ _).1 w.2⟩⟩
      have key : ∀ q : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ),
          (q : UnderlyingSpace ℂ Z) = Φ (⟨x.1, x.2.2⟩, ⟨_, (hWΔ _).1 w.2⟩) →
          (Φ.symm q).1 = ⟨x.1, x.2.2⟩ := fun q hq ↦ by
        rw [show q = Φ (⟨x.1, x.2.2⟩, ⟨_, (hWΔ _).1 w.2⟩) from Subtype.ext hq, Φ.symm_apply_apply]
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact congrArg (fun q : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) ↦
          (q : UnderlyingSpace ℂ Z)) (key _ hv)
      apply 𝔉.isEmbedding_jB.injective
      change mapFun (K := ℂ) 𝔉.jB (mapFun (K := ℂ) 𝔉.g _) = _
      rw [← 𝔉.mapFun_r_jG, hv, hΦ.mapFun_eq]
    right_inv := by
      intro v
      apply Subtype.ext
      apply 𝔉.isEmbedding_jG.injective
      refine (hG _).trans ?_
      have key : ∀ (q : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ)
          (δ : Δ), (δ : UnderlyingSpace ℂ Y) = mapFun r (Φ q : UnderlyingSpace ℂ Z) →
          (Φ (q.1, δ) : UnderlyingSpace ℂ Z) = Φ q := fun q δ h ↦ by
        rw [show (q.1, δ) = q from Prod.ext rfl (Subtype.ext (h.trans (hΦ.mapFun_eq q)))]
      refine (key _ _ ?_).trans ?_
      · rw [Φ.apply_symm_apply]
        exact (𝔉.mapFun_r_jG v.1).symm
      · rw [Φ.apply_symm_apply]
    continuous_toFun := by
      refine Continuous.subtype_mk (eG.symm.continuous.comp (Continuous.subtype_mk
        (continuous_subtype_val.comp (Φ.continuous.comp ?_)) _)) _
      exact (Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) _).prodMk
        (Continuous.subtype_mk
          ((continuous_mapFun _).comp (continuous_subtype_val.comp continuous_snd)) _)
    continuous_invFun := by
      refine Continuous.prodMk (Continuous.subtype_mk (continuous_subtype_val.comp
        (continuous_fst.comp (Φ.symm.continuous.comp (Continuous.subtype_mk
          ((continuous_mapFun _).comp continuous_subtype_val) _)))) _)
        (Continuous.subtype_mk ((continuous_mapFun _).comp continuous_subtype_val) _) }

/-- The image under `jG` of `prodHomeomorph hE hU'' hΦ hO hΔO p` is `Φ (p.1, jB p.2)`. -/
theorem PrimeDivisorFamily.exists_mapFun_jG_prodHomeomorph (𝔉 : PrimeDivisorFamily r T E P U)
    (hE : E ∈ F.support) {U'' : Y.Opens} (hU'' : U'' ≤ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U'' hbΔ Φ) {O : Set (UnderlyingSpace ℂ Y)}
    (hO : IsOpen O) (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y))
    (p : (TopCat.of (fibrePointsIn F r (E.support : Set Z) b)) × 𝔉.baseOpens hO) :
    ∃ h : mapFun (K := ℂ) 𝔉.jB p.2 ∈ Δ,
      mapFun (K := ℂ) 𝔉.jG (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO p : UnderlyingSpace ℂ 𝔉.G) =
        Φ (⟨p.1.1, p.1.2.2⟩, ⟨_, h⟩) :=
  ⟨_, congrArg Subtype.val (𝔉.isEmbedding_jG.toHomeomorph.apply_symm_apply _)⟩

/-- The image under `g` of `prodHomeomorph hE hU'' hΦ hO hΔO p` is `p.2`. -/
theorem PrimeDivisorFamily.mapFun_g_prodHomeomorph (𝔉 : PrimeDivisorFamily r T E P U)
    (hE : E ∈ F.support) {U'' : Y.Opens} (hU'' : U'' ≤ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U'' hbΔ Φ) {O : Set (UnderlyingSpace ℂ Y)}
    (hO : IsOpen O) (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y))
    (p : (TopCat.of (fibrePointsIn F r (E.support : Set Z) b)) × 𝔉.baseOpens hO) :
    map (K := ℂ) 𝔉.g (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO p : UnderlyingSpace ℂ 𝔉.G) =
      (p.2 : UnderlyingSpace ℂ 𝔉.B) := by
  obtain ⟨h, hp⟩ := 𝔉.exists_mapFun_jG_prodHomeomorph hE hU'' hΦ hO hΔO p
  apply 𝔉.isEmbedding_jB.injective
  change mapFun (K := ℂ) 𝔉.jB (mapFun (K := ℂ) 𝔉.g _) = _
  rw [← 𝔉.mapFun_r_jG, hp, hΦ.mapFun_eq]

end primeDivisorFamilyProduct

section fibreTransport

variable {T : IrreducibleCloseds Y} {U : Y.Opens} {b : UnderlyingSpace ℂ Y}
  {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
  {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
    ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}

/-- The slice `Φ_s` restricted to the points of a component `E` of `F`: `E_b(ℂ) ≃ₜ E_s(ℂ)`. -/
noncomputable def IsExceptionalTrivialization.componentHomeomorph
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {E : Mori.PrimeDivisor Z}
    (hE : E ∈ F.support) (s : Δ) :
    fibrePointsIn F r (E.support : Set Z) b ≃ₜ fibrePointsIn F r (E.support : Set Z) s :=
  transportHomeomorph Φ hΦ.mapFun_eq s Set.inter_subset_right Set.inter_subset_right
    (fun z ↦ ⟨fun h ↦ ⟨(hΦ.mem_iff E hE (z, s)).2 h.1, (Φ (z, s)).2.1, hΦ.mapFun_eq (z, s)⟩,
      fun h ↦ ⟨(hΦ.mem_iff E hE (z, s)).1 h.1, z.2⟩⟩)

/-- On a point `x` of `E_b(ℂ)`, `componentHomeomorph hE s` is `Φ (x, s)`. -/
theorem IsExceptionalTrivialization.coe_componentHomeomorph_apply
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {E : Mori.PrimeDivisor Z}
    (hE : E ∈ F.support) (s : Δ) (x : fibrePointsIn F r (E.support : Set Z) b) :
    (hΦ.componentHomeomorph hE s x : UnderlyingSpace ℂ Z) = Φ (⟨x.1, x.2.2⟩, s) :=
  rfl

/-- At the base point `b`, `componentHomeomorph hE` is the identity of `E_b(ℂ)`. -/
theorem IsExceptionalTrivialization.coe_componentHomeomorph_base
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {E : Mori.PrimeDivisor Z}
    (hE : E ∈ F.support) (x : fibrePointsIn F r (E.support : Set Z) b) :
    (hΦ.componentHomeomorph hE ⟨b, hbΔ⟩ x : UnderlyingSpace ℂ Z) = x :=
  hΦ.apply_base _

/-- The complex points of a closed subvariety `G` of `E` lying over `s` lie in `E_s(ℂ)`. -/
theorem mapFun_mem_fibrePointsIn [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    {E : Mori.PrimeDivisor Z} (hE : E ∈ F.support) {s : UnderlyingSpace ℂ Y}
    (G : Subvariety E.idealSheaf.subscheme)
    (hG : (G.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {s.toHom (IsLocalRing.closedPoint ℂ)}) (q : UnderlyingSpace ℂ G.toScheme) :
    mapFun (K := ℂ) (G.ι ≫ E.idealSheaf.subschemeι) q ∈
      fibrePointsIn F r (E.support : Set Z) s := by
  have hq : mapFun (K := ℂ) (G.ι ≫ E.idealSheaf.subschemeι) q ∈
      pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' (G.support : Set _)) := by
    rw [← range_ι_comp_subschemeι]
    exact ⟨_, by rw [toHom_mapFun]; rfl⟩
  refine ⟨pointsOver_mono ?_ hq, pointsOver_image_subset_fibre hE hG hq⟩
  rintro _ ⟨x, -, rfl⟩
  change _ ∈ (E.idealSheaf.support : Set Z)
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨x, rfl⟩

/-- The complex points of a closed subvariety `G` of `E` lying over `s`, as points of `E_s(ℂ)`. -/
noncomputable def subvarietyFibrePointsHom [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    {E : Mori.PrimeDivisor Z} (hE : E ∈ F.support) {s : UnderlyingSpace ℂ Y}
    (G : Subvariety E.idealSheaf.subscheme)
    (hG : (G.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {s.toHom (IsLocalRing.closedPoint ℂ)}) :
    C(UnderlyingSpace ℂ G.toScheme, fibrePointsIn F r (E.support : Set Z) s) :=
  ⟨fun q ↦ ⟨_, mapFun_mem_fibrePointsIn hE G hG q⟩, (continuous_mapFun _).subtype_mk _⟩

/-- `subvarietyFibrePointsHom hE G hG` is a closed embedding. -/
theorem isClosedEmbedding_subvarietyFibrePointsHom [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    {E : Mori.PrimeDivisor Z} (hE : E ∈ F.support) {s : UnderlyingSpace ℂ Y}
    (G : Subvariety E.idealSheaf.subscheme)
    (hG : (G.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {s.toHom (IsLocalRing.closedPoint ℂ)}) :
    Topology.IsClosedEmbedding (subvarietyFibrePointsHom (F := F) hE G hG) :=
  Topology.IsClosedEmbedding.of_comp (f := subvarietyFibrePointsHom (F := F) hE G hG)
    Topology.IsEmbedding.subtypeVal
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (G.ι ≫ E.idealSheaf.subschemeι))

/-- The complex points of a closed subvariety `G` of `E` over `s ∈ Δ`, carried to `E_b(ℂ)` by
the inverse of the slice `Φ_s`. -/
noncomputable def IsExceptionalTrivialization.componentPointsHom
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {E : Mori.PrimeDivisor Z}
    (hE : E ∈ F.support) (s : Δ) (G : Subvariety E.idealSheaf.subscheme)
    (hG : (G.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) :
    TopCat.of (UnderlyingSpace ℂ G.toScheme) ⟶
      TopCat.of (fibrePointsIn F r (E.support : Set Z) b) :=
  TopCat.ofHom (((hΦ.componentHomeomorph hE s).symm : C(_, _)).comp
    (subvarietyFibrePointsHom hE G hG))

/-- `componentPointsHom hE s G hG` is a closed embedding. -/
theorem IsExceptionalTrivialization.isClosedEmbedding_componentPointsHom
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {E : Mori.PrimeDivisor Z}
    (hE : E ∈ F.support) (s : Δ) (G : Subvariety E.idealSheaf.subscheme)
    (hG : (G.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) :
    Topology.IsClosedEmbedding (hΦ.componentPointsHom hE s G hG) :=
  (hΦ.componentHomeomorph hE s).symm.isClosedEmbedding.comp
    (isClosedEmbedding_subvarietyFibrePointsHom hE G hG)

/-- Composing `componentPointsHom hE s G hG` with `componentHomeomorph hE s` gives the inclusion
of `G(ℂ)` in `Z(ℂ)`. -/
theorem IsExceptionalTrivialization.componentHomeomorph_componentPointsHom
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {E : Mori.PrimeDivisor Z}
    (hE : E ∈ F.support) (s : Δ) (G : Subvariety E.idealSheaf.subscheme)
    (hG : (G.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
    (q : UnderlyingSpace ℂ G.toScheme) :
    (hΦ.componentHomeomorph hE s (hΦ.componentPointsHom hE s G hG q) : UnderlyingSpace ℂ Z) =
      mapFun (K := ℂ) (G.ι ≫ E.idealSheaf.subschemeι) q := by
  change ((hΦ.componentHomeomorph hE s ((hΦ.componentHomeomorph hE s).symm _)) :
    UnderlyingSpace ℂ Z) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

/-- The homeomorphism `G_b(ℂ) ≃ₜ G_t(ℂ)` behind `MMP.Fourfold.fibreComponentTransport`: the
slice `Φ_t` read on complex points. -/
theorem IsExceptionalTrivialization.exists_fibreComponentTransport_eq
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) (t : Δ) {E : Mori.PrimeDivisor Z}
    (hE : E ∈ F.support) {Gb Gt : Subvariety E.idealSheaf.subscheme}
    (hGb : (Gb.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {b.toHom (IsLocalRing.closedPoint ℂ)})
    (hGt : (Gt.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
    (hGbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈
        pointsOver (E.idealSheaf.subschemeι.base '' (Gb.support : Set _)) ↔
      (Φ (z, t) : UnderlyingSpace ℂ Z) ∈
        pointsOver (E.idealSheaf.subschemeι.base '' (Gt.support : Set _))) :
    ∃ e : UnderlyingSpace ℂ Gb.toScheme ≃ₜ UnderlyingSpace ℂ Gt.toScheme,
      (∀ q, mapFun (K := ℂ) (Gt.ι ≫ E.idealSheaf.subschemeι) (e q) =
        (Φ (⟨_, (mapFun_mem_fibrePointsIn hE Gb hGb q).2⟩, t) : UnderlyingSpace ℂ Z)) ∧
      ∀ n : ℕ, fibreComponentTransport hΦ t hE hGb hGt hGbt n = homologyEquivOfHomeomorph e n := by
  refine ⟨((homeomorphPointsOverRange (Gb.ι ≫ E.idealSheaf.subschemeι)).trans
      (Homeomorph.setCongr (by rw [range_ι_comp_subschemeι]))).trans
    ((transportHomeomorph Φ hΦ.mapFun_eq t (pointsOver_image_subset_fibre hE hGb)
      (pointsOver_image_subset_fibre hE hGt) hGbt).trans
      ((Homeomorph.setCongr (by rw [range_ι_comp_subschemeι])).trans
        (homeomorphPointsOverRange (Gt.ι ≫ E.idealSheaf.subschemeι)).symm)), fun q ↦ ?_,
    fun n ↦ rfl⟩
  exact congrArg Subtype.val ((homeomorphPointsOverRange
    (Gt.ι ≫ E.idealSheaf.subschemeι)).apply_symm_apply _)

/-- The range of `componentPointsHom hE s G hG` is the set of points of `E_b(ℂ)` that
`componentHomeomorph hE s` sends into `G(ℂ)`. -/
theorem IsExceptionalTrivialization.range_componentPointsHom
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) {E : Mori.PrimeDivisor Z}
    (hE : E ∈ F.support) (s : Δ) (G : Subvariety E.idealSheaf.subscheme)
    (hG : (G.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) :
    Set.range (hΦ.componentPointsHom hE s G hG) =
      {x | (hΦ.componentHomeomorph hE s x : UnderlyingSpace ℂ Z) ∈
        pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' (G.support : Set _))} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    rw [Set.mem_setOf_eq, hΦ.componentHomeomorph_componentPointsHom, ← range_ι_comp_subschemeι,
      ← range_map_of_isClosedImmersion]
    exact ⟨q, rfl⟩
  · intro hx
    rw [Set.mem_setOf_eq, ← range_ι_comp_subschemeι, ← range_map_of_isClosedImmersion] at hx
    obtain ⟨q, hq⟩ := hx
    refine ⟨q, (hΦ.componentHomeomorph hE s).injective (Subtype.ext ?_)⟩
    rw [hΦ.componentHomeomorph_componentPointsHom]
    exact hq

/-- If `Φ_t` matches `G_b(ℂ)` with `G_t(ℂ)`, the range of `componentPointsHom hE t G_t hG_t` is
`G_b(ℂ)` read in `E_b(ℂ)`. -/
theorem IsExceptionalTrivialization.range_componentPointsHom_eq_of_iff
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) (t : Δ) {E : Mori.PrimeDivisor Z}
    (hE : E ∈ F.support) {Gb Gt : Subvariety E.idealSheaf.subscheme}
    (hGt : (Gt.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
    (hGbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈
        pointsOver (E.idealSheaf.subschemeι.base '' (Gb.support : Set _)) ↔
      (Φ (z, t) : UnderlyingSpace ℂ Z) ∈
        pointsOver (E.idealSheaf.subschemeι.base '' (Gt.support : Set _))) :
    Set.range (hΦ.componentPointsHom hE t Gt hGt) =
      {x : fibrePointsIn F r (E.support : Set Z) b | (x : UnderlyingSpace ℂ Z) ∈
        pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' (Gb.support : Set _))} := by
  rw [hΦ.range_componentPointsHom]
  ext x
  exact (hGbt ⟨x.1, x.2.2⟩).symm

/-- A homeomorphism `e : G_b(ℂ) ≃ₜ G_t(ℂ)` induced by `Φ_t` intertwines the maps
`componentPointsHom` of `G_b` and `G_t` into `E_b(ℂ)`. -/
theorem IsExceptionalTrivialization.ofHom_comp_componentPointsHom
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ) (t : Δ) {E : Mori.PrimeDivisor Z}
    (hE : E ∈ F.support) {Gb Gt : Subvariety E.idealSheaf.subscheme}
    (hGb : (Gb.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {b.toHom (IsLocalRing.closedPoint ℂ)})
    (hGt : (Gt.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
    (e : UnderlyingSpace ℂ Gb.toScheme ≃ₜ UnderlyingSpace ℂ Gt.toScheme)
    (he : ∀ q, mapFun (K := ℂ) (Gt.ι ≫ E.idealSheaf.subschemeι) (e q) =
      (Φ (⟨_, (mapFun_mem_fibrePointsIn hE Gb hGb q).2⟩, t) : UnderlyingSpace ℂ Z)) :
    TopCat.ofHom (e : C(_, _)) ≫ hΦ.componentPointsHom hE t Gt hGt =
      hΦ.componentPointsHom hE ⟨b, hbΔ⟩ Gb hGb := by
  refine ConcreteCategory.hom_ext _ _ fun q ↦ ?_
  apply (hΦ.componentHomeomorph hE t).injective
  apply Subtype.ext
  change (hΦ.componentHomeomorph hE t (hΦ.componentPointsHom hE t Gt hGt (e q)) :
    UnderlyingSpace ℂ Z) = (hΦ.componentHomeomorph hE t
      (hΦ.componentPointsHom hE ⟨b, hbΔ⟩ Gb hGb q) : UnderlyingSpace ℂ Z)
  rw [hΦ.componentHomeomorph_componentPointsHom, he,
    IsExceptionalTrivialization.coe_componentHomeomorph_apply]
  have hb' := hΦ.componentHomeomorph_componentPointsHom hE ⟨b, hbΔ⟩ Gb hGb q
  rw [hΦ.coe_componentHomeomorph_base] at hb'
  exact congrArg (fun w ↦ (Φ (w, t) : UnderlyingSpace ℂ Z)) (Subtype.ext hb'.symm)

end fibreTransport

section ambientComponent

variable {T : Scheme.{0}} [T.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))]
  {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsComplexScheme V]
  {G : Scheme.{0}} [G.Over (Spec (.of ℂ))] [IsComplexScheme G]

/-- The complex points of the closure of a point `y` of the fibre `V_t` of `f = ι ≫ g`, read in
`X` through `ι` and a product structure `ψ : X × W ≃ₜ g⁻¹(W)` of the ambient family. -/
noncomputable def ambientComponentTransportHom (ι : V ⟶ G) [ι.IsOver (Spec (.of ℂ))]
    (g : G ⟶ T) [g.IsOver (Spec (.of ℂ))] {f : V ⟶ T} [f.IsOver (Spec (.of ℂ))]
    (hf : ι ≫ g = f) {X : TopCat.{0}} {W : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T))}
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) g)) W)
    (hψ : ∀ p, map (K := ℂ) g (ψ p : UnderlyingSpace ℂ G) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) (y : ParameterPoint.fibre f t) :
    TopCat.of (UnderlyingSpace ℂ (Stacks.Chow.integralComponentAt y).subscheme) ⟶ X :=
  TopCat.ofHom (map (K := ℂ) (Stacks.Chow.integralComponentAt y).subschemeι) ≫
    fibreAmbientPointsHom ι g hf t ≫ fibreTransportHom ψ hψ ht

/-- `ambientComponentTransportHom ι g hf ψ hψ t ht y` is a proper map. -/
theorem isProperMap_ambientComponentTransportHom (ι : V ⟶ G) [ι.IsOver (Spec (.of ℂ))]
    [IsProper ι] (g : G ⟶ T) [g.IsOver (Spec (.of ℂ))] {f : V ⟶ T} [f.IsOver (Spec (.of ℂ))]
    (hf : ι ≫ g = f) {X : TopCat.{0}} {W : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T))}
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) g)) W)
    (hψ : ∀ p, map (K := ℂ) g (ψ p : UnderlyingSpace ℂ G) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) (y : ParameterPoint.fibre f t) :
    IsProperMap (ambientComponentTransportHom ι g hf ψ hψ t ht y) :=
  ((isProperMap_fibreTransportHom ψ hψ ht).comp
    (isProperMap_fibreAmbientPointsHom ι g hf t)).comp
    (isProperMap_map (K := ℂ) (Stacks.Chow.integralComponentAt y).subschemeι)

/-- The class of a point of `V_t`, read in `X` through the ambient product structure, is the
push-forward of a fundamental class of its closure along `ambientComponentTransportHom`. -/
theorem exists_pushforward_pointCycleClass_eq_ambientComponentTransportHom (ι : V ⟶ G)
    [ι.IsOver (Spec (.of ℂ))] [IsProper ι] (g : G ⟶ T) [g.IsOver (Spec (.of ℂ))] {f : V ⟶ T}
    [f.IsOver (Spec (.of ℂ))] (hf : ι ≫ g = f) {X : TopCat.{0}}
    {W : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T))}
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) g)) W)
    (hψ : ∀ p, map (K := ℂ) g (ψ p : UnderlyingSpace ℂ G) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) {n : ℕ} (y : ParameterPoint.fibre f t)
    (hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) y = n) :
    ∃ c, (pushforward ℚ (ModuleCat.of ℚ ℚ)
        (fibreAmbientPointsHom ι g hf t ≫ fibreTransportHom ψ hψ ht)
        ((isProperMap_fibreTransportHom ψ hψ ht).comp
          (isProperMap_fibreAmbientPointsHom ι g hf t)) (2 * n : ℕ)).hom
        (Chow.pointCycleClass ℚ y hy) =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (ambientComponentTransportHom ι g hf ψ hψ t ht y)
        (isProperMap_ambientComponentTransportHom ι g hf ψ hψ t ht y) (2 * n : ℕ)).hom c :=
  ⟨_, (pushforward_comp_apply' ℚ _ _ _ _ _ _).symm⟩

end ambientComponent

section assembly

variable {T : IrreducibleCloseds Y} {E : Mori.PrimeDivisor Z}
  {P : Mori.PrimeDivisor E.idealSheaf.subscheme} {U : Y.Opens}

/-- The complex points of the closure of a point of a fibre `V_u`, read in `E_b(ℂ)` through the
ambient product structure and carried back to `E_u(ℂ)` by the slice of `Φ`, are their points in
`Z(ℂ)`. -/
theorem PrimeDivisorFamily.coe_componentHomeomorph_ambientComponentTransportHom
    (𝔉 : PrimeDivisorFamily r T E P U)
    (hE : E ∈ F.support) {U'' : Y.Opens} (hU'' : U'' ≤ U)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U'' hbΔ Φ) {O : Set (UnderlyingSpace ℂ Y)}
    (hO : IsOpen O) (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y))
    (u : ParameterPoint 𝔉.B) (hu : u.complexPoint ∈ 𝔉.baseOpens hO)
    (y : ParameterPoint.fibre 𝔉.f u)
    (q : UnderlyingSpace ℂ (Stacks.Chow.integralComponentAt y).subscheme) :
    ∃ h : mapFun (K := ℂ) 𝔉.jB u.complexPoint ∈ Δ,
      (hΦ.componentHomeomorph hE ⟨_, h⟩ (ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
        (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
        u hu y q) : UnderlyingSpace ℂ Z) =
      mapFun (K := ℂ) ((Stacks.Chow.integralComponentAt y).subschemeι ≫
        ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG) q := by
  set ψ := 𝔉.prodHomeomorph hE hU'' hΦ hO hΔO with hψdef
  have hψ := 𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO
  set v := fibreAmbientPointsHom 𝔉.ι 𝔉.g 𝔉.hf u
    (map (K := ℂ) (Stacks.Chow.integralComponentAt y).subschemeι q) with hv
  have hv' : (ψ ((fibreHomeomorphOfProd ψ hψ hu) v, ⟨_, hu⟩) : UnderlyingSpace ℂ 𝔉.G) = v.1 :=
    congrArg Subtype.val ((fibreHomeomorphOfProd ψ hψ hu).symm_apply_apply v)
  obtain ⟨h, hp⟩ := 𝔉.exists_mapFun_jG_prodHomeomorph hE hU'' hΦ hO hΔO
    ((fibreHomeomorphOfProd ψ hψ hu) v, ⟨_, hu⟩)
  refine ⟨h, ?_⟩
  rw [hv'] at hp
  have hq : ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf ψ hψ u hu y q =
      (fibreHomeomorphOfProd ψ hψ hu) v := rfl
  rw [IsExceptionalTrivialization.coe_componentHomeomorph_apply, hq]
  refine (hp.symm.trans ?_)
  apply UnderlyingSpace.ext
  change ((q.toHom ≫ (Stacks.Chow.integralComponentAt y).subschemeι) ≫
    ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι) ≫ 𝔉.jG = _
  rw [toHom_mapFun]
  simp only [Category.assoc]

section perFibre

variable [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (𝔉 : PrimeDivisorFamily r T E P U)
  (hE : E ∈ F.support) {U'' : Y.Opens} (hU'' : U'' ≤ U)
  {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
  {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
    ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
  (hΦ : IsExceptionalTrivialization r F T U'' hbΔ Φ) {O : Set (UnderlyingSpace ℂ Y)}
  (hO : IsOpen O) (hΔO : Δ = O ∩ pointsOver (K := ℂ) (T : Set Y))

/-- The ambient map of the closure of a point of the fibre `V_u` over `s = j_B(u)`, read in
`E_s(ℂ)`. -/
theorem PrimeDivisorFamily.coe_componentHomeomorph_amb (s : Δ)
    (u : ParameterPoint 𝔉.B) (hu : u.complexPoint ∈ 𝔉.baseOpens hO)
    (hus : mapFun (K := ℂ) 𝔉.jB u.complexPoint = s)
    (y : ParameterPoint.fibre 𝔉.f u)
    (q : UnderlyingSpace ℂ (Stacks.Chow.integralComponentAt y).subscheme) :
    (hΦ.componentHomeomorph hE s (ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
        (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
        u hu y q) : UnderlyingSpace ℂ Z) =
      mapFun (K := ℂ) ((Stacks.Chow.integralComponentAt y).subschemeι ≫
        ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG) q := by
  obtain ⟨s, hsΔ⟩ := s
  subst hus
  obtain ⟨h, e⟩ := 𝔉.coe_componentHomeomorph_ambientComponentTransportHom hE hU'' hΦ hO hΔO
    u hu y q
  exact e

/-- The point of `Y` underlying the complex point `jB u` is the image of `u.point` under `jB`. -/
theorem PrimeDivisorFamily.toHom_mapFun_jB (u : ParameterPoint 𝔉.B) :
    (mapFun (K := ℂ) 𝔉.jB u.complexPoint).toHom (IsLocalRing.closedPoint ℂ) =
      𝔉.jB.base u.point := by
  rw [toHom_mapFun]
  change 𝔉.jB.base (u.complexPoint.toHom.base (IsLocalRing.closedPoint ℂ)) = _
  rw [← ParameterPoint.complexPoint_toHom_closedPoint u]

/-- **The ambient image of the closure of a point of the fibre lands in the piece `Ω` or misses
it.** -/
theorem PrimeDivisorFamily.range_amb_subset_or_disjoint
    (Ω : TopologicalSpace.Opens (TopCat.of (fibrePointsIn F r (E.support : Set Z) b)))
    (s : Δ) (Gs : Subvariety E.idealSheaf.subscheme)
    (u : ParameterPoint 𝔉.B) (hu : u.complexPoint ∈ 𝔉.baseOpens hO)
    (hus : mapFun (K := ℂ) 𝔉.jB u.complexPoint = s)
    (hGs : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {𝔉.jB.base u.point}) (Gs.support : Set _))
    (hdisj : ∀ (A B : Set E.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {𝔉.jB.base u.point}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {𝔉.jB.base u.point}) B → A ≠ B → Disjoint A B)
    (hΩs : ∀ x, x ∈ Ω ↔ (hΦ.componentHomeomorph hE s x : UnderlyingSpace ℂ Z) ∈
      pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' (Gs.support : Set _)))
    (y : ParameterPoint.fibre 𝔉.f u) :
    (Set.range ((Stacks.Chow.integralComponentAt y).subschemeι ≫ ParameterPoint.fibreι 𝔉.f u ≫
        𝔉.ι ≫ 𝔉.jG).base ⊆ E.idealSheaf.subschemeι.base '' (Gs.support : Set _) ∧
      Set.range (ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
        (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
        u hu y) ⊆ Ω) ∨
    (Disjoint (Set.range ((Stacks.Chow.integralComponentAt y).subschemeι ≫
          ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base)
        (E.idealSheaf.subschemeι.base '' (Gs.support : Set _)) ∧
      Disjoint (Set.range (ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
        (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
        u hu y)) Ω) := by
  have hmemΩ : ∀ q, ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
        (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
        u hu y q ∈ Ω ↔
      mapFun (K := ℂ) ((Stacks.Chow.integralComponentAt y).subschemeι ≫
          ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG) q ∈
        pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' (Gs.support : Set _)) :=
    fun q ↦ by rw [hΩs, 𝔉.coe_componentHomeomorph_amb hE hU'' hΦ hO hΔO s u hu hus]
  rcases 𝔉.range_subset_or_disjoint u Gs hGs hdisj y with h | h
  · refine Or.inl ⟨h, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact (hmemΩ q).2 (pointsOver_mono h (mapFun_mem_pointsOver_range _ q))
  · refine Or.inr ⟨h, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨q, rfl⟩ hq
    exact Set.disjoint_left.1 h (mapFun_mem_pointsOver_range _ q) ((hmemΩ q).1 hq)

/-- The points of a curve cut on `G_s` by `P`, read in `E_b(ℂ)` directly or through the
matching component of the fibre `V_u`. -/
theorem PrimeDivisorFamily.map_comp_componentPointsHom_eq
    (s : Δ) (Gs : Subvariety E.idealSheaf.subscheme)
    (hGs : (Gs.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
    (u : ParameterPoint 𝔉.B) (hu : u.complexPoint ∈ 𝔉.baseOpens hO)
    (hus : mapFun (K := ℂ) 𝔉.jB u.complexPoint = s)
    {C : Scheme.{0}} [C.Over (Spec (.of ℂ))] (c : C ⟶ Gs.toScheme) [c.IsOver (Spec (.of ℂ))]
    (y : ParameterPoint.fibre 𝔉.f u)
    (ge : C ⟶ (Stacks.Chow.integralComponentAt y).subscheme) [ge.IsOver (Spec (.of ℂ))]
    (hge : ge ≫ (Stacks.Chow.integralComponentAt y).subschemeι ≫ ParameterPoint.fibreι 𝔉.f u ≫
      𝔉.ι ≫ 𝔉.jG = c ≫ Gs.ι ≫ E.idealSheaf.subschemeι) :
    TopCat.ofHom (map (K := ℂ) c) ≫ hΦ.componentPointsHom hE s Gs hGs =
      TopCat.ofHom (map (K := ℂ) ge) ≫ ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
        (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
        u hu y := by
  refine ConcreteCategory.hom_ext _ _ fun q ↦ ?_
  apply (hΦ.componentHomeomorph hE s).injective
  apply Subtype.ext
  change (hΦ.componentHomeomorph hE s (hΦ.componentPointsHom hE s Gs hGs
      (map (K := ℂ) c q)) : UnderlyingSpace ℂ Z) =
    (hΦ.componentHomeomorph hE s (ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
      (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
      u hu y (map (K := ℂ) ge q)) : UnderlyingSpace ℂ Z)
  rw [𝔉.coe_componentHomeomorph_amb hE hU'' hΦ hO hΔO s u hu hus,
    IsExceptionalTrivialization.componentHomeomorph_componentPointsHom]
  apply UnderlyingSpace.ext
  rw [toHom_mapFun, toHom_mapFun]
  change ((q.toHom ≫ c) ≫ Gs.ι ≫ E.idealSheaf.subschemeι) =
    (q.toHom ≫ ge) ≫ (Stacks.Chow.integralComponentAt y).subschemeι ≫
      ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG
  rw [Category.assoc, Category.assoc, hge]

/-- **The class of a curve cut on `G_s` by `P`, read in `E_b(ℂ)`, is the class of the matching
component of the fibre `V_u`.** -/
theorem PrimeDivisorFamily.pushforward_componentPointsHom_pointCycleClass
    (s : Δ) (Gs : Subvariety E.idealSheaf.subscheme)
    (hGs : (Gs.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
    (u : ParameterPoint 𝔉.B) (hu : u.complexPoint ∈ 𝔉.baseOpens hO)
    (hus : mapFun (K := ℂ) 𝔉.jB u.complexPoint = s)
    (x : Gs.toScheme) (hx : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Gs.toScheme ↘ Spec (.of ℂ)) x =
        (1 : ℕ))
    (y : ParameterPoint.fibre 𝔉.f u) (hy : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ)) y = (1 : ℕ))
    (ge : (Stacks.Chow.integralComponentAt x).subscheme ⟶
      (Stacks.Chow.integralComponentAt y).subscheme) [IsIso ge] [ge.IsOver (Spec (.of ℂ))]
    (hge : ge ≫ (Stacks.Chow.integralComponentAt y).subschemeι ≫ ParameterPoint.fibreι 𝔉.f u ≫
      𝔉.ι ≫ 𝔉.jG =
      (Stacks.Chow.integralComponentAt x).subschemeι ≫ Gs.ι ≫ E.idealSheaf.subschemeι) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (hΦ.componentPointsHom hE s Gs hGs)
        (hΦ.isClosedEmbedding_componentPointsHom hE s Gs hGs).isProperMap
        ((2 * 1 : ℕ) : ℤ)).hom (Chow.pointCycleClass ℚ x hx) =
      (pushforward ℚ (ModuleCat.of ℚ ℚ)
        (fibreAmbientPointsHom 𝔉.ι 𝔉.g 𝔉.hf u ≫ fibreTransportHom
          (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO) hu)
        ((isProperMap_fibreTransportHom _ _ hu).comp
          (isProperMap_fibreAmbientPointsHom 𝔉.ι 𝔉.g 𝔉.hf u))
        ((2 * 1 : ℕ) : ℤ)).hom (Chow.pointCycleClass ℚ y hy) := by
  obtain ⟨μC, hμC, hμCeq⟩ := Chow.isCycleClassOf_pointCycleClass ℚ x hx
  have hry : Set.range (Stacks.Chow.integralComponentAt y).subschemeι.base = closure {y} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Stacks.Chow.coe_support_integralComponentAt]
  have hyμ := pushforward_pushforward_fundamentalClass_eq_pointCycleClass ge
    (Stacks.Chow.integralComponentAt y).subschemeι
    (Chow.natCast_eq_dimension_integralComponentAt x hx) hμC y hy hry
  rw [← hμCeq, ← hyμ]
  have hmaps := 𝔉.map_comp_componentPointsHom_eq hE hU'' hΦ hO hΔO s Gs hGs u hu hus
    (Stacks.Chow.integralComponentAt x).subschemeι y ge hge
  have hp1 := (hΦ.isClosedEmbedding_componentPointsHom hE s Gs hGs).isProperMap
  have hp2 := isProperMap_ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
    (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO) u hu y
  have hp3 : IsProperMap
      (TopCat.ofHom (map (K := ℂ) (Stacks.Chow.integralComponentAt x).subschemeι) ≫
      hΦ.componentPointsHom hE s Gs hGs) :=
    hp1.comp (isProperMap_map (K := ℂ) (Stacks.Chow.integralComponentAt x).subschemeι)
  have hp4 : IsProperMap (TopCat.ofHom (map (K := ℂ) ge) ≫
      ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
      (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
      u hu y) := hp2.comp (isProperMap_map (K := ℂ) ge)
  have e1 := borelMooreHomology.pushforward_comp_apply ℚ
    (TopCat.ofHom (map (K := ℂ) (Stacks.Chow.integralComponentAt x).subschemeι))
    (hΦ.componentPointsHom hE s Gs hGs)
    (isProperMap_map (K := ℂ) (Stacks.Chow.integralComponentAt x).subschemeι) hp1 hp3
    ((2 * 1 : ℕ) : ℤ) μC
  have e2 := borelMooreHomology.pushforward_comp_apply ℚ (TopCat.ofHom (map (K := ℂ) ge))
    (ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
      (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
      u hu y) (isProperMap_map (K := ℂ) ge) hp2 hp4 ((2 * 1 : ℕ) : ℤ) μC
  have e3 := borelMooreHomology.pushforward_apply_congr ℚ hmaps hp3 hp4 ((2 * 1 : ℕ) : ℤ) μC
  have e4 := borelMooreHomology.pushforward_comp_apply ℚ
    (TopCat.ofHom (map (K := ℂ) (Stacks.Chow.integralComponentAt y).subschemeι))
    (fibreAmbientPointsHom 𝔉.ι 𝔉.g 𝔉.hf u ≫ fibreTransportHom
      (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO) hu)
    (isProperMap_map (K := ℂ) (Stacks.Chow.integralComponentAt y).subschemeι)
    ((isProperMap_fibreTransportHom _ _ hu).comp
      (isProperMap_fibreAmbientPointsHom 𝔉.ι 𝔉.g 𝔉.hf u)) hp2 ((2 * 1 : ℕ) : ℤ)
    ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) ge))
      (isProperMap_map (K := ℂ) ge) (2 * 1 : ℕ)).hom μC)
  rw [e1, e4, e3, ← e2]
  rfl

/-- A curve cut on `G_s` by `P` is a component of the fibre `V_u`, landing in the piece `Ω`. -/
theorem PrimeDivisorFamily.exists_component_mem_piece
    (Ω : TopologicalSpace.Opens (TopCat.of (fibrePointsIn F r (E.support : Set Z) b)))
    (s : Δ) (Gs : Subvariety E.idealSheaf.subscheme)
    (hGs0 : (Gs.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
    (u : ParameterPoint 𝔉.B) (hu : u.complexPoint ∈ 𝔉.baseOpens hO)
    (hus : mapFun (K := ℂ) 𝔉.jB u.complexPoint = s)
    (hGs : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {𝔉.jB.base u.point}) (Gs.support : Set _))
    (hdisj : ∀ (A B : Set E.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {𝔉.jB.base u.point}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {𝔉.jB.base u.point}) B → A ≠ B → Disjoint A B)
    (hΩs : ∀ x, x ∈ Ω ↔ (hΦ.componentHomeomorph hE s x : UnderlyingSpace ℂ Z) ∈
      pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' (Gs.support : Set _)))
    (x : Gs.toScheme) (hx : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Gs.toScheme ↘ Spec (.of ℂ)) x =
        (1 : ℕ))
    (hC : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Gs.ι.base ⁻¹' (P.support : Set _))
      (closure {x})) :
    ∃ (y : ParameterPoint.fibre 𝔉.f u) (hy : Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ)) y = (1 : ℕ)),
      (y ∈ genericPoints (ParameterPoint.fibre 𝔉.f u) ∧
        Set.range (ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
          (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
          u hu y) ⊆ Ω) ∧
      ∃ (ge : (Stacks.Chow.integralComponentAt x).subscheme ⟶
          (Stacks.Chow.integralComponentAt y).subscheme) (_ : IsIso ge)
        (_ : ge.IsOver (Spec (.of ℂ))),
        ge ≫ (Stacks.Chow.integralComponentAt y).subschemeι ≫ ParameterPoint.fibreι 𝔉.f u ≫
          𝔉.ι ≫ 𝔉.jG =
          (Stacks.Chow.integralComponentAt x).subschemeι ≫ Gs.ι ≫ E.idealSheaf.subschemeι := by
  haveI := Stacks.Chow.isIntegral_integralComponentAt x
  obtain ⟨y, hyg, hy1, ge, hgi, hgo, hge⟩ := 𝔉.exists_component u
    (Stacks.Chow.integralComponentAt x).subscheme
    ((Stacks.Chow.integralComponentAt x).subschemeι ≫ Gs.ι ≫ E.idealSheaf.subschemeι)
    (Chow.natCast_eq_dimension_integralComponentAt x hx)
    (pointsOver_mono (by
      rw [range_subschemeι_integralComponentAt_comp x (Gs.ι ≫ E.idealSheaf.subschemeι)]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, hC.1.2 hy, rfl⟩))
    (fun q hq ↦ by
      rw [hus]
      exact (pointsOver_image_subset_fibre hE hGs0
        (pointsOver_mono (range_subschemeι_integralComponentAt_subset Gs x) hq)).2)
  have hr : Set.range ((Stacks.Chow.integralComponentAt y).subschemeι ≫
        ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base =
      Set.range ((Stacks.Chow.integralComponentAt x).subschemeι ≫ Gs.ι ≫
        E.idealSheaf.subschemeι).base := by
    rw [← hge]
    exact (range_comp_of_isIso ge _).symm
  refine ⟨y, hy1, ⟨hyg, ?_⟩, ge, hgi, hgo, hge⟩
  rcases 𝔉.range_amb_subset_or_disjoint hE hU'' hΦ hO hΔO Ω s Gs u hu hus hGs hdisj hΩs y
    with h | h
  · exact h.2
  · exfalso
    haveI : CompactSpace (Stacks.Chow.integralComponentAt x).subscheme :=
      QuasiCompact.compactSpace_of_compactSpace
        ((Stacks.Chow.integralComponentAt x).subscheme ↘ Spec (.of ℂ))
    obtain ⟨c, -, hc⟩ := (isClosed_univ
      (X := (Stacks.Chow.integralComponentAt x).subscheme)).exists_closed_singleton
      (@Set.univ_nonempty _ (Stacks.Chow.isIntegral_integralComponentAt x).nonempty)
    exact Set.disjoint_left.1 h.1 (hr ▸ ⟨c, rfl⟩)
      (range_subschemeι_integralComponentAt_subset Gs x ⟨c, rfl⟩)

/-- A component of the fibre `V_u` landing in the piece `Ω` comes from a curve cut on `G_s`
by `P`. -/
theorem PrimeDivisorFamily.exists_curve_of_mem_piece
    (Ω : TopologicalSpace.Opens (TopCat.of (fibrePointsIn F r (E.support : Set Z) b)))
    (s : Δ) (Gs : Subvariety E.idealSheaf.subscheme)
    (u : ParameterPoint 𝔉.B) (hu : u.complexPoint ∈ 𝔉.baseOpens hO)
    (hus : mapFun (K := ℂ) 𝔉.jB u.complexPoint = s)
    (hGs : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {𝔉.jB.base u.point}) (Gs.support : Set _))
    (hdisj : ∀ (A B : Set E.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {𝔉.jB.base u.point}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {𝔉.jB.base u.point}) B → A ≠ B → Disjoint A B)
    (hΩs : ∀ x, x ∈ Ω ↔ (hΦ.componentHomeomorph hE s x : UnderlyingSpace ℂ Z) ∈
      pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' (Gs.support : Set _)))
    (y : ParameterPoint.fibre 𝔉.f u) (hyg : y ∈ genericPoints (ParameterPoint.fibre 𝔉.f u))
    (hy1 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ)) y = (1 : ℕ))
    (hC'Ω : Set.range (ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
          (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
          u hu y) ⊆ Ω) :
    ∃ x : {x : Gs.toScheme // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Gs.toScheme ↘ Spec (.of ℂ)) x =
          (1 : ℕ)},
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Gs.ι.base ⁻¹' (P.support : Set _))
        (closure {x.1}) ∧
      Set.range ((Stacks.Chow.integralComponentAt x.1).subschemeι ≫ Gs.ι ≫
          E.idealSheaf.subschemeι).base =
        Set.range ((Stacks.Chow.integralComponentAt y).subschemeι ≫
          ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base := by
  have hsub : Set.range ((Stacks.Chow.integralComponentAt y).subschemeι ≫
        ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base ⊆
      E.idealSheaf.subschemeι.base '' (Gs.support : Set _) := by
    rcases 𝔉.range_amb_subset_or_disjoint hE hU'' hΦ hO hΔO Ω s Gs u hu hus hGs hdisj hΩs y
      with h | h
    · exact h.1
    · exfalso
      haveI := Stacks.Chow.isIntegral_integralComponentAt y
      haveI : CompactSpace (Stacks.Chow.integralComponentAt y).subscheme :=
        QuasiCompact.compactSpace_of_compactSpace
          ((Stacks.Chow.integralComponentAt y).subscheme ↘ Spec (.of ℂ))
      obtain ⟨c, -, hc⟩ := (isClosed_univ
        (X := (Stacks.Chow.integralComponentAt y).subscheme)).exists_closed_singleton
        (@Set.univ_nonempty _ (Stacks.Chow.isIntegral_integralComponentAt y).nonempty)
      obtain ⟨q, -⟩ := exists_toHom_eq' (X := (Stacks.Chow.integralComponentAt y).subscheme) hc
      exact Set.disjoint_left.1 h.2 ⟨q, rfl⟩ (hC'Ω ⟨q, rfl⟩)
  obtain ⟨C, hC, hCr⟩ := 𝔉.exists_subvariety_of_range_subset u Gs hGs.1.2 y hyg hy1 hsub
  refine ⟨⟨C.1.genericPoint, relativeDimension_eq_of_topologicalKrullDim_closure_eq _ _ 1 ?_⟩,
    ?_, ?_⟩
  · rw [MMP.Intersection.Scheme.Subvariety.closure_genericPoint,
      ← MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support]
    exact (MMP.Intersection.hasDim_natCast_iff 1).1 C.2
  · rw [MMP.Intersection.Scheme.Subvariety.closure_genericPoint]
    exact hC
  · rw [range_subschemeι_integralComponentAt_comp,
      MMP.Intersection.Scheme.Subvariety.closure_genericPoint, ← range_ι_comp_eq_image_support]
    exact hCr

open Classical in
/-- **Matching the curves cut on `G_s` by `P` with the components of `V_u` in `Ω`.** -/
theorem PrimeDivisorFamily.finsum_pushforward_componentPointsHom_eq
    (Ω : TopologicalSpace.Opens (TopCat.of (fibrePointsIn F r (E.support : Set Z) b)))
    (s : Δ) (Gs : Subvariety E.idealSheaf.subscheme)
    (hGs0 : (Gs.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
    (u : ParameterPoint 𝔉.B) (hu : u.complexPoint ∈ 𝔉.baseOpens hO)
    (hus : mapFun (K := ℂ) 𝔉.jB u.complexPoint = s)
    (hGs : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {𝔉.jB.base u.point}) (Gs.support : Set _))
    (hdisj : ∀ (A B : Set E.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {𝔉.jB.base u.point}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {𝔉.jB.base u.point}) B → A ≠ B → Disjoint A B)
    (hΩs : ∀ x, x ∈ Ω ↔ (hΦ.componentHomeomorph hE s x : UnderlyingSpace ℂ Z) ∈
      pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' (Gs.support : Set _))) :
    ∑ᶠ x ∈ {x : {x : Gs.toScheme // Stacks.Chow.relativeDimension
          (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Gs.toScheme ↘ Spec (.of ℂ)) x =
            (1 : ℕ)} |
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Gs.ι.base ⁻¹' (P.support : Set _))
          (closure {x.1})},
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (hΦ.componentPointsHom hE s Gs hGs0)
        (hΦ.isClosedEmbedding_componentPointsHom hE s Gs hGs0).isProperMap
        ((2 * 1 : ℕ) : ℤ)).hom (Chow.pointCycleClass ℚ x.1 x.2) =
    ∑ᶠ y ∈ {y : {y : ParameterPoint.fibre 𝔉.f u // Stacks.Chow.relativeDimension
          (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ)) y = (1 : ℕ)} |
        y.1 ∈ genericPoints (ParameterPoint.fibre 𝔉.f u)} ∩
        {y | Set.range (ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
          (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO)
          u hu y.1) ⊆ Ω},
      (pushforward ℚ (ModuleCat.of ℚ ℚ)
        (fibreAmbientPointsHom 𝔉.ι 𝔉.g 𝔉.hf u ≫ fibreTransportHom
          (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO) hu)
        ((isProperMap_fibreTransportHom _ _ hu).comp
          (isProperMap_fibreAmbientPointsHom 𝔉.ι 𝔉.g 𝔉.hf u))
        ((2 * 1 : ℕ) : ℤ)).hom (Chow.pointCycleClass ℚ y.1 y.2) := by
  choose φ hφ hφg ge hgi hgo hge using fun C : {x : {x : Gs.toScheme //
        Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Gs.toScheme ↘ Spec (.of ℂ)) x =
          (1 : ℕ)} //
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Gs.ι.base ⁻¹' (P.support : Set _))
        (closure {x.1})} ↦
    𝔉.exists_component_mem_piece hE hU'' hΦ hO hΔO Ω s Gs hGs0 u hu hus hGs hdisj hΩs C.1.1
      C.1.2 C.2
  have hr : ∀ C, Set.range ((Stacks.Chow.integralComponentAt (φ C)).subschemeι ≫
        ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base =
      Set.range ((Stacks.Chow.integralComponentAt C.1.1).subschemeι ≫ Gs.ι ≫
        E.idealSheaf.subschemeι).base := fun C ↦ by
    haveI := hgi C
    rw [← hge C]
    exact (range_comp_of_isIso (ge C) _).symm
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_subtype_eq_finsum_cond]
  refine finsum_eq_of_bijective (fun C ↦ ⟨⟨φ C, hφ C⟩, hφg C⟩)
    ⟨fun C₁ C₂ h12 ↦ ?_, fun C' ↦ ?_⟩ fun C ↦ ?_
  · have h1 : φ C₁ = φ C₂ := congrArg (fun y ↦ y.1.1) h12
    have h2 : Set.range ((Stacks.Chow.integralComponentAt C₁.1.1).subschemeι ≫ Gs.ι ≫
          E.idealSheaf.subschemeι).base =
        Set.range ((Stacks.Chow.integralComponentAt C₂.1.1).subschemeι ≫ Gs.ι ≫
          E.idealSheaf.subschemeι).base := by
      rw [← hr C₁, ← hr C₂, h1]
    exact Subtype.ext (Subtype.ext (eq_of_range_subschemeι_integralComponentAt_eq h2))
  · obtain ⟨⟨y, hy1⟩, hyg, hyΩ⟩ := C'
    obtain ⟨C, hC, hCr⟩ := 𝔉.exists_curve_of_mem_piece hE hU'' hΦ hO hΔO Ω s Gs u hu hus hGs
      hdisj hΩs y hyg hy1 hyΩ
    exact ⟨⟨C, hC⟩, Subtype.ext (Subtype.ext
      (𝔉.eq_of_range_fibre_eq u _ _ ((hr ⟨C, hC⟩).trans hCr)))⟩
  · haveI := hgi C
    haveI := hgo C
    exact 𝔉.pushforward_componentPointsHom_pointCycleClass hE hU'' hΦ hO hΔO s Gs hGs0 u hu
      hus C.1.1 C.1.2 (φ C) (hφ C) (ge C) (hge C)

open Classical in
/-- **The curves cut on a fibre component, read in `E_b(ℂ)`.** For a fibre component `G_s` of
`E_s`, the push-forward to `E_b(ℂ)` (along `G_s(ℂ) → E_s(ℂ) ≅ E_b(ℂ)`) of the sum of the classes
of the curves cut on `G_s` by `P` is the part over the piece `Ω ≅ G_s(ℂ)` of the sum of the
classes of the components of the fibre `V_u` of the family over `s`. -/
theorem PrimeDivisorFamily.pushforward_finsum_eq_restrict
    (Ω : TopologicalSpace.Opens (TopCat.of (fibrePointsIn F r (E.support : Set Z) b)))
    (hp : IsProperMap (inclHom Ω)) (s : Δ)
    (Gs : {V : Subvariety E.idealSheaf.subscheme // V.HasDim 2})
    (hGs : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) (Gs.1.support : Set _))
    (hdisj : ∀ (A B : Set E.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {(s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {(s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) B → A ≠ B → Disjoint A B)
    (hΩs : ∀ x, x ∈ Ω ↔ (hΦ.componentHomeomorph hE s x : UnderlyingSpace ℂ Z) ∈
      pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' (Gs.1.support : Set _)))
    (u : ParameterPoint 𝔉.B) (hu : u.complexPoint ∈ 𝔉.baseOpens hO)
    (hus : mapFun (K := ℂ) 𝔉.jB u.complexPoint = s) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (hΦ.componentPointsHom hE s Gs.1 hGs.1.2)
        (hΦ.isClosedEmbedding_componentPointsHom hE s Gs.1 hGs.1.2).isProperMap
        (2 * 1 : ℕ)).hom
        (∑ᶠ (x : {x : Gs.1.toScheme // Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (Gs.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun A ↦ IsIrreducible A ∧
            A ⊆ Gs.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2) =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (inclHom Ω) hp (2 * 1 : ℕ)).hom
        ((restrict ℚ (ModuleCat.of ℚ ℚ) Ω (2 * 1 : ℕ)).hom
          (∑ᶠ (y : {y : ParameterPoint.fibre 𝔉.f u // Stacks.Chow.relativeDimension
              (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ)) y = (1 : ℕ)})
            (_ : y.1 ∈ genericPoints (ParameterPoint.fibre 𝔉.f u)),
            (pushforward ℚ (ModuleCat.of ℚ ℚ)
              (fibreAmbientPointsHom 𝔉.ι 𝔉.g 𝔉.hf u ≫ fibreTransportHom
                (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO)
                (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO) hu)
              ((isProperMap_fibreTransportHom _ _ hu).comp
                (isProperMap_fibreAmbientPointsHom 𝔉.ι 𝔉.g 𝔉.hf u))
              (2 * 1 : ℕ)).hom (Chow.pointCycleClass ℚ y.1 y.2))) := by
  have hspt : (s : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ) = 𝔉.jB.base u.point := by
    rw [← hus, 𝔉.toHom_mapFun_jB]
  have hGs' := hGs
  rw [hspt] at hGs' hdisj
  haveI : IsLocallyNoetherian (ParameterPoint.fibre 𝔉.f u) :=
    LocallyOfFiniteType.isLocallyNoetherian ((ParameterPoint.fibre 𝔉.f u) ↘ Spec (.of ℂ))
  haveI : CompactSpace (ParameterPoint.fibre 𝔉.f u) :=
    (quasiCompact_iff_compactSpace (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ))).mp inferInstance
  haveI : AlgebraicGeometry.IsNoetherian (ParameterPoint.fibre 𝔉.f u) := ⟨⟩
  set J := {y : {y : ParameterPoint.fibre 𝔉.f u // Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ)) y = (1 : ℕ)} |
      y.1 ∈ genericPoints (ParameterPoint.fibre 𝔉.f u)} with hJ
  have hJfin : J.Finite := finite_of_closure_singleton_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents fun _ hy ↦ hy
  choose c hc using fun y : {y : ParameterPoint.fibre 𝔉.f u // Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ)) y = (1 : ℕ)} ↦
    exists_pushforward_pointCycleClass_eq_ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
      (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO) u hu
      (n := 1) y.1 y.2
  have hR := pushforward_inclHom_restrict_finsum (R := ℚ)
    (A := fun y : {y : ParameterPoint.fibre 𝔉.f u // Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ)) y = (1 : ℕ)} ↦
      TopCat.of (UnderlyingSpace ℂ (Stacks.Chow.integralComponentAt y.1).subscheme))
    (fun y ↦ ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
      (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO) u hu y.1)
    (fun y ↦ isProperMap_ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf _ _ u hu y.1)
    Ω hp ((2 * 1 : ℕ) : ℤ) c hJfin (fun y _ ↦ by
      rcases 𝔉.range_amb_subset_or_disjoint hE hU'' hΦ hO hΔO Ω s Gs.1 u hu hus hGs' hdisj hΩs
        y.1 with h | h
      · exact Or.inl h.2
      · exact Or.inr h.2)
  have hsum : (∑ᶠ (y : {y : ParameterPoint.fibre 𝔉.f u // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ)) y = (1 : ℕ)})
      (_ : y.1 ∈ genericPoints (ParameterPoint.fibre 𝔉.f u)),
      (pushforward ℚ (ModuleCat.of ℚ ℚ)
        (fibreAmbientPointsHom 𝔉.ι 𝔉.g 𝔉.hf u ≫ fibreTransportHom
          (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO)
          (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO) hu)
        ((isProperMap_fibreTransportHom _ _ hu).comp
          (isProperMap_fibreAmbientPointsHom 𝔉.ι 𝔉.g 𝔉.hf u))
        (2 * 1 : ℕ)).hom (Chow.pointCycleClass ℚ y.1 y.2)) =
      ∑ᶠ y ∈ J, (pushforward ℚ (ModuleCat.of ℚ ℚ) (ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf
        (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO) u hu
          y.1) (isProperMap_ambientComponentTransportHom 𝔉.ι 𝔉.g 𝔉.hf _ _ u hu y.1)
        ((2 * 1 : ℕ) : ℤ)).hom (c y) :=
    finsum_congr fun y ↦ finsum_congr fun _ ↦ hc y
  rw [hsum, hR]
  haveI : TopologicalSpace.NoetherianSpace Gs.1.toScheme := noetherianSpace_of_isComplexScheme
  have hIfin : {x : {x : Gs.1.toScheme // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Gs.1.toScheme ↘ Spec (.of ℂ)) x =
          (1 : ℕ)} |
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Gs.1.ι.base ⁻¹' (P.support : Set _))
        (closure {x.1})}.Finite :=
    finite_of_closure_singleton_mem (finite_setOf_maximal (Gs.1.ι.base ⁻¹' (P.support : Set _)))
      fun _ hC ↦ hC
  refine (AddMonoidHom.map_finsum_mem (fun x : {x : Gs.1.toScheme // Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Gs.1.toScheme ↘ Spec (.of ℂ)) x =
        (1 : ℕ)} ↦
      Chow.pointCycleClass ℚ x.1 x.2)
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (hΦ.componentPointsHom hE s Gs.1 hGs.1.2)
      (hΦ.isClosedEmbedding_componentPointsHom hE s Gs.1 hGs.1.2).isProperMap
      ((2 * 1 : ℕ) : ℤ)).hom.toAddMonoidHom hIfin).trans ?_
  refine (𝔉.finsum_pushforward_componentPointsHom_eq hE hU'' hΦ hO hΔO Ω s Gs.1 hGs.1.2 u hu hus
    hGs' hdisj hΩs).trans ?_
  exact finsum_mem_congr rfl fun y _ ↦ hc y

include hU'' hΦ hΔO in
/-- Every point of `Δ` is the image under `jB` of a point of `B(ℂ)`. -/
theorem PrimeDivisorFamily.exists_mapFun_jB_eq (s : UnderlyingSpace ℂ Y) (hs : s ∈ Δ) :
    ∃ w, mapFun (K := ℂ) 𝔉.jB w = s := by
  rw [← Set.mem_range, 𝔉.range_jB, pointsOver_inter]
  exact ⟨pointsOver_mono hU'' (hΦ.subset hs), (hΔO ▸ hs).2⟩

include hΔO in
/-- A point `w` of `B(ℂ)` lies in `baseOpens hO` exactly when `jB w` lies in `Δ`. -/
theorem PrimeDivisorFamily.mem_baseOpens_iff' (w : UnderlyingSpace ℂ 𝔉.B) :
    w ∈ 𝔉.baseOpens hO ↔ mapFun (K := ℂ) 𝔉.jB w ∈ Δ := by
  rw [hΔO]
  exact 𝔉.mem_baseOpens_iff hO w

include hU'' hΦ hΔO in
/-- The open of the base curve over `Δ` is connected. -/
theorem PrimeDivisorFamily.connectedSpace_baseOpens : ConnectedSpace (𝔉.baseOpens hO) := by
  obtain ⟨wb, hwb⟩ := 𝔉.exists_mapFun_jB_eq hU'' hΦ hΔO b hbΔ
  have himg : mapFun (K := ℂ) 𝔉.jB '' (𝔉.baseOpens hO : Set (UnderlyingSpace ℂ 𝔉.B)) = Δ := by
    ext s
    refine ⟨fun ⟨w, hw, hws⟩ ↦ hws ▸ (𝔉.mem_baseOpens_iff' hO hΔO w).1 hw, fun hs ↦ ?_⟩
    obtain ⟨w, rfl⟩ := 𝔉.exists_mapFun_jB_eq hU'' hΦ hΔO s hs
    exact ⟨w, (𝔉.mem_baseOpens_iff' hO hΔO w).2 hs, rfl⟩
  have hc : IsConnected (𝔉.baseOpens hO : Set (UnderlyingSpace ℂ 𝔉.B)) :=
    ⟨⟨wb, (𝔉.mem_baseOpens_iff' hO hΔO wb).2 (hwb ▸ hbΔ)⟩,
      𝔉.isEmbedding_jB.isInducing.isPreconnected_image.1 (himg ▸ hΦ.isPreconnected)⟩
  exact Subtype.connectedSpace hc

include hU'' hΦ hΔO in
/-- The parameter point of the base curve over a point of `Δ`. -/
theorem PrimeDivisorFamily.exists_parameterPoint (s : UnderlyingSpace ℂ Y) (hs : s ∈ Δ) :
    ∃ u : ParameterPoint 𝔉.B, u.complexPoint ∈ 𝔉.baseOpens hO ∧
      mapFun (K := ℂ) 𝔉.jB u.complexPoint = s := by
  obtain ⟨w, rfl⟩ := 𝔉.exists_mapFun_jB_eq hU'' hΦ hΔO s hs
  refine ⟨ParameterPoint.ofIsClosed (w.toHom (IsLocalRing.closedPoint ℂ))
    (equivClosedPoints (K := ℂ) 𝔉.B w).2
    (isRegularLocalRing_stalk_of_smooth_over_field (𝔉.B ↘ Spec (.of ℂ)) _), ?_⟩
  have hw : (ParameterPoint.ofIsClosed (w.toHom (IsLocalRing.closedPoint ℂ))
      (equivClosedPoints (K := ℂ) 𝔉.B w).2
      (isRegularLocalRing_stalk_of_smooth_over_field (𝔉.B ↘ Spec (.of ℂ)) _)).complexPoint = w :=
    UnderlyingSpace.eq_iff_toHom_closedPoint_eq.2
      ((ParameterPoint.complexPoint_toHom_closedPoint _).trans
        (ParameterPoint.point_ofIsClosed _ _ _))
  rw [hw]
  exact ⟨(𝔉.mem_baseOpens_iff' hO hΔO w).2 hs, rfl⟩

include 𝔉 hU'' hO hΔO in
open Classical in
/-- **The curves cut by `P` on `G_b` and on `G_t`, read in `E_b(ℂ)`, have equal classes**
(Fulton, Lemma 19.1.3 and Lemma 19.2(c)). -/
theorem PrimeDivisorFamily.pushforward_componentPointsHom_finsum_eq
    (hdisj : ∀ y ∈ (U'' : Set Y) ∩ T, ∀ (A B : Set E.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
      A ≠ B → Disjoint A B)
    (t : Δ) (Gb Gt : {V : Subvariety E.idealSheaf.subscheme // V.HasDim 2})
    (hGb : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {b.toHom (IsLocalRing.closedPoint ℂ)}) (Gb.1.support : Set _))
    (hGt : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) (Gt.1.support : Set _))
    (hGbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈
        pointsOver (E.idealSheaf.subschemeι.base '' (Gb.1.support : Set _)) ↔
      (Φ (z, t) : UnderlyingSpace ℂ Z) ∈
        pointsOver (E.idealSheaf.subschemeι.base '' (Gt.1.support : Set _))) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (hΦ.componentPointsHom hE ⟨b, hbΔ⟩ Gb.1 hGb.1.2)
        (hΦ.isClosedEmbedding_componentPointsHom hE ⟨b, hbΔ⟩ Gb.1 hGb.1.2).isProperMap
        (2 * 1 : ℕ)).hom
        (∑ᶠ (x : {x : Gb.1.toScheme // Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (Gb.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun A ↦ IsIrreducible A ∧
            A ⊆ Gb.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2) =
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (hΦ.componentPointsHom hE t Gt.1 hGt.1.2)
        (hΦ.isClosedEmbedding_componentPointsHom hE t Gt.1 hGt.1.2).isProperMap
        (2 * 1 : ℕ)).hom
        (∑ᶠ (x : {x : Gt.1.toScheme // Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (Gt.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun A ↦ IsIrreducible A ∧
            A ⊆ Gt.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2) := by
  haveI := 𝔉.connectedSpace_baseOpens hU'' hΦ hO hΔO
  obtain ⟨sb, hsbW, hsb⟩ := 𝔉.exists_parameterPoint hU'' hΦ hO hΔO b hbΔ
  obtain ⟨st, hstW, hst⟩ := 𝔉.exists_parameterPoint hU'' hΦ hO hΔO t t.2
  have hmem : ∀ s ∈ Δ, s.toHom (IsLocalRing.closedPoint ℂ) ∈ (U'' : Set Y) ∩ T := fun s hs ↦
    ⟨hΦ.subset hs, (hΔO ▸ hs).2⟩
  set Ω : TopologicalSpace.Opens (TopCat.of (fibrePointsIn F r (E.support : Set Z) b)) :=
    ⟨_, isOpen_setOf_mem_pointsOver_fibreComponent Gb.1 (hdisj _ (hmem b hbΔ)) hGb⟩ with hΩ
  have hΩcl : IsClosed {x : fibrePointsIn F r (E.support : Set Z) b |
      (x : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ)
        (E.idealSheaf.subschemeι.base '' (Gb.1.support : Set _))} :=
    (isClosed_pointsOver
      (E.idealSheaf.subschemeι.isClosedMap _ Gb.1.ideal.support.isClosed)).preimage
      continuous_subtype_val
  have hp : IsProperMap (inclHom Ω) := (Topology.IsClosedEmbedding.subtypeVal hΩcl).isProperMap
  have hΩb : ∀ x, x ∈ Ω ↔ (hΦ.componentHomeomorph hE ⟨b, hbΔ⟩ x : UnderlyingSpace ℂ Z) ∈
      pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' (Gb.1.support : Set _)) := fun x ↦ by
    rw [hΦ.coe_componentHomeomorph_base]; rfl
  have hΩt : ∀ x, x ∈ Ω ↔ (hΦ.componentHomeomorph hE t x : UnderlyingSpace ℂ Z) ∈
      pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' (Gt.1.support : Set _)) := fun x ↦
    hGbt ⟨x.1, x.2.2⟩
  haveI : TopologicalSpace.MetrizableSpace
      (TopCat.of (fibrePointsIn F r (E.support : Set Z) b)) := by
    haveI : TopologicalSpace.MetrizableSpace (UnderlyingSpace ℂ Z) :=
      UnderlyingSpace.metrizableSpace_of_isComplexScheme Z
    exact Topology.IsEmbedding.subtypeVal.metrizableSpace
  have hB := finsum_pushforward_fibreTransportHom_fibreAmbientPointsHom_pointCycleClass_eq_of_mult
    (R := ℚ) 𝔉.dim_B 𝔉.ι 𝔉.g 𝔉.f 𝔉.hf (n := 1) 𝔉.dimension_V (𝔉.baseOpens hO)
    (𝔉.prodHomeomorph hE hU'' hΦ hO hΔO) (𝔉.mapFun_g_prodHomeomorph hE hU'' hΦ hO hΔO) sb st
    hsbW hstW (𝔉.mult_fibre sb) (𝔉.mult_fibre st)
  rw [𝔉.pushforward_finsum_eq_restrict hE hU'' hΦ hO hΔO Ω hp ⟨b, hbΔ⟩ Gb hGb
      (hdisj _ (hmem b hbΔ)) hΩb sb hsbW hsb,
    𝔉.pushforward_finsum_eq_restrict hE hU'' hΦ hO hΔO Ω hp t Gt hGt
      (hdisj _ (hmem t t.2)) hΩt st hstW hst]
  exact congrArg _ (congrArg _ hB)

end perFibre

open Classical in
/-- **Transport of the curves cut by a prime divisor `P` of `E`, along its algebraic family.** -/
theorem PrimeDivisorFamily.fibreComponentTransport_eq [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (𝔉 : PrimeDivisorFamily r T E P U) (hE : E ∈ F.support)
    {U'' : Y.Opens} (hU'' : U'' ≤ U)
    (hdisj : ∀ y ∈ (U'' : Set Y) ∩ T, ∀ (A B : Set E.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
      A ≠ B → Disjoint A B)
    {b : UnderlyingSpace ℂ Y} {Δ : Set (UnderlyingSpace ℂ Y)} {hbΔ : b ∈ Δ}
    {Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)}
    (hΦ : IsExceptionalTrivialization r F T U'' hbΔ Φ)
    (t : Δ) (Gb Gt : {V : Subvariety E.idealSheaf.subscheme // V.HasDim 2})
    (hGb : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {b.toHom (IsLocalRing.closedPoint ℂ)}) (Gb.1.support : Set _))
    (hGt : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) (Gt.1.support : Set _))
    (hGbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
      (z : UnderlyingSpace ℂ Z) ∈
        pointsOver (E.idealSheaf.subschemeι.base '' (Gb.1.support : Set _)) ↔
      (Φ (z, t) : UnderlyingSpace ℂ Z) ∈
        pointsOver (E.idealSheaf.subschemeι.base '' (Gt.1.support : Set _))) :
    fibreComponentTransport hΦ t hE hGb.1.2 hGt.1.2 hGbt (2 * 1)
        (∑ᶠ (x : {x : Gb.1.toScheme // Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (Gb.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun A ↦ IsIrreducible A ∧
            A ⊆ Gb.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2) =
      ∑ᶠ (x : {x : Gt.1.toScheme // Stacks.Chow.relativeDimension
          (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (Gt.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
        (_ : Maximal (fun A ↦ IsIrreducible A ∧
          A ⊆ Gt.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
        Chow.pointCycleClass ℚ x.1 x.2 := by
  obtain ⟨O, hO, hΔO⟩ := hΦ.isOpen
  have h := 𝔉.pushforward_componentPointsHom_finsum_eq hE hU'' hΦ hO hΔO hdisj t Gb Gt hGb hGt
    hGbt
  obtain ⟨e, he, hθ⟩ := hΦ.exists_fibreComponentTransport_eq t hE hGb.1.2 hGt.1.2 hGbt
  rw [hθ]
  have hκb := hΦ.isClosedEmbedding_componentPointsHom hE ⟨b, hbΔ⟩ Gb.1 hGb.1.2
  have hκt := hΦ.isClosedEmbedding_componentPointsHom hE t Gt.1 hGt.1.2
  have hcomp := hΦ.ofHom_comp_componentPointsHom t hE hGb.1.2 hGt.1.2 e he
  have hrange : IsOpen (Set.range (hΦ.componentPointsHom hE t Gt.1 hGt.1.2)) := by
    rw [hΦ.range_componentPointsHom_eq_of_iff t hE hGt.1.2 hGbt]
    exact isOpen_setOf_mem_pointsOver_fibreComponent Gb.1
      (hdisj _ ⟨hΦ.subset hbΔ, (hΔO ▸ hbΔ).2⟩) hGb
  apply pushforward_injective_of_isOpen_range (R := ℚ) _ hκt hrange
  rw [homologyEquivOfHomeomorph_apply]
  have e1 := borelMooreHomology.pushforward_comp_apply ℚ (TopCat.ofHom (e : C(_, _)))
    (hΦ.componentPointsHom hE t Gt.1 hGt.1.2) e.isProperMap hκt.isProperMap
    (hcomp ▸ hκb.isProperMap) ((2 * 1 : ℕ) : ℤ)
    (∑ᶠ (x : {x : Gb.1.toScheme // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (Gb.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
      (_ : Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ Gb.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
      Chow.pointCycleClass ℚ x.1 x.2)
  have e2 := borelMooreHomology.pushforward_apply_congr ℚ hcomp (hcomp ▸ hκb.isProperMap)
    hκb.isProperMap ((2 * 1 : ℕ) : ℤ)
    (∑ᶠ (x : {x : Gb.1.toScheme // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (Gb.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
      (_ : Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ Gb.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
      Chow.pointCycleClass ℚ x.1 x.2)
  exact e1.trans (e2.trans h)

end assembly

section primeDivisorTransport

open Classical in
/-- The curves cut by `P` on a surface `G` of `E` missing `P`: none. -/
theorem finsum_restrictionClass_eq_zero {E : Mori.PrimeDivisor Z}
    {P : Mori.PrimeDivisor E.idealSheaf.subscheme} (G : Subvariety E.idealSheaf.subscheme)
    (h : ∀ x : G.toScheme, G.ι.base x ∉ (P.support : Set _)) :
    ∑ᶠ (x : {x : G.toScheme // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (G.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
      (_ : Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ G.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
      Chow.pointCycleClass ℚ x.1 x.2 = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun C ↦ ?_
  haveI : IsEmpty (Maximal (fun A ↦ IsIrreducible A ∧
      A ⊆ G.ι.base ⁻¹' (P.support : Set _)) (closure {C.1})) := ⟨fun hC ↦ by
    obtain ⟨x, hx⟩ := hC.1.1.nonempty
    exact h x (hC.1.2 hx)⟩
  exact finsum_of_isEmpty _

open Classical in
/-- **(ii) for one prime divisor `P` of `E`.** -/
theorem exists_open_restrictionClass_prime
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) (E : F.support)
    (P : Mori.PrimeDivisor E.1.idealSheaf.subscheme) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ (U'' : Y.Opens), U'' ≤ U → ∀ (b : UnderlyingSpace ℂ Y) (Δ : Set (UnderlyingSpace ℂ Y))
        (hbΔ : b ∈ Δ)
        (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
          ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
        (hΦ : IsExceptionalTrivialization r F T U'' hbΔ Φ)
        (t : Δ) (Gb Gt : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2})
        (hGb : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
          {b.toHom (IsLocalRing.closedPoint ℂ)}) (Gb.1.support : Set _))
        (hGt : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
          {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) (Gt.1.support : Set _))
        (hGbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
          (z : UnderlyingSpace ℂ Z) ∈
            pointsOver (E.1.idealSheaf.subschemeι.base '' (Gb.1.support : Set _)) ↔
          (Φ (z, t) : UnderlyingSpace ℂ Z) ∈
            pointsOver (E.1.idealSheaf.subschemeι.base '' (Gt.1.support : Set _))),
        fibreComponentTransport hΦ t E.2 hGb.1.2 hGt.1.2 hGbt (2 * 1)
            (∑ᶠ (x : {x : Gb.1.toScheme // Stacks.Chow.relativeDimension
                (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (Gb.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
              (_ : Maximal (fun A ↦ IsIrreducible A ∧
                A ⊆ Gb.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
              Chow.pointCycleClass ℚ x.1 x.2) =
          ∑ᶠ (x : {x : Gt.1.toScheme // Stacks.Chow.relativeDimension
              (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
              (Gt.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
            (_ : Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ Gt.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
            Chow.pointCycleClass ℚ x.1 x.2 := by
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  by_cases hTP : (T : Set Y) ⊆ r.base '' (E.1.idealSheaf.subschemeι.base '' P.support)
  · obtain ⟨U₁, hU₁, ⟨𝔉⟩⟩ := exists_primeDivisorFamily hM T hT1 E.1 E.2 P hTP
    obtain ⟨U₂, hU₂, hd⟩ := exists_disjoint_maximal_fibre hM T hT1
    refine ⟨U₁ ⊓ U₂, inter_inter_nonempty_of_irreducibleCloseds T hU₁ hU₂,
      fun U'' hU'' b Δ hbΔ Φ hΦ t Gb Gt hGb hGt hGbt ↦ ?_⟩
    exact 𝔉.fibreComponentTransport_eq E.2 (hU''.trans inf_le_left)
      (fun y hy ↦ hd y ⟨(hU''.trans inf_le_right) hy.1, hy.2⟩ E) hΦ t Gb Gt hGb hGt hGbt
  -- `P` does not dominate `T`: off the closed set `r(P)`, the fibres of `P` are empty
  have hPcl : IsClosed (r.base '' (E.1.idealSheaf.subschemeι.base '' P.support)) :=
    r.isClosedMap _ (E.1.idealSheaf.subschemeι.isClosedMap _ P.idealSheaf.support.isClosed)
  refine ⟨⟨_, hPcl.isOpen_compl⟩, ?_, fun U'' hU'' b Δ hbΔ Φ hΦ t Gb Gt hGb hGt hGbt ↦ ?_⟩
  · obtain ⟨y, hyT, hyP⟩ := Set.not_subset.1 hTP
    exact ⟨y, hyP, hyT⟩
  have hmiss : ∀ (s : UnderlyingSpace ℂ Y), s ∈ Δ → ∀ G : Subvariety E.1.idealSheaf.subscheme,
      (G.support : Set _) ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {s.toHom (IsLocalRing.closedPoint ℂ)} →
      ∀ x : G.toScheme, G.ι.base x ∉ (P.support : Set _) := by
    intro s hs G hG x hx
    have hxG : G.ι.base x ∈ (G.support : Set _) := by
      rw [MMP.Intersection.Scheme.Subvariety.support_eq, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩
    have h1 : (E.1.idealSheaf.subschemeι ≫ r).base (G.ι.base x) =
        s.toHom (IsLocalRing.closedPoint ℂ) := hG hxG
    apply hU'' (hΦ.subset hs)
    rw [← h1]
    exact ⟨_, ⟨_, hx, rfl⟩, rfl⟩
  rw [finsum_restrictionClass_eq_zero Gb.1 (hmiss b hbΔ Gb.1 hGb.1.2),
    finsum_restrictionClass_eq_zero Gt.1 (hmiss t t.2 Gt.1 hGt.1.2), map_zero]

end primeDivisorTransport

end primeDivisorCurves

open Classical in
/-- **(ii) Transport of the curves cut by a divisor.** Fix `ℚ`-divisors `L E` on the components
`E` of `F`. Over a general open `U` of `T`, for every exceptional trivialization `Φ` over
`Δ ∋ b`, `t ∈ Δ` and fibre components `G_b`, `G_t` matched by `Φ_t`, the isomorphism
`H_2(G_b) ≅ H_2(G_t)` induced by `Φ_t` sends the class of the curves cut on `G_b` by `L E` to the
class of the curves cut on `G_t`: for a prime divisor `P` of `E` dominating `T`, the fibres of
`P ∩ G_{T°} → T°` are reduced over a general open (generic smoothness), so their reduced classes
are the specializations of `cl(P ∩ G_{T°})` (Fulton's Lemma 19.1.3), constant along the
trivialization (Lemma 19.2(c)); a prime divisor not dominating `T` misses the general fibres. -/
theorem fibreComponentTransport_restrictionClass
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ (b : UnderlyingSpace ℂ Y) (Δ : Set (UnderlyingSpace ℂ Y)) (hbΔ : b ∈ Δ)
        (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
          ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
        (hΦ : IsExceptionalTrivialization r F T U hbΔ Φ)
        (t : Δ) (E : F.support) (Gb Gt : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2})
        (hGb : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
          {b.toHom (IsLocalRing.closedPoint ℂ)}) (Gb.1.support : Set _))
        (hGt : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
          {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) (Gt.1.support : Set _))
        (hGbt : ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
          (z : UnderlyingSpace ℂ Z) ∈
            pointsOver (E.1.idealSheaf.subschemeι.base '' (Gb.1.support : Set _)) ↔
          (Φ (z, t) : UnderlyingSpace ℂ Z) ∈
            pointsOver (E.1.idealSheaf.subschemeι.base '' (Gt.1.support : Set _))),
        fibreComponentTransport hΦ t E.2 hGb.1.2 hGt.1.2 hGbt (2 * 1)
            ((L E).sum fun P c ↦ c • ∑ᶠ (x : {x : Gb.1.toScheme // Stacks.Chow.relativeDimension
                (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (Gb.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
              (_ : Maximal (fun A ↦ IsIrreducible A ∧
                A ⊆ Gb.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
              Chow.pointCycleClass ℚ x.1 x.2) =
          (L E).sum fun P c ↦ c • ∑ᶠ (x : {x : Gt.1.toScheme // Stacks.Chow.relativeDimension
              (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
              (Gt.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
            (_ : Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ Gt.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
            Chow.pointCycleClass ℚ x.1 x.2 := by
  choose UP hUP hUPP using fun (E : F.support) (P : Mori.PrimeDivisor E.1.idealSheaf.subscheme) ↦
    exists_open_restrictionClass_prime hM T hTs hT1 E P
  let Uf : (Σ E : F.support, Mori.PrimeDivisor E.1.idealSheaf.subscheme) → Y.Opens :=
    fun p ↦ UP p.1 p.2
  have hne : ∀ s : Finset (Σ E : F.support, Mori.PrimeDivisor E.1.idealSheaf.subscheme),
      (((s.inf Uf : Y.Opens) : Set Y) ∩ T).Nonempty := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
      exact ⟨x, by simp, hx⟩
    | insert a s _ ih =>
      rw [Finset.inf_insert]
      exact inter_inter_nonempty_of_irreducibleCloseds T (hUP a.1 a.2) ih
  let S : Finset (Σ E : F.support, Mori.PrimeDivisor E.1.idealSheaf.subscheme) :=
    (Finset.univ : Finset F.support).sigma fun E ↦ (L E).support
  refine ⟨S.inf Uf, hne S, fun b Δ hbΔ Φ hΦ t E Gb Gt hGb hGt hGbt ↦ ?_⟩
  have key : ∀ P ∈ (L E).support, fibreComponentTransport hΦ t E.2 hGb.1.2 hGt.1.2 hGbt (2 * 1)
            (∑ᶠ (x : {x : Gb.1.toScheme // Stacks.Chow.relativeDimension
                (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (Gb.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
              (_ : Maximal (fun A ↦ IsIrreducible A ∧
                A ⊆ Gb.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
              Chow.pointCycleClass ℚ x.1 x.2) =
          ∑ᶠ (x : {x : Gt.1.toScheme // Stacks.Chow.relativeDimension
              (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
              (Gt.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
            (_ : Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ Gt.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
            Chow.pointCycleClass ℚ x.1 x.2 := fun P hP ↦ by
    have hmem : (⟨E, P⟩ : Σ E : F.support, Mori.PrimeDivisor E.1.idealSheaf.subscheme) ∈ S :=
      Finset.mem_sigma.2 ⟨Finset.mem_univ E, hP⟩
    have h1 : S.inf Uf ≤ UP E P := Finset.inf_le (f := Uf) hmem
    exact hUPP E P _ h1 b Δ hbΔ Φ hΦ t Gb Gt hGb hGt hGbt
  rw [Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun P hP ↦ ?_
  rw [LinearEquiv.map_smul, key P hP]

/-! ### The transport of fibre classes -/

/-- The points of `Y(ℂ)` over an open of `Y` form an open set. -/
theorem isOpen_pointsOver_opens (U : Y.Opens) : IsOpen (pointsOver (K := ℂ) (U : Set Y)) := by
  convert isOpen_setOf_le_preimage (K := ℂ) U using 1
  ext p
  exact (top_le_preimage_iff p U).symm

open Classical in
/-- **Transport of the fibre curve classes.** Fix `ℚ`-divisors `L E` on the components `E` of
`F`. Over a general open `U₀` of the singular curve `T`, at every `b ∈ (U₀ ∩ T)(ℂ)` there is a
product germ `Φ : F_b × Δ ≃ₜ F_Δ` as in `exists_homeomorph_prod_exceptionalFibre` such that for
every `t ∈ Δ` and every component `G_b` of a fibre `E_b`, the image `G_t = Φ_t(G_b)` is a
component of `E_t` and some linear isomorphism `H_2(G_b, ℚ) ≃ H_2(G_t, ℚ)` (the one induced by
`Φ_t`, `fibreComponentTransport`) sends the class of every curve `C ⊆ G_b` lying in another
component `E'` to that of the curve `Φ_t(C)`, and the class of the curves cut on `G_b` by `L E`
to that of the curves cut on `G_t`. -/
theorem exists_transport_fibreClasses
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧
      ∀ b ∈ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T), ∀ N ∈ 𝓝 b,
        ∃ Δ : Set (UnderlyingSpace ℂ Y), Δ ⊆ N ∧
          (∃ O, IsOpen O ∧ Δ = O ∩ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T)) ∧
          IsPreconnected Δ ∧ ∃ hbΔ : b ∈ Δ,
          ∃ Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
              ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ),
            (∀ p, mapFun r (Φ p : UnderlyingSpace ℂ Z) = p.2) ∧
            (∀ z, (Φ (z, ⟨b, hbΔ⟩) : UnderlyingSpace ℂ Z) = z) ∧
            (∀ E ∈ F.support, ∀ p, (Φ p : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) ↔
              (p.1 : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z)) ∧
            ∀ t : Δ, ∀ (E : F.support)
              (Gb : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2}),
              Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
                {b.toHom (IsLocalRing.closedPoint ℂ)}) (Gb.1.support : Set _) →
              ∃ Gt : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
                Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
                  {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
                  (Gt.1.support : Set _) ∧
                (∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
                    (z : UnderlyingSpace ℂ Z) ∈ pointsOver
                    (E.1.idealSheaf.subschemeι.base '' (Gb.1.support : Set _)) ↔
                  (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver
                    (E.1.idealSheaf.subschemeι.base '' (Gt.1.support : Set _))) ∧
                ∃ θ : RationalHomology Gb.1.toScheme (2 * 1) ≃ₗ[ℚ]
                    RationalHomology Gt.1.toScheme (2 * 1),
                  (∀ (E' : F.support), E' ≠ E →
                    ∀ (Cb : {x : Gb.1.toScheme // Stacks.Chow.relativeDimension
                        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                        (Gb.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
                      (Ct : {x : Gt.1.toScheme // Stacks.Chow.relativeDimension
                        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                        (Gt.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)}),
                    (Gb.1.ι ≫ E.1.idealSheaf.subschemeι).base '' closure {Cb.1} ⊆
                      (E'.1.support : Set Z) →
                    (∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
                    (z : UnderlyingSpace ℂ Z) ∈ pointsOver
                        ((Gb.1.ι ≫ E.1.idealSheaf.subschemeι).base '' closure {Cb.1}) ↔
                      (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver
                        ((Gt.1.ι ≫ E.1.idealSheaf.subschemeι).base '' closure {Ct.1})) →
                    θ (Chow.pointCycleClass ℚ Cb.1 Cb.2) =
                      Chow.pointCycleClass ℚ Ct.1 Ct.2) ∧
                  θ ((L E).sum fun P c ↦ c • ∑ᶠ (x : {x : Gb.1.toScheme //
                        Stacks.Chow.relativeDimension
                        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                        (Gb.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
                      (_ : Maximal (fun A ↦ IsIrreducible A ∧
                        A ⊆ Gb.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
                      Chow.pointCycleClass ℚ x.1 x.2) =
                    (L E).sum fun P c ↦ c • ∑ᶠ (x : {x : Gt.1.toScheme //
                        Stacks.Chow.relativeDimension
                        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                        (Gt.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
                      (_ : Maximal (fun A ↦ IsIrreducible A ∧
                        A ⊆ Gt.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
                      Chow.pointCycleClass ℚ x.1 x.2 := by
  haveI : MMP.Mori.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hM.isResolution.1
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  obtain ⟨U₀, hU₀, hH1⟩ := exists_homeomorph_prod_exceptionalFibre hM T hTs hT1
  obtain ⟨U₁, hU₁, h₁⟩ := exists_maximal_fibre_transport hM T hTs hT1
  obtain ⟨U₂, hU₂, h₂⟩ := fibreComponentTransport_doubleCurve hM T hTs hT1
  obtain ⟨U₃, hU₃, h₃⟩ := fibreComponentTransport_restrictionClass hM L T hTs hT1
  set U : Y.Opens := U₀ ⊓ U₁ ⊓ U₂ ⊓ U₃ with hU
  have hUT : ((U : Set Y) ∩ T).Nonempty :=
    inter_inter_nonempty_of_irreducibleCloseds T
      (inter_inter_nonempty_of_irreducibleCloseds T
        (inter_inter_nonempty_of_irreducibleCloseds T hU₀ hU₁) hU₂) hU₃
  have hU0 : U ≤ U₀ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hU1 : U ≤ U₁ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hU2 : U ≤ U₂ := inf_le_left.trans inf_le_right
  have hU3 : U ≤ U₃ := inf_le_right
  refine ⟨U, hUT, fun b hb N hN ↦ ?_⟩
  have hbU : b ∈ pointsOver (K := ℂ) (U : Set Y) := hb.1
  obtain ⟨Δ, hΔN, ⟨O, hO, hΔO⟩, hΔc, hbΔ, Φ, hΦr, hΦb, hΦE⟩ :=
    hH1 b ⟨hU0 hb.1, hb.2⟩ (N ∩ pointsOver (K := ℂ) (U : Set Y))
      (Filter.inter_mem hN ((isOpen_pointsOver_opens U).mem_nhds hbU))
  have hΔU : Δ ⊆ pointsOver (K := ℂ) (U : Set Y) := fun s hs ↦ (hΔN hs).2
  have hΦ : IsExceptionalTrivialization r F T U hbΔ Φ :=
    { subset := hΔU
      isOpen := ⟨O ∩ pointsOver (K := ℂ) (U₀ : Set Y), hO.inter (isOpen_pointsOver_opens U₀), by
        rw [hΔO, pointsOver_inter, Set.inter_assoc]⟩
      isPreconnected := hΔc
      mapFun_eq := hΦr
      apply_base := hΦb
      mem_iff := hΦE }
  refine ⟨Δ, fun s hs ↦ (hΔN hs).1, ⟨O, hO, ?_⟩, hΔc, hbΔ, Φ, hΦr, hΦb, hΦE,
    fun t E Gb hGb ↦ ?_⟩
  · apply Set.Subset.antisymm
    · intro s hs
      refine ⟨(hΔO ▸ hs).1, hΔU hs, ((hΔO ▸ hs).2).2⟩
    · rw [hΔO]
      exact Set.inter_subset_inter_right _ (pointsOver_mono fun y hy ↦ ⟨hU0 hy.1, hy.2⟩)
  obtain ⟨Gt, hGt, hGbt⟩ := h₁ b Δ hbΔ Φ (hΦ.mono hU1) t E Gb hGb
  exact ⟨Gt, hGt, hGbt, fibreComponentTransport (hΦ.mono hU2) t E.2 hGb.1.2 hGt.1.2 hGbt (2 * 1),
    fun E' hE' Cb Ct hCb hCbt ↦ h₂ b Δ hbΔ Φ (hΦ.mono hU2) t E Gb Gt hGb hGt hGbt E' hE' Cb Ct
      hCb hCbt,
    h₃ b Δ hbΔ Φ (hΦ.mono hU3) t E Gb Gt hGb hGt hGbt⟩

end MMP.Fourfold
