module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
public import MMP.AlgebraicGeometry.MMP.MinimalModel.DltModification
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.FloorProgramInputs
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison

/-!
# Crepant dlt modifications of projective lc fourfolds

Let `(X, Δ)` be a log canonical pair with rational boundary on a normal projective complex
fourfold `X`, with canonical divisor `K_X`. Then there is a projective birational morphism
`p : V ⟶ X` from a `ℚ`-factorial variety `V` such that, with `Δ_V = p⁻¹_* Δ + Exc(p)_red`, the
pair `(V, Δ_V)` is dlt and `K_V + Δ_V = p^*(K_X + Δ)`; that is, `p` is a crepant dlt lift of
`(X, Δ)` (`MMP.Fourfold.IsCrepantDltLift`).

## Main results

* `MMP.Fourfold.exists_isCrepantDltLift`: every projective lc complex fourfold with rational
  boundary has a crepant dlt lift.

## Implementation notes

The conclusion is packaged as `MMP.Fourfold.IsCrepantDltLift`, whose fields are exactly the
assertions of the theorem: `p` projective and birational, `V` `ℚ`-factorial, the boundary equal to
the birational inverse transform of `Δ` plus the reduced exceptional divisor of `p`, the pair
`(V, Δ_V)` dlt, and `Δ_V` the crepant boundary of `(X, Δ)` on `V`.

## References

* [OAI4] the fourfold source, *Projective rational fourfold crepant dlt modification*.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

universe u

namespace Proof_thm_fourfold_projective_dlt_modification_4

open TopologicalSpace MMP MMP.Flips

section InverseTransform

variable {X Y : Scheme.{u}}

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `e` is a partial isomorphism representing a morphism `f : Y ⟶ X` and `g'` a partial map
representing `e⁻¹`, then `f ∘ g'` is the identity where `g'` is defined. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- If `g'` represents `φ` at `η_P` and `g'(η_P) = η_E`, then the strict transform of `P` under
`φ` is `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y}
    (h : Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ :=
    Mori.RationalMap.definedAt_iff.mp (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

private theorem isSeparated_terminal_from {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- Let `f : Y ⟶ X` be a proper birational morphism of varieties with `X` normal. If `f` sends the
generic point of a prime divisor `E` of `Y` to that of a prime divisor `P` of `X`, then the strict
transform of `P` under `f⁻¹` is `E`. -/
private theorem transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (f ≫ sX)
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  have hdef : Mori.RationalMap.DefinedAt (Mori.RationalMap.IsBirational.inverse hf)
      P.genericPoint := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp (RationalMap.isMorphismInCodimOne_inverse hX f hY hf)
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (Mori.RationalMap.dom (Mori.RationalMap.IsBirational.inverse hf)).compl.isClosed)
    rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
      (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- For a proper birational morphism `f : Y ⟶ X` of varieties with `X` normal, the coefficient of
`f⁻¹_* D` along a prime divisor `E` of `Y` with `f(η_E) = η_P` is the coefficient of `D`
along `P`. -/
private theorem birationalInverseTransform_apply_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    birationalInverseTransform f hf D E = D P := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (f ≫ sX)
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hX f hY hf h)
    (fun P' hP' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf hP').symm.trans h)) D

/-- The strict transform `f⁻¹_* D` has coefficient zero along a prime divisor of `Y` lying over no
prime divisor of `X`. -/
private theorem birationalInverseTransform_apply_eq_zero {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} {R : Type*} [AddCommMonoid R]
    (hX : MMP.Mori.IsVariety k sX) {μ : Y ⟶ X} (hY : MMP.Mori.IsVariety k (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) (D : DivisorWithCoeffs R X) {E : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P : MMP.Mori.PrimeDivisor X, μ E.genericPoint ≠ P.genericPoint) :
    birationalInverseTransform μ hμ D E = 0 := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.toIsSeparated
  have : IsSeparated (μ ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (μ ≫ sX)
  exact mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun P hP =>
    h P (genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hμ hP)) D

end InverseTransform

/-- A discrepancy `a(E, X, Δ)` of a divisor `(Y, f, E)` over `X` whose centre is the generic point
of a prime divisor `P` of `X` is `-coeff_P(Δ)`. -/
private theorem IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : MMP.Mori.IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : MMP.Mori.DivisorOver k sX}
    {P : MMP.Mori.PrimeDivisor X} (hP : D.f D.E.genericPoint = P.genericPoint) {a : ℚ}
    (h : MMP.Mori.IsDiscrepancy sX n K Δ D a) : a = -Δ.coeff P := by
  obtain ⟨hX', hK, m, hm, hC, U, hU, τ, hτ, hτa⟩ := h
  refine MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX (P := P)
    ⟨hX', hK, m, hm, hC, U, ?_, τ, hτ, ?_⟩
  · convert hU using 2
    exact hP.symm
  · rw [hτa, MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX
      hK.topologicalKrullDim_eq
      (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX D P hP)]

/-- A prime divisor `F` contained in the exceptional locus of a proper birational morphism
`p : V ⟶ X` onto a normal scheme maps to a point of coheight at least two: `p` is an isomorphism
over the points of coheight at most one. -/
private theorem two_le_coheight_of_subset_exceptionalLocus {X V : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral V] {p : V ⟶ X} [IsProper p]
    (hp : IsBirationalMorphism p) {F : MMP.Mori.PrimeDivisor V}
    (hF : F.support ⊆ MMP.Intersection.exceptionalLocus p) :
    2 ≤ Order.coheight (p F.genericPoint) := by
  have hη : F.genericPoint ∈ F.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  by_contra h
  have h1 : Order.coheight (p F.genericPoint) ≤ 1 := Order.le_of_lt_succ (lt_of_not_ge h)
  have hb := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal p hp h1
  have : IsIso (p ∣_ biregularLocus p) := isBiregular_biregularLocus p
  refine MMP.Intersection.mem_exceptionalLocus_iff.mp (hF hη) (p ⁻¹ᵁ biregularLocus p) hb ?_
  rw [← morphismRestrict_ι]
  infer_instance

/-- A prime divisor contained in the exceptional locus of a proper birational morphism onto a
normal scheme is exceptional for it. -/
private theorem isExceptional_of_subset_exceptionalLocus {X V : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsSeparated (X ↘ ⊤_ Scheme)]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] {p : V ⟶ X} [IsProper p]
    (hp : IsBirationalMorphism p) {F : MMP.Mori.PrimeDivisor V}
    (hF : F.support ⊆ MMP.Intersection.exceptionalLocus p) :
    Mori.RationalMap.IsExceptional (X := V) p.toRationalMap F := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff, le_closedsCodimension_iff_le_coheight]
  intro x hx
  have hsp : p F.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure]
    refine (closure_minimal ?_ isClosed_closure) hx
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ F.support := hy
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy'
    exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hy').map p.continuous)
  exact (two_le_coheight_of_subset_exceptionalLocus hp hF).trans (Order.coheight_anti hsp)

open Classical in
/-- **The crepant boundary is `p⁻¹_* Δ + Exc(p)_red`.** Let `p : V ⟶ X` be a proper birational
morphism of normal varieties and `Δ_V` the crepant boundary of `(X, Δ)` on `V`, with coefficient
one along every `p`-exceptional prime divisor. Then the coefficient of `Δ_V` along a prime divisor
`F` of `V` is that of `p⁻¹_* Δ` plus one if `F` lies in the exceptional locus of `p`, and plus zero
otherwise. -/
private theorem coeff_eq_birationalInverseTransform_add {k : Type u} [Field k] [PerfectField k]
    {X V : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {p : V ⟶ X} [IsProper p] (hp : IsBirationalMorphism p)
    (hV : IsNormalVariety k (p ≫ sX)) {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {ΔV : QDivisor V} (hcr : IsCrepantBoundary sX n K Δ p hV hp ΔV)
    (hexc : ∀ F, Mori.RationalMap.IsExceptional (X := V) p.toRationalMap F → ΔV.coeff F = 1)
    (F : MMP.Mori.PrimeDivisor V) :
    ΔV.coeff F = (birationalInverseTransform p hp Δ).coeff F +
      if F.support ⊆ MMP.Intersection.exceptionalLocus p then 1 else 0 := by
  have : IsSeparated sX := hX.1.toIsSeparated
  have := isSeparated_terminal_from sX
  split_ifs with hF
  · have h0 : (birationalInverseTransform p hp Δ).coeff F = 0 :=
      birationalInverseTransform_apply_eq_zero hX.1 hV.1 hp Δ fun P hP => by
        have h2 := two_le_coheight_of_subset_exceptionalLocus hp hF
        rw [hP, P.coheight_genericPoint] at h2
        exact absurd h2 (by decide)
    rw [h0, zero_add, hexc F (isExceptional_of_subset_exceptionalLocus hp hF)]
  · obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hF
    rw [add_zero, neg_inj.mp (IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq hX
      (D := ⟨V, p, hV, hp, F⟩) hQ.symm (hcr F))]
    exact (birationalInverseTransform_apply_of_genericPoint_eq hX p hV.1 hp Δ hQ.symm).symm

private theorem solution :
    ∀ {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {Δ : QDivisor X} (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ),
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (p : V ⟶ X) (ΔV : QDivisor V), IsCrepantDltLift sX K Δ p ΔV := by
  intro X _ _ _ sX hX hdim K hK Δ hΔ
  obtain ⟨V, _, _, _, p, hp, hV, ΔV, hproj, hdlt, hcrep, hexc⟩ :=
    projectiveFloorProgramInputs_four.exists_crepant_dltModification sX hX hdim hΔ
  have : IsProper p := isProper_of_isProjectiveMorphism p hproj
  have : IsSeparated sX := hΔ.1.1.1.toIsSeparated
  have := isSeparated_terminal_from sX
  have hcoeff := coeff_eq_birationalInverseTransform_add hΔ.1.1 hp hV.1 (hcrep K hK)
    fun F hF => (hexc F hF).2
  classical
  let E : Divisor V := Finsupp.onFinset ΔV.support
    (fun F => if F.support ⊆ MMP.Intersection.exceptionalLocus p then 1 else 0) fun F hF => by
      have hF' : F.support ⊆ MMP.Intersection.exceptionalLocus p := by
        by_contra hc; exact hF (if_neg hc)
      rw [Finsupp.mem_support_iff]
      change ΔV.coeff F ≠ 0
      rw [(hexc F (isExceptional_of_subset_exceptionalLocus hp hF')).2]
      exact one_ne_zero
  have hE : MMP.Intersection.IsExceptionalDivisorSum p E := fun F => Finsupp.onFinset_apply ..
  exact ⟨V, ‹_›, ‹_›, ‹_›, p, ΔV, hX, hΔ, ⟨4, hK⟩, hproj, hp, hV,
    ⟨E, hE, DivisorWithCoeffs.ext' fun F => by
      rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, hE F, hcoeff F]; push_cast; rfl⟩,
    hdlt, ⟨4, hcrep K hK⟩⟩

end Proof_thm_fourfold_projective_dlt_modification_4

end

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Crepant dlt modification of a projective lc fourfold.** Let `X` be a normal projective
complex fourfold with canonical divisor `K`, and `(X, Δ)` a log canonical pair with `Δ` a
`ℚ`-divisor. Then there is a projective birational morphism `p : V ⟶ X` from a `ℚ`-factorial
variety `V` such that `Δ_V = p⁻¹_* Δ + Exc(p)_red` makes `(V, Δ_V)` dlt with
`K_V + Δ_V = p^*(K + Δ)`: a crepant dlt lift of `(X, Δ)`. -/
@[mmp "thm_fourfold_projective_dlt_modification_4"]
public theorem exists_isCrepantDltLift
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {Δ : QDivisor X} (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (p : V ⟶ X) (ΔV : QDivisor V), IsCrepantDltLift sX K Δ p ΔV :=
        by revert X sX hX hdim K hK Δ hΔ; first | exact Proof_thm_fourfold_projective_dlt_modification_4.solution | exact Proof_thm_fourfold_projective_dlt_modification_4.solution _ | exact Proof_thm_fourfold_projective_dlt_modification_4.solution _ _ | exact Proof_thm_fourfold_projective_dlt_modification_4.solution _ _ _ | exact Proof_thm_fourfold_projective_dlt_modification_4.solution _ _ _ _

end MMP.Fourfold
