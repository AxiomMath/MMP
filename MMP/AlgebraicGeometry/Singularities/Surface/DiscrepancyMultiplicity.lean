module

public import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolution
public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupNumericalDiscrepancy
public import MMP.AlgebraicGeometry.Intersection.Surface.NumericalPullback
public import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupFactorization
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Positivity.NefTopIntersectionPositive
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal

/-!
# Minimal resolutions, exceptional divisors and terminal pairs on surfaces

This file proves four results of Kollár–Mori, Chapter 4, on surfaces over an algebraically closed
field `k`.

A normal surface `X` has a minimal resolution `f : Y ⟶ X`, a resolution with no exceptional
smooth rational curve of self-intersection `-1`, and every resolution of `X` factors uniquely
through it.

Every exceptional divisor `(Y₁, f₁, E₁)` over a surface `X` has the valuation of an exceptional
curve on some resolution of `X`. The center of `E₁` is a closed point of `X`. Nagata's
compactification of `f₁`, normalized in `Y₁`, is a proper birational morphism `g : Z ⟶ X` from a
normal surface containing `Y₁` as an open subscheme, so the prime divisor `F = closure E₁` of `Z`
has the valuation of `E₁`. On the minimal resolution `q : Y ⟶ Z`, the local ring at a point over
the generic point of `F` dominates the discrete valuation ring `𝒪_{Z,F}` inside the common
function field, hence equals it, and that point is the generic point of the required curve.

Let `X` be smooth, `k` of characteristic zero, `Δ` an effective `ℚ`-divisor and `μ ≤ 1` with
`mult_p Δ ≤ μ` at every closed point `p`. Every resolution `g : Y ⟶ X` is, up to isomorphism
over `X`, a chain of blow-ups of closed points. Along the chain the solution of the numerical
pull-back equations is followed one blow-up at a time: the new exceptional curve of the blow-up
of `p` gets the entry `1 - mult_p Θ`, where `Θ` is the log pull-back, and by induction all entries
are at least `1 - μ` while all multiplicities of the strict transform of `Δ` stay at most `μ`. So
every numerical discrepancy of `(X, Δ)` is at least `1 - μ`.

Finally `(X, Δ)` is terminal near a closed point `x` if and only if `mult_x Δ < 1`. If it is, the
exceptional curve of the blow-up of `x` has discrepancy `1 - mult_x Δ > 0`. Conversely the
multiplicity is upper semicontinuous, so `mult_p Δ ≤ mult_x Δ < 1` on a neighbourhood `U` of `x`;
every exceptional divisor over `U` appears on a resolution of `U`, where its discrepancy is a
numerical discrepancy, hence at least `1 - mult_x Δ`.

## Main results

* `MMP.Mori.exists_isMinimalSurfaceResolution_existsUnique_comp_eq`: a normal surface over an
  algebraically closed field has a minimal resolution through which every resolution factors
  uniquely.
* `MMP.Mori.DivisorOver.IsExceptional.exists_isSmoothResolution_isExceptionalCurve`: every
  exceptional divisor over a surface `X` has the same valuation as an exceptional curve on some
  resolution of `X`.
* `MMP.Mori.IsNumericalDiscrepancy.one_sub_le_of_multiplicityAt_le`: every numerical
  discrepancy of `(X, Δ)` on a resolution of the smooth surface `X` is at least `1 - μ`.
* `MMP.Mori.exists_isExceptional_isDiscrepancy_one_sub_multiplicityAt`: on a smooth surface, the
  exceptional curve of the blow-up of a closed point `x` is an exceptional divisor over `X` with
  center `x` and discrepancy `1 - mult_x Δ`.
* `MMP.Mori.isAt_isTerminalPair_iff_multiplicityAt_lt_one`: on a smooth surface, `(X, Δ)` is
  terminal at a closed point `x` if and only if `mult_x Δ < 1`.

## Implementation notes

A surface is a variety `X` over `k` with `topologicalKrullDim X = 2`. In the minimal resolution
result the instances on the source `Y` that `MMP.Mori.IsMinimalSurfaceResolution` needs are part
of the existential conclusion. The exceptional curve of a divisor over `X` is phrased as a second
divisor over `X` whose morphism is a resolution and whose prime divisor is an exceptional curve,
with the same valuation (`MMP.Mori.DivisorOver.valuation`); `X` need not be normal. Kollár–Mori
obtain the proper model from Zariski's theorem on sequences of blow-ups; Nagata's
compactification gives it at once, together with the open embedding of `Y₁` (KM 2.22).
"Computed on `g`" is the predicate `MMP.Mori.IsNumericalDiscrepancy sX g K Δ E q`, which contains
that `g` is a resolution, that `K` is a canonical divisor of `Y`, and that `E` is a
`g`-exceptional curve. "Terminal near `x`" is `MMP.Mori.IsAt` applied to
`MMP.Mori.IsTerminalPair`, with an explicit canonical divisor `K` of `X`. The neighbourhood on
which `mult_p Δ ≤ mult_x Δ` comes from the upper semicontinuity of the order of an ideal on a
smooth scheme in characteristic zero (`MMP.Resolution.isClosed_setOf_le_multAt`), applied to the
ideal sheaf of each component of `Δ`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Notation 4.1, 2.22,
  2.45, Theorem 4.5.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Mori

section MinimalResolution

universe u

/-- A normal surface `X` over an algebraically closed field `k` has a minimal resolution
`f : Y ⟶ X` such that every resolution `g : Y' ⟶ X` factors uniquely as `g = h ≫ f`. -/
@[mmp "lem_mmp_foundation_km_surface_minimal_resolution_universal"]
public theorem exists_isMinimalSurfaceResolution_existsUnique_comp_eq
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : QuasiCompact (f ≫ sX)) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y), IsMinimalSurfaceResolution sX f ∧
        ∀ (Y' : Scheme.{u}) (g : Y' ⟶ X), IsSmoothResolution sX g → ∃! h : Y' ⟶ Y, h ≫ f = g := by
  obtain ⟨Y, f, -, -, ⟨_, _, _, hf⟩, -⟩ := exists_isMinimalSurfaceResolution sX hX hdim
  exact ⟨Y, f, ‹_›, ‹_›, ‹_›, hf,
    (IsMinimalSurfaceResolution.existsUnique_comp_eq sX f hX hdim hf).1⟩

end MinimalResolution

section DivisorOverPoint

universe u

/-- A point of coheight at least two on a scheme of dimension two is closed. -/
theorem isClosed_singleton_of_two_le_coheight {X : Scheme.{u}}
    (hdim : topologicalKrullDim X = 2) {x : X} (hx : 2 ≤ Order.coheight x) :
    IsClosed ({x} : Set X) := by
  have hkd : Order.krullDim X = 2 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hyx : y ≤ x := Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hy)
  by_contra hne
  have hxy : ¬ x ≤ y := fun h =>
    hne ((Scheme.le_iff_specializes.mp h).antisymm (specializes_iff_mem_closure.mpr hy)).eq
  have h2 : Order.coheight y ≤ 2 := by
    have := Order.coheight_le_krullDim y
    rw [hkd] at this
    exact WithBot.coe_le_coe.mp this
  have : (2 : ℕ∞) + 1 ≤ 2 :=
    (add_le_add_left hx 1).trans ((Order.coheight_add_one_le (hyx.lt_of_not_ge hxy)).trans h2)
  exact absurd this (by decide)

/-- A dominant morphism of integral schemes inducing a surjection of function fields is an
isomorphism on the local ring at every point whose image has a valuation ring as local ring. -/
private theorem bijective_stalkMap_of_valuationRing {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (ν : Z ⟶ Y) [IsDominant ν] (hν : Function.Surjective (functionFieldMap ν))
    (z : Z) [ValuationRing (Y.presheaf.stalk (ν z))] : Function.Bijective (ν.stalkMap z) := by
  set φ := (ν.stalkMap z).hom
  have hsq : ∀ a, algebraMap _ Z.functionField (φ a) =
      functionFieldMap ν (algebraMap _ Y.functionField a) := fun a =>
    (MMP.Mori.functionFieldMap_algebraMap_stalk ν z a).symm
  have hinj : Function.Injective φ := by
    intro a b hab
    apply IsFractionRing.injective (Y.presheaf.stalk (ν z)) Y.functionField
    apply (functionFieldMap ν).injective
    rw [← hsq, ← hsq, hab]
  refine ⟨hinj, fun b => ?_⟩
  obtain ⟨r, hr⟩ := hν (algebraMap _ Z.functionField b)
  by_cases hr0 : r = 0
  · refine ⟨0, IsFractionRing.injective (Z.presheaf.stalk z) Z.functionField ?_⟩
    rw [map_zero, map_zero, ← hr, hr0, map_zero]
  rcases ValuationRing.isInteger_or_isInteger (Y.presheaf.stalk (ν z)) r with ⟨a, ha⟩ | ⟨c, hc⟩
  · refine ⟨a, IsFractionRing.injective (Z.presheaf.stalk z) Z.functionField ?_⟩
    rw [hsq, ha, hr]
  · have h1 : φ c * b = 1 := by
      apply IsFractionRing.injective (Z.presheaf.stalk z) Z.functionField
      rw [map_mul, hsq, hc, ← hr, ← map_mul, inv_mul_cancel₀ hr0, map_one, map_one]
    have hcu : IsUnit c := (isUnit_map_iff φ c).mp (IsUnit.of_mul_eq_one _ h1)
    obtain ⟨d, hd⟩ := hcu.exists_left_inv
    refine ⟨d, ?_⟩
    calc φ d = φ d * (φ c * b) := by rw [h1, mul_one]
      _ = b := by rw [← mul_assoc, ← map_mul, hd, map_one, one_mul]

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    MMP.Mori.IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : MMP.Mori.IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have he' : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- Along a morphism `q` with bijective local ring map at `y`, a rational function on the target
is regular at `z = q(y)` exactly when its pull-back is regular at `y`. -/
private theorem functionFieldMap_mem_range_iff {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (q : Y ⟶ Z) [IsDominant q] (y : Y) (hb : Function.Bijective (q.stalkMap y))
    {z : Z} (hz : q y = z) (s : Z.functionField) :
    functionFieldMap q s ∈ (algebraMap (Y.presheaf.stalk y) Y.functionField).range ↔
      s ∈ (algebraMap (Z.presheaf.stalk z) Z.functionField).range := by
  subst hz
  constructor
  · rintro ⟨b, hb'⟩
    obtain ⟨a, rfl⟩ := hb.2 b
    refine ⟨a, (functionFieldMap q).injective ?_⟩
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk, hb']
  · rintro ⟨a, rfl⟩
    exact ⟨(q.stalkMap y).hom a, (MMP.Mori.functionFieldMap_algebraMap_stalk q y a).symm⟩

/-- A composite of birational morphisms out of an irreducible scheme is birational. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : MMP.Mori.IsBirationalMorphism f)
    (hg : MMP.Mori.IsBirationalMorphism g) : MMP.Mori.IsBirationalMorphism (f ≫ g) := by
  haveI := hf.isDominant
  haveI := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    haveI : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hU : Dense (U : Set X) := U.2.dense hne
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have hle₁ : U ≤ U₁ := inf_le_left
  have hres : IsOpenImmersion (f.resLE U₂ U hle) := by
    have : f.resLE U₂ U hle ≫ U₂.ι = X.homOfLE hle₁ ≫ (U₁.ι ≫ f) := by
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]
    have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by rw [this]; infer_instance
    exact IsOpenImmersion.of_comp _ U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U hU

/-- If `t` is an open immersion of a nonempty scheme into an irreducible one and `t ≫ g` is
birational, then `g` is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {X Y Z : Scheme.{u}}
    [Nonempty X] [IrreducibleSpace Y] (t : X ⟶ Y) [IsOpenImmersion t] (g : Y ⟶ Z)
    (h : MMP.Mori.IsBirationalMorphism (t ≫ g)) : MMP.Mori.IsBirationalMorphism g := by
  have := h.isDominant
  have : IsDominant g := IsDominant.of_comp t g
  obtain ⟨W, ⟨w, hw⟩, hWo⟩ := h.exists_isOpenImmersion
  have : IsOpenImmersion ((t ''ᵁ W).ι ≫ g) := by
    rw [← Scheme.Hom.isoImage_inv_ι_assoc]; infer_instance
  exact isBirationalMorphism_of_isOpenImmersion g _ ((t ''ᵁ W).2.dense ⟨t w, w, hw, rfl⟩)

/-- For a divisor `(Y₁, f₁, E₁)` over a variety `X`, the morphism `f₁` factors as an open
immersion followed by a proper morphism from a normal variety: Nagata's compactification of
`f₁`, normalized in `Y₁`. -/
private theorem exists_isOpenImmersion_comp_isProper_eq {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] (hX : MMP.Mori.IsVariety k sX)
    (D : MMP.Mori.DivisorOver k sX) :
    ∃ (Z : Scheme.{u}) (t : D.Y ⟶ Z) (g : Z ⟶ X), IsOpenImmersion t ∧ IsProper g ∧
      t ≫ g = D.f ∧ MMP.Mori.IsNormalVariety k (g ≫ sX) := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have hYv := D.isNormalVariety.1
  have : IsSeparated sX := hX.toIsSeparated
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.toQuasiCompact
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsSeparated (D.f ≫ sX) := hYv.toIsSeparated
  have : LocallyOfFiniteType (D.f ≫ sX) := hYv.toLocallyOfFiniteType
  have : QuasiCompact (D.f ≫ sX) := hYv.toQuasiCompact
  have : IsSeparated D.f := IsSeparated.of_comp D.f sX
  have : LocallyOfFiniteType D.f := locallyOfFiniteType_of_comp D.f sX
  have : QuasiCompact D.f := QuasiCompact.of_comp D.f sX
  have : IsNoetherian X := {}
  obtain ⟨c, hc⟩ : ∃ c : CompactificationOf (Over.mk D.f), QuasiCompact c.immersion :=
    hasCompactification_of_compactSpace_quasiSeparatedSpace D.f
  set P := c.space
  set j : D.Y ⟶ P := c.immersion
  set p : P ⟶ X := c.toBase
  have hjp : j ≫ p = D.f := Over.w c.obj.hom
  have : IsSeparated j := by
    have : IsSeparated (j ≫ p) := by rw [hjp]; infer_instance
    exact IsSeparated.of_comp j p
  have : QuasiCompact j := hc
  have : QuasiSeparated j := IsSeparated.instQuasiSeparated j
  -- the normalization of `P` in `Y₁` is normal, finite over `P`, and contains `Y₁` as an open
  have ht : IsOpenImmersion (Scheme.Hom.toNormalization j) := by
    have : IsOpenImmersion ((Limits.pullback.snd j j).toNormalization ≫
        j.normalizationPullback j ≫ Limits.pullback.fst _ _) := inferInstance
    rw [Scheme.Hom.toNormalization_normalizationPullback_fst j j] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
      (Limits.pullback.fst j j) _).mp this
  have hnorm : IsNormal (Scheme.Hom.normalization j) :=
    AlgebraicGeometry.isNormal_normalization j fun V hV => by
      have : IsNoetherian V :=
        { toIsLocallyNoetherian := inferInstance
          toCompactSpace := isCompact_iff_compactSpace.mp hV }
      exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hfin : IsFinite (Scheme.Hom.fromNormalization j) :=
    isFinite_fromNormalization_of_locallyOfFiniteType j
      (isNagataScheme_of_locallyOfFiniteType_over_field k (p ≫ sX))
  refine ⟨_, j.toNormalization, j.fromNormalization ≫ p, ht, inferInstance, by
    simp only [Scheme.Hom.toNormalization_fromNormalization_assoc, hjp],
    ⟨(MMP.Mori.isVariety_iff k _).2 ⟨inferInstance, inferInstance, inferInstance,
      inferInstance⟩, hnorm⟩⟩

/-- **KM 2.22 for `g = 𝟙`.** Every divisor over a variety `X` has the valuation of a divisor
`(Z, g, F)` over `X` with `g` proper. -/
private theorem exists_isProper_valuation_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (hX : MMP.Mori.IsVariety k sX)
    (D : MMP.Mori.DivisorOver k sX) :
    ∃ D₁ : MMP.Mori.DivisorOver k sX, IsProper D₁.f ∧ D₁.valuation = D.valuation := by
  obtain ⟨Z, t, g, ht, hg, htg, hgv⟩ := exists_isOpenImmersion_comp_isProper_eq hX D
  have := D.isIntegral
  have := hgv.1.toIsIntegral
  let D₁ : MMP.Mori.DivisorOver k sX := ⟨Z, g, hgv,
    isBirationalMorphism_of_isOpenImmersion_comp t g (htg ▸ D.isBirationalMorphism),
    OpenWeilRestriction.primeDivisorMap t D.E⟩
  refine ⟨D₁, hg, (MMP.Positivity.DivisorOver.valuation_eq_of_iso D D₁ ⊤
    t.opensRange trivial ⟨D.E.genericPoint, ?_⟩ (D.Y.topIso ≪≫ t.isoOpensRange) ?_ ?_).symm⟩
  · exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm
  · simp [D₁, htg]
  · apply Subtype.ext
    change (D.Y.topIso.hom ≫ t.isoOpensRange.hom ≫ t.opensRange.ι) ⟨D.E.genericPoint, trivial⟩ =
      _
    rw [Scheme.Hom.isoOpensRange_hom_ι]
    exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm

/-- The image `f(η_E)` of the generic point of an exceptional divisor `(Y, f, E)` over `X` has
coheight at least two. -/
private theorem two_le_coheight_of_isExceptional {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {D : MMP.Mori.DivisorOver k sX} (hD : D.IsExceptional) :
    2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have hdef : MMP.Mori.RationalMap.DefinedAt (X := D.Y) D.f.toRationalMap D.E.genericPoint := by
    rw [MMP.Mori.RationalMap.DefinedAt, MMP.Mori.RationalMap.dom_toRationalMap_hom]
    trivial
  have h2 := (MMP.Mori.RationalMap.isExceptional_iff.mp hD) hdef
  set T := MMP.Mori.RationalMap.transform (X := D.Y) D.f.toRationalMap D.E.idealSheaf.support
  have hmem : D.f D.E.genericPoint ∈ (T : Set X) := by
    refine MMP.Mori.RationalMap.image_subset_transform D.f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨D.E.genericPoint, ?_, rfl⟩
    change D.E.genericPoint ∈ D.E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hsub : ((irreducibleSetEquivPoints (α := X)).symm (D.f D.E.genericPoint) : Set X) ⊆ T :=
    T.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
  have := MMP.Mori.le_closedsCodimension_iff.mp h2 _ hsub
  rwa [codimension_eq_coheight, Order.coheight_orderIso] at this

/-- Let `X` be a surface over an algebraically closed field `k` and `D = (Y₁, f₁, E₁)` a divisor
over `X` which is exceptional over `X`. Then there is a divisor `(Y, f, E)` over `X` with the same
valuation of `k(X)`, such that `f : Y ⟶ X` is a resolution and `E` is an `f`-exceptional curve. -/
@[mmp "lem_km4a_divisor_over_point_on_resolution"]
public theorem DivisorOver.IsExceptional.exists_isSmoothResolution_isExceptionalCurve
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : IsVariety k sX) (hdim : topologicalKrullDim X = 2)
    {D : DivisorOver k sX} (hD : D.IsExceptional) :
    haveI : IsIntegral X := hX.toIsIntegral
    ∃ D' : DivisorOver k sX, IsSmoothResolution sX D'.f ∧
      IsExceptionalCurve D'.f D'.E.idealSheaf ∧ D'.valuation = D.valuation := by
  haveI : IsIntegral X := hX.toIsIntegral
  -- the center `x = f₁(η_{E₁})` is a closed point
  have hxc : IsClosed ({D.f D.E.genericPoint} : Set X) :=
    isClosed_singleton_of_two_le_coheight hdim (two_le_coheight_of_isExceptional hD)
  -- a proper normal model `(Z, g, F)` with the valuation of `E₁`
  obtain ⟨D₁, hp₁, hv₁⟩ := exists_isProper_valuation_eq hX D
  have := D₁.isIntegral
  have := D₁.isNormal
  have := D₁.isLocallyNoetherian
  have := D₁.isDominant
  have hZv := D₁.isNormalVariety
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D₁.f ≫ sX) := hZv.1.toLocallyOfFiniteType
  have hZd : topologicalKrullDim D₁.Y = 2 := by
    rw [← hdim, ← MMP.Mori.toENat_trdeg_functionField (sX := D₁.f ≫ sX),
      ← MMP.Mori.toENat_trdeg_functionField (sX := sX),
      MMP.Mori.trdeg_functionField_eq_of_bijective _ D₁.f
        D₁.isBirationalMorphism.functionFieldMap_bijective]
  -- the minimal resolution `q : Y ⟶ Z`
  obtain ⟨Y, q, hYv, hYd, ⟨_, _, _, hq⟩, -⟩ :=
    MMP.Mori.exists_isMinimalSurfaceResolution (D₁.f ≫ sX) hZv hZd
  have hqr := hq.1
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsProper q := hqr.isProper
  have : IsProper D₁.f := hp₁
  have hqb := hqr.isBirationalMorphism
  have : IsDominant q := hqb.isDominant
  have hfb : MMP.Mori.IsBirationalMorphism (q ≫ D₁.f) :=
    isBirationalMorphism_comp hqb D₁.isBirationalMorphism
  have hYv' : MMP.Mori.IsVariety k ((q ≫ D₁.f) ≫ sX) := by rw [Category.assoc]; exact hYv
  have hfv : MMP.Mori.IsNormalVariety k ((q ≫ D₁.f) ≫ sX) := ⟨hYv', inferInstance⟩
  -- a point `y` over `η_F`; its local ring is `𝒪_{Z,F}`
  obtain ⟨y, hy⟩ := q.surjective D₁.E.genericPoint
  haveI : IsDiscreteValuationRing (D₁.Y.presheaf.stalk (q y)) :=
    hy ▸ D₁.E.isDiscreteValuationRing_localRing
  have hbs := bijective_stalkMap_of_valuationRing q hqb.functionFieldMap_bijective.2 y
  have hcoh : Order.coheight y = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight y
    have h2 := ringKrullDim_stalk_eq_coheight (q y)
    rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hbs), h2, hy,
      D₁.E.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  set E' : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hcoh
  have hE' : E'.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hcoh
  let D' : MMP.Mori.DivisorOver k sX := ⟨Y, q ≫ D₁.f, hfv, hfb, E'⟩
  have hfy : (q ≫ D₁.f) y = D.f D.E.genericPoint := by
    rw [Scheme.Hom.comp_apply, hy]
    exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX hv₁
  refine ⟨D', ⟨inferInstance, hfb, ?_⟩, ⟨?_, D.f D.E.genericPoint, ?_⟩, ?_⟩
  · change MMP.Mori.IsSmoothScheme ((q ≫ D₁.f) ≫ sX)
    rw [Category.assoc]
    exact hqr.isSmoothScheme
  · exact MMP.Flips.isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv' hYd E'
  · change (q ≫ D₁.f).base '' E'.support = _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      show AlgebraicGeometry.PrimeDivisor.genericPoint E' = y from hE']
    refine Set.Subset.antisymm ?_ ?_
    · refine (image_closure_subset_closure_image (q ≫ D₁.f).continuous).trans ?_
      rw [Set.image_singleton]
      change closure {(q ≫ D₁.f) y} ⊆ _
      rw [hfy, hxc.closure_eq]
    · rw [Set.singleton_subset_iff, ← hfy]
      exact ⟨y, subset_closure rfl, rfl⟩
  · rw [← hv₁]
    refine MMP.Positivity.DivisorOver.valuation_eq_of_forall_le_one_iff D' D₁ fun t => ?_
    change E'.divisorialValuation (functionFieldMap (q ≫ D₁.f) t) ≤ 1 ↔
      D₁.E.divisorialValuation (functionFieldMap D₁.f t) ≤ 1
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
      MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply q D₁.f]
    rw [← hE'] at hbs hy
    exact functionFieldMap_mem_range_iff q _ hbs hy _

end DivisorOverPoint

section DiscrepancyBound

universe u
universe w

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Multiplicities and transforms -/

section Multiplicity

variable {X : Scheme.{w}}

/-- The multiplicity at a point is additive: `mult_x (∑ Dᵢ) = ∑ mult_x Dᵢ`. -/
private lemma multiplicityAt_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → MMP.Mori.QDivisor X) (x : X) :
    (∑ i ∈ s, f i).multiplicityAt x = ∑ i ∈ s, (f i).multiplicityAt x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MMP.Mori.DivisorWithCoeffs.multiplicityAt]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      MMP.Mori.DivisorWithCoeffs.multiplicityAt_add, ih]

/-- The multiplicity of an effective `ℚ`-divisor is nonnegative. -/
private lemma multiplicityAt_nonneg {D : MMP.Mori.QDivisor X} (hD : 0 ≤ D) (x : X) :
    0 ≤ D.multiplicityAt x :=
  Finset.sum_nonneg fun P _ => nsmul_nonneg (hD P) _

/-- `mult_x (D - D') = mult_x D - mult_x D'`. -/
private lemma multiplicityAt_sub (D D' : MMP.Mori.QDivisor X) (x : X) :
    (D - D').multiplicityAt x = D.multiplicityAt x - D'.multiplicityAt x := by
  rw [eq_sub_iff_add_eq, ← MMP.Mori.DivisorWithCoeffs.multiplicityAt_add, sub_add_cancel]

end Multiplicity

/-! ### Transforms of prime divisors -/

section Transform

variable {X Y : Scheme.{w}}

/-- The transform of an effective divisor is effective. -/
private lemma inverseTransformDivisor_nonneg (g : Y ⟶ X) {D : MMP.Mori.QDivisor X}
    (hD : 0 ≤ D) : 0 ≤ inverseTransformDivisor g D := by
  intro E
  rw [MMP.Mori.inverseTransformDivisor, MMP.Mori.DivisorWithCoeffs.mapPrimeDivisors,
    Finsupp.liftAddHom_apply, Finsupp.sum_apply]
  classical
  refine Finset.sum_nonneg fun P _ => ?_
  rcases hφ : inverseTransformPrimeDivisor g P with _ | E'
  · simp [hφ]
  · simp only [hφ, Option.elim_some, Finsupp.singleAddHom_apply, Finsupp.single_apply]
    split_ifs
    · exact hD P
    · exact le_rfl

/-- If `g⁻¹_* P = E`, the coefficient of `g⁻¹_* D` at `E` is the coefficient of `D` at `P`. -/
private lemma inverseTransformDivisor_apply_of_eq_some {g : Y ⟶ X}
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : inverseTransformPrimeDivisor g P = some E) (D : MMP.Mori.QDivisor X) :
    inverseTransformDivisor g D E = D P := by
  classical
  have hinj : ∀ P', inverseTransformPrimeDivisor g P' = some E → P' = P := fun P' hP' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hP').1).symm.trans
        (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some h).1)
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, h₁, h₂]
  | single P' r =>
    rw [MMP.Mori.inverseTransformDivisor_single]
    rcases hP' : inverseTransformPrimeDivisor g P' with _ | E'
    · rw [Option.elim_none, Finsupp.zero_apply, Finsupp.single_apply, if_neg]
      rintro rfl
      rw [h] at hP'
      cases hP'
    · simp only [Option.elim_some]
      by_cases hE : E' = E
      · subst hE
        obtain rfl := hinj P' hP'
        simp
      · rw [Finsupp.single_apply, if_neg hE, Finsupp.single_apply, if_neg]
        rintro rfl
        rw [h] at hP'
        exact hE (Option.some.inj hP').symm

/-- A prime divisor which is the transform of no prime divisor has coefficient `0` in every
transform. -/
private lemma inverseTransformDivisor_apply_eq_zero {g : Y ⟶ X} {E : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P, inverseTransformPrimeDivisor g P ≠ some E) (D : MMP.Mori.QDivisor X) :
    inverseTransformDivisor g D E = 0 := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ => rw [map_add, Finsupp.add_apply, h₁, h₂, add_zero]
  | single P' r =>
    rw [MMP.Mori.inverseTransformDivisor_single]
    rcases hP' : inverseTransformPrimeDivisor g P' with _ | E'
    · simp
    · simp only [Option.elim_some]
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact h P' hP'

/-- The inverse transform under the identity is the identity: `(𝟙_X)⁻¹_* D = D`. -/
private lemma inverseTransformDivisor_id (D : MMP.Mori.QDivisor X) :
    inverseTransformDivisor (𝟙 X) D = D := by
  ext P
  exact inverseTransformDivisor_apply_of_eq_some
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint rfl
      (MMP.Mori.le_biregularLocus (V := ⊤) ((MMP.Mori.isBiregular_top_iff _).mpr inferInstance)
        trivial)) D

end Transform

/-! ### Multiplicities where a morphism is a local isomorphism -/

section LocalIso

variable {X Y : Scheme.{w}}

/-- If `J.comap f ≤ I`, the stalk of `J` at `f q` maps into the stalk of `I` at `q`. -/
private lemma map_stalkIdeal_le (f : Y ⟶ X) [QuasiCompact f] {I : Y.IdealSheafData}
    {J : X.IdealSheafData} (hIJ : J.comap f ≤ I) (q : Y) :
    (J.stalkIdeal (f q)).map (f.stalkMap q).hom ≤ I.stalkIdeal q := by
  have hJ : J ≤ I.map f := Scheme.IdealSheafData.le_map_iff_comap_le.mpr hIJ
  refine Ideal.map_le_iff_le_comap.mpr (iSup_le fun U => Ideal.map_le_iff_le_comap.mpr
    fun a ha => ?_)
  simp only [Ideal.mem_comap]
  rw [Scheme.Hom.germ_stalkMap_apply]
  by_cases hq : q ∈ I.support
  · let z : I.subscheme := ⟨q, hq⟩
    have hker := I.ker_stalkMap_subschemeι z
    change _ = I.stalkIdeal q at hker
    rw [← hker]
    refine RingHom.mem_ker.mpr ?_
    erw [Scheme.Hom.germ_stalkMap_apply I.subschemeι (f ⁻¹ᵁ U.1.1) z]
    have h0 : ((I.subschemeι ≫ f).app U.1.1).hom a = 0 := by
      have := hJ U.1 ha
      rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker] at this
      exact this
    have h0' : (I.subschemeι.app (f ⁻¹ᵁ U.1.1)).hom ((f.app U.1.1).hom a) = 0 := h0
    erw [h0', map_zero]
  · rw [I.stalkIdeal_eq_top_of_notMem_support hq]
    trivial

/-- Where the stalk map of `f` is an isomorphism, the multiplicity of the transform of a prime
divisor is at most that of the prime divisor. -/
private lemma multiplicityAt_le_of_isIso_stalkMap (f : Y ⟶ X) [QuasiCompact f] {q : Y}
    [IsIso (f.stalkMap q)] {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : inverseTransformPrimeDivisor f P = some E) :
    E.multiplicityAt q ≤ P.multiplicityAt (f q) := by
  have hPE : P.idealSheaf.comap f ≤ E.idealSheaf := by
    rw [(MMP.Mori.inverseTransformPrimeDivisor_eq_some_iff.mp h).2, MMP.Mori.inverseTransformIdeal,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
      Scheme.IdealSheafData.support_comap]
    intro y hy
    exact closure_minimal (fun x hx => hx.1)
      (P.idealSheaf.support.isClosed.preimage f.continuous) hy
  have hmap := map_stalkIdeal_le f hPE q
  have hbij : Function.Bijective (f.stalkMap q).hom :=
    ConcreteCategory.bijective_of_isIso (f.stalkMap q)
  have hm := IsLocalRing.map_maximalIdeal_of_surjective (f.stalkMap q).hom hbij.2
  refine iSup₂_le fun k hk => le_iSup₂_of_le k ?_ le_rfl
  intro x hx
  have h1 : (f.stalkMap q).hom x ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk q) ^ k :=
    hk (hmap (Ideal.mem_map_of_mem _ hx))
  rw [← Ideal.comap_map_of_bijective _ hbij (I := IsLocalRing.maximalIdeal _ ^ k),
    Ideal.map_pow, hm]
  exact h1

/-- Where the stalk map of `f` is an isomorphism, `mult_q (f⁻¹_* D) ≤ mult_{f q} D` for an
effective `D` on a smooth `X`. -/
private lemma multiplicityAt_inverseTransformDivisor_le_of_isIso_stalkMap {k : Type w} [Field k]
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]
    (hXs : MMP.Mori.IsSmoothScheme sX) (f : Y ⟶ X) [QuasiCompact f] {q : Y}
    [IsIso (f.stalkMap q)] {D : MMP.Mori.QDivisor X} (hD : 0 ≤ D) :
    (inverseTransformDivisor f D).multiplicityAt q ≤ D.multiplicityAt (f q) := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, multiplicityAt_finset_sum, MMP.Mori.DivisorWithCoeffs.multiplicityAt,
    Finsupp.sum]
  refine Finset.sum_le_sum fun P _ => ?_
  rw [MMP.Mori.inverseTransformDivisor_single]
  rcases hP : inverseTransformPrimeDivisor f P with _ | E
  · simp only [Option.elim_none, MMP.Mori.DivisorWithCoeffs.multiplicityAt,
      Finsupp.sum_zero_index]
    exact nsmul_nonneg (hD P) _
  · simp only [Option.elim_some]
    rw [MMP.Mori.DivisorWithCoeffs.multiplicityAt_single]
    exact nsmul_le_nsmul_left (hD P) (ENat.toNat_le_toNat
      (multiplicityAt_le_of_isIso_stalkMap f hP)
      (MMP.Threefold.Resolution.multiplicityAt_ne_top P
        (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hXs P)
        (f q)))

end LocalIso

/-! ### Resolutions of a smooth surface -/

section Resolution

variable {k : Type w} [Field k] {X Y : Scheme.{w}} {sX : X ⟶ Spec (.of k)}

/-- A morphism injective on points contracts no curve. -/
private lemma not_isExceptionalCurve_of_injective {f : Y ⟶ X} (hf : Function.Injective f.base)
    (C : Y.IdealSheafData) : ¬ IsExceptionalCurve f C := by
  rintro ⟨hC, x, hx⟩
  refine hC.not_subsingleton fun y hy z hz => hf ?_
  have hy' : f.base y ∈ f.base '' (C.support : Set Y) := ⟨y, hy, rfl⟩
  have hz' : f.base z ∈ f.base '' (C.support : Set Y) := ⟨z, hz, rfl⟩
  rw [hx] at hy' hz'
  exact hy'.trans hz'.symm

/-- An exceptional curve of a resolution of a normal surface is a prime divisor. -/
private lemma exists_primeDivisor_idealSheaf_eq (hX : MMP.Mori.IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {f : Y ⟶ X} (hf : IsSmoothResolution sX f)
    {E : Y.IdealSheafData} (hE : IsExceptionalCurve f E) :
    ∃ P : MMP.Mori.PrimeDivisor Y, P.idealSheaf = E := by
  have hY := hf.isNormalVariety hX
  have hv := hY.1.1
  have : IsIntegral Y := hv.toIsIntegral
  have : LocallyOfFiniteType (f ≫ sX) := hv.toLocallyOfFiniteType
  have := hE.1.1
  have hcl : closure ({E.subschemeι (genericPoint E.subscheme)} : Set Y) =
      (E.support : Set Y) := by
    have h1 := (genericPoint_spec E.subscheme).image E.subschemeι.continuous
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
      E.support.isClosed.closure_eq] at h1
    exact h1
  have hd : topologicalKrullDim (E.support : Set Y) = 1 := by
    rw [← MMP.Mori.topologicalKrullDim_subscheme_eq]
    exact hE.1.2
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (f ≫ sX)
    (E.subschemeι (genericPoint E.subscheme))
  rw [hcl, hd, hY.2.1, hdim] at h
  refine ⟨⟨E, hE.1.1, ?_⟩, rfl⟩
  rw [MMP.Flips.codimension_closureSingleton]
  generalize Order.coheight (E.subschemeι (genericPoint E.subscheme)) = c at h ⊢
  induction c using ENat.recTopCoe with
  | top => exact absurd h (by decide)
  | coe c =>
    have h' : ((1 + c : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) :=
      WithBot.coe_injective (by push_cast; exact h)
    have : c = 1 := by have := Nat.cast_injective h'; omega
    subst this
    rfl

/-- The generic point of a prime divisor of a normal surface lies in the biregular locus of a
resolution. -/
private lemma genericPoint_mem_biregularLocus [IsAlgClosed k] (hX : MMP.Mori.IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {f : Y ⟶ X} (hf : IsSmoothResolution sX f)
    (D : MMP.Mori.PrimeDivisor X) : D.genericPoint ∈ MMP.Mori.biregularLocus f := by
  obtain ⟨S, -, hScl, ⟨hS, hiso⟩, -⟩ :=
    MMP.Mori.exists_finite_isIso_and_isExceptionalCurve_iff hX hdim hf
  refine MMP.Mori.le_biregularLocus (V := ⟨Sᶜ, hS⟩) hiso ?_
  intro hDS
  have h1 := D.coheight_genericPoint
  rw [MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hX.1 hdim (hScl _ hDS)] at h1
  exact absurd h1 (by decide)

/-- On a surface, the generic point of a prime divisor is not a closed point. -/
private lemma genericPoint_ne_of_isClosed [IsAlgClosed k] {W : Scheme.{w}}
    {sW : W ⟶ Spec (.of k)} (hW : MMP.Mori.IsVariety k sW) (hWd : topologicalKrullDim W = 2)
    (P : MMP.Mori.PrimeDivisor W) {w : W} (hw : IsClosed ({w} : Set W)) :
    P.genericPoint ≠ w := fun h => by
  have h1 := P.coheight_genericPoint
  rw [h, MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hW hWd hw] at h1
  exact absurd h1 (by decide)

/-- **Transforms along a resolution followed by a point blow-up**:
`(h ∘ π)⁻¹_* D = π⁻¹_* (h⁻¹_* D)`. -/
private lemma inverseTransformDivisor_blowUpToBase_comp [IsAlgClosed k]
    (hX : MMP.Mori.IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2) {W : Scheme.{w}}
    {h : W ⟶ X} (hh : IsSmoothResolution sX h) {w : W} (hw : IsClosed ({w} : Set W))
    (hcomp : IsSmoothResolution sX
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h))
    (D : MMP.Mori.QDivisor X) :
    inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) D =
      inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
        (inverseTransformDivisor h D) := by
  obtain ⟨hWv, hWd, -⟩ := hh.isNormalVariety hX
  have hprime : ∀ P : MMP.Mori.PrimeDivisor X,
      inverseTransformPrimeDivisor
          (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) P =
        (inverseTransformPrimeDivisor h P).bind (inverseTransformPrimeDivisor
          (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))) := by
    intro P
    obtain ⟨P₁, h₁, hη₁⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P
      (genericPoint_mem_biregularLocus hX hdim hh P)
    obtain ⟨P₂, h₂, hη₂⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P₁
      (MMP.Threefold.Resolution.mem_biregularLocus_blowUpToBase_singleton hw
        (genericPoint_ne_of_isClosed hWv.1 (hWd.trans hdim) P₁ hw))
    rw [h₁, Option.bind_some, h₂]
    have hη : (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h)
        P₂.genericPoint = P.genericPoint := by
      rw [Scheme.Hom.comp_apply, hη₂, hη₁]
    exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη
      (hη ▸ genericPoint_mem_biregularLocus hX hdim hcomp P)
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add B₁ B₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | single P r =>
    rw [MMP.Mori.inverseTransformDivisor_single, MMP.Mori.inverseTransformDivisor_single,
      hprime P]
    rcases inverseTransformPrimeDivisor h P with _ | P₁
    · simp
    · simp only [Option.bind_some, Option.elim_some]
      rw [MMP.Mori.inverseTransformDivisor_single]

/-- **Blowing up a closed point keeps a multiplicity bound.** If an effective `ℚ`-divisor `D` on a
smooth surface `W` has `mult_q D ≤ μ` at every closed point `q`, then so does its transform on the
blow-up of a closed point `w`, at every closed point. -/
private lemma multiplicityAt_inverseTransformDivisor_blowUpToBase_le_of_forall [IsAlgClosed k]
    {W : Scheme.{w}} {sW : W ⟶ Spec (.of k)} (hW : MMP.Mori.IsVariety k sW)
    (hWs : MMP.Mori.IsSmoothScheme sW) (hWd : topologicalKrullDim W = 2) {w : W}
    (hw : IsClosed ({w} : Set W))
    {F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
    {D : MMP.Mori.QDivisor W} (hD : 0 ≤ D) {μ : ℚ}
    (hmult : ∀ q : W, IsClosed ({q} : Set W) → D.multiplicityAt q ≤ μ)
    {x : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)} (hx : IsClosed ({x} : Set _)) :
    (inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
      D).multiplicityAt x ≤ μ := by
  by_cases hxF : x ∈ F.support
  · exact (MMP.Threefold.Resolution.multiplicityAt_inverseTransformDivisor_blowUpToBase_le
      hW hWs hWd hw hF hD hxF).trans (hmult w hw)
  have : Smooth sW := (MMP.Mori.isSmoothScheme_iff _).mp hWs
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs
  obtain ⟨-, -, -, _, -, _, F', hF', hFsupp, -⟩ :=
    MMP.Threefold.Resolution.isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve
      sW hW hWd hw
  obtain rfl : F' = F := MMP.Mori.PrimeDivisor.ext_idealSheaf (hF'.trans hF.symm)
  have hxw : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) x ≠ w := fun h' =>
    hxF (by rw [hFsupp]; exact h')
  have := AlgebraicGeometry.isIso_stalkMap_of_isIso_morphismRestrict _
    (U := (⟨{w}ᶜ, hw.isOpen_compl⟩ : W.Opens)) inferInstance hxw
  have hcl := (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)).isClosedMap _ hx
  rw [Set.image_singleton] at hcl
  exact (multiplicityAt_inverseTransformDivisor_le_of_isIso_stalkMap hWs _ hD).trans
    (hmult _ hcl)

end Resolution

/-- The base case of `exists_solution_of_pointBlowupChain`: on the identity of a smooth surface,
`0` solves the numerical pull-back equations, and `𝟙⁻¹_* Δ = Δ` keeps `mult_q ≤ μ`. -/
private theorem exists_solution_id {k : Type w} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{w}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX)
    (hXs : MMP.Mori.IsSmoothScheme sX) (hdim : topologicalKrullDim X = 2)
    {Δ : MMP.Mori.QDivisor X} {μ : ℚ}
    (hmult : ∀ p : X, IsClosed ({p} : Set X) → Δ.multiplicityAt p ≤ μ) :
    ∃ (_ : QuasiCompact (𝟙 X ≫ sX)) (_ : IsLocallyNoetherian X) (_ : IsNormal X)
      (K : MMP.Mori.Divisor X) (a : MMP.Mori.QDivisor X),
      IsNumericalPullbackSolution sX (𝟙 X) K Δ a ∧
      (∀ E : MMP.Mori.PrimeDivisor X, IsExceptionalCurve (𝟙 X) E.idealSheaf → 1 - μ ≤ a E) ∧
      ∀ q : X, IsClosed ({q} : Set X) →
        (inverseTransformDivisor (𝟙 X) Δ).multiplicityAt q ≤ μ := by
  have : IsIntegral X := hX.toIsIntegral
  obtain ⟨hXl, hXN⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hXs
  have : QuasiCompact sX := hX.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hs : MMP.Mori.IsSmoothScheme (𝟙 X ≫ sX) := by rwa [Category.id_comp]
  have : AlgebraicGeometry.IsVariety k (𝟙 X ≫ sX) := by rwa [Category.id_comp]
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (𝟙 X ≫ sX) hs
    (n := 2) (by rw [hdim]; rfl)
  have hnex : ∀ C : X.IdealSheafData, ¬ IsExceptionalCurve (𝟙 X) C :=
    not_isExceptionalCurve_of_injective (Scheme.Hom.isOpenEmbedding (𝟙 X)).injective
  refine ⟨by rw [Category.id_comp]; infer_instance, hXl, hXN, K, 0,
    ⟨⟨inferInstance, MMP.Mori.isBirationalMorphism_of_isIso _, hs⟩, ⟨2, hK⟩, by simp,
      fun Ej hEj => absurd hEj (hnex _)⟩, fun E hE => absurd hE (hnex _), fun q hq => ?_⟩
  rw [inverseTransformDivisor_id]
  exact hmult q hq

/-- The exceptional-curve bound in the inductive step of `exists_solution_of_pointBlowupChain`:
after blowing up a closed point `w`, every exceptional curve of `π ≫ h` has coefficient
`≥ 1 - μ` in the solution `π⁻¹_* a + (1 - mult_w Θ) F`. -/
private theorem one_sub_le_of_isExceptionalCurve_blowUpToBase_comp {k : Type w} [Field k]
    [IsAlgClosed k] {X : Scheme.{w}} {sX : X ⟶ Spec (.of k)}
    (hXn : MMP.Mori.IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    {Δ : MMP.Mori.QDivisor X} {μ : ℚ} (hμ : μ ≤ 1) {W : Scheme.{w}} {h : W ⟶ X}
    [QuasiCompact (h ≫ sX)] [IsLocallyNoetherian W] [IsNormal W]
    {K : MMP.Mori.Divisor W} {a : MMP.Mori.QDivisor W}
    (ha : IsNumericalPullbackSolution sX h K Δ a)
    (h1 : ∀ E : MMP.Mori.PrimeDivisor W, IsExceptionalCurve h E.idealSheaf → 1 - μ ≤ a E)
    (h2 : ∀ q : W, IsClosed ({q} : Set W) → (inverseTransformDivisor h Δ).multiplicityAt q ≤ μ)
    {w : W} (hw : IsClosed ({w} : Set W))
    {F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))}
    (hηF : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) F.genericPoint = w)
    (hiffB : ∀ C : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)).IdealSheafData,
      IsExceptionalCurve (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) C →
        (∃ E : W.IdealSheafData, IsExceptionalCurve h E ∧
          C = inverseTransformIdeal
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)) E.support) ∨
          C = F.idealSheaf)
    {E : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))}
    (hE : IsExceptionalCurve
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) E.idealSheaf) :
    1 - μ ≤ (inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      ⟨{w}, hw⟩)) a + Finsupp.single F (1 - (MMP.Mori.logPullback h Δ a).multiplicityAt w)) E := by
  classical
  obtain ⟨hWv, hWd, -⟩ := ha.1.isNormalVariety hXn
  have hWd2 : topologicalKrullDim W = 2 := hWd.trans hdim
  rcases hiffB E.idealSheaf hE with ⟨E0, hE0, hEE0⟩ | hEF
  · obtain ⟨P0, rfl⟩ := exists_primeDivisor_idealSheaf_eq hXn hdim ha.1 hE0
    have hP0w := genericPoint_ne_of_isClosed hWv.1 hWd2 P0 hw
    have hsome : inverseTransformPrimeDivisor
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)) P0 = some E :=
      MMP.Mori.inverseTransformPrimeDivisor_eq_some_iff.mpr
        ⟨⟨P0.genericPoint, by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
          MMP.Threefold.Resolution.mem_biregularLocus_blowUpToBase_singleton hw hP0w⟩, hEE0⟩
    have hEF : F ≠ E := by
      rintro rfl
      exact hP0w
        ((Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
          hsome).1.symm.trans hηF)
    rw [Finsupp.add_apply, inverseTransformDivisor_apply_of_eq_some hsome,
      Finsupp.single_apply, if_neg hEF, add_zero]
    exact h1 P0 hE0
  · obtain rfl : E = F := MMP.Mori.PrimeDivisor.ext_idealSheaf hEF
    have ha0 : 0 ≤ a := fun P => by
      by_cases hP : P ∈ a.support
      · exact (sub_nonneg.mpr hμ).trans (h1 P (ha.2.2.1 P hP))
      · rw [Finsupp.notMem_support_iff.mp hP]
        simp
    rw [Finsupp.add_apply, inverseTransformDivisor_apply_eq_zero ?_, Finsupp.single_eq_same,
      zero_add]
    · have : (MMP.Mori.logPullback h Δ a).multiplicityAt w ≤ μ := by
        rw [MMP.Mori.logPullback, multiplicityAt_sub]
        linarith [multiplicityAt_nonneg ha0 w, h2 w hw]
      linarith
    · intro P hP
      have hη :=
        (Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP).1
      rw [hηF] at hη
      exact genericPoint_ne_of_isClosed hWv.1 hWd2 P hw hη.symm

/-- **The induction along a chain of point blow-ups.** For every chain `h : W ⟶ X` of blow-ups of
closed points of the smooth surface `X`, there is a solution `a` of the numerical pull-back
equations of `(X, Δ)` on `h` with all entries `≥ 1 - μ`, and `mult_q (h⁻¹_* Δ) ≤ μ` at every
closed point `q` of `W`. -/
private theorem exists_solution_of_pointBlowupChain {k : Type w} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{w}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX)
    (hXs : MMP.Mori.IsSmoothScheme sX) (hdim : topologicalKrullDim X = 2)
    {Δ : MMP.Mori.QDivisor X} (hΔ : 0 ≤ Δ) {μ : ℚ} (hμ : μ ≤ 1)
    (hmult : ∀ p : X, IsClosed ({p} : Set X) → Δ.multiplicityAt p ≤ μ)
    {W : Scheme.{w}} {h : W ⟶ X}
    (hc : Stacks.ResolutionOfSurfaces.PointBlowupChain X Set.univ W h) :
    ∃ (_ : QuasiCompact (h ≫ sX)) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (K : MMP.Mori.Divisor W) (a : MMP.Mori.QDivisor W),
      IsNumericalPullbackSolution sX h K Δ a ∧
      (∀ E : MMP.Mori.PrimeDivisor W, IsExceptionalCurve h E.idealSheaf → 1 - μ ≤ a E) ∧
      ∀ q : W, IsClosed ({q} : Set W) → (inverseTransformDivisor h Δ).multiplicityAt q ≤ μ := by
  have hXn : MMP.Mori.IsNormalVariety k sX :=
    ⟨hX, (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hXs).2⟩
  have : IsIntegral X := hX.toIsIntegral
  induction hc with
  | refl => exact exists_solution_id hX hXs hdim hmult
  | @step W h hc w hw _ ih =>
    obtain ⟨_, _, _, K, a, ha, h1, h2⟩ := ih
    obtain ⟨hWv, hWd, -⟩ := ha.1.isNormalVariety hXn
    have hWd2 : topologicalKrullDim W = 2 := hWd.trans hdim
    have : LocallyOfFiniteType (h ≫ sX) := hWv.1.toLocallyOfFiniteType
    have : LocallyOfFinitePresentation (h ≫ sX) :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
    have : Smooth (h ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp ha.1.isSmoothScheme
    obtain ⟨hvar, -, hdimB, -, -, -, F, hF, hFsupp, -⟩ :=
      Threefold.Resolution.isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve
        (h ≫ sX) hWv.1 hWd2 hw
    have hBs := MMP.Threefold.Resolution.isSmoothScheme_blowUp_singleton hWv.1
      ha.1.isSmoothScheme hWd2 hw
    obtain ⟨hBl, hBn⟩ :=
      MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hBs
    have : QuasiCompact
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h ≫ sX) :=
      hvar.toQuasiCompact
    have hqc : QuasiCompact
        ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) ≫ sX) := by
      rw [Category.assoc]; infer_instance
    have : IsIntegral (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)) :=
      hvar.toIsIntegral
    have : CompactSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)) :=
      QuasiCompact.compactSpace_of_compactSpace
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h ≫ sX)
    have : AlgebraicGeometry.IsVariety k
        ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) ≫ sX) := by
      rwa [Category.assoc]
    obtain ⟨K', hK'⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme
      ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h) ≫ sX)
      (by rwa [Category.assoc]) (n := 2) (by rw [hdimB]; rfl)
    obtain ⟨hiffB, hsol⟩ := ha.isNumericalPullbackSolution_blowUpToBase_comp hXn hdim hw hF
      ⟨2, hK'⟩
    have hηF :
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) F.genericPoint = w := by
      have : F.genericPoint ∈ (F.support : Set _) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      rwa [hFsupp] at this
    refine ⟨hqc, hBl, hBn, K', _, hsol, fun E hE => ?_, fun x hx => ?_⟩
    · exact one_sub_le_of_isExceptionalCurve_blowUpToBase_comp hXn hdim hμ ha h1 h2 hw hηF
        (fun C => (hiffB C).1) hE
    · rw [inverseTransformDivisor_blowUpToBase_comp hXn hdim ha.1 hw hsol.1]
      exact multiplicityAt_inverseTransformDivisor_blowUpToBase_le_of_forall hWv.1
        ha.1.isSmoothScheme hWd2 hw hF (inverseTransformDivisor_nonneg h hΔ) h2 hx

/-- On a smooth surface `X`, let `Δ` be an effective `ℚ`-divisor and `μ ≤ 1` with
`mult_p Δ ≤ μ` at every closed point `p`. Then every numerical discrepancy `a(E, X, Δ)` of an
exceptional curve `E` of a resolution `g : Y ⟶ X`, computed on `g`, is at least `1 - μ`. -/
@[mmp "lem_km4a_smooth_surface_discrepancy_bound"]
public theorem IsNumericalDiscrepancy.one_sub_le_of_multiplicityAt_le
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsVariety k sX) (hXs : IsSmoothScheme sX)
    (hdim : topologicalKrullDim X = 2)
    {Δ : QDivisor X} (hΔ : 0 ≤ Δ) {μ : ℚ} (hμ : μ ≤ 1)
    (hmult : ∀ p : X, IsClosed ({p} : Set X) → Δ.multiplicityAt p ≤ μ)
    {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    {K : Divisor Y} {E : PrimeDivisor Y} {q : ℚ}
    (hq : IsNumericalDiscrepancy sX g K Δ E q) :
    1 - μ ≤ q := by
  obtain ⟨hE, a, ha, rfl⟩ := hq
  have hres := ha.1
  have hXn : MMP.Mori.IsNormalVariety k sX :=
    ⟨hX, (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hXs).2⟩
  obtain ⟨hYn, hYd, hbir⟩ := hres.isNormalVariety hXn
  have : IsProper g := hres.isProper
  obtain ⟨Z, c, hc, e, he⟩ := MMP.Resolution.Bridges.factorsAsPointBlowups_of_isSmoothSurface k
    hX hXs hdim hYn.1 hres.isSmoothScheme (hYd.trans hdim) g rfl hbir
  obtain ⟨_, _, _, Kc, ac, hac, hbd, -⟩ :=
    exists_solution_of_pointBlowupChain hX hXs hdim hΔ hμ hmult hc
  subst he
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Z := hac.1.isIntegral
  have hh : IsSmoothResolution (c ≫ sX) e.hom :=
    ⟨inferInstance, MMP.Mori.isBirationalMorphism_of_isIso _, by
      rw [← Category.assoc]; exact hres.isSmoothScheme⟩
  obtain ⟨b, hb, hbE, -⟩ := hac.exists_isNumericalPullbackSolution_comp hXn hdim hac.1 hh ha.2.1
  obtain ⟨n, hn⟩ := ha.2.1
  have hn2 : n = 2 := by
    have := hn.topologicalKrullDim_eq
    rw [hYd, hdim] at this
    exact_mod_cast this.symm
  subst hn2
  have hab : a = b := (MMP.Mori.existsUnique_isNumericalPullbackSolution sX (e.hom ≫ c) hXn hdim
    hres K hn Δ).unique ha hb
  subst hab
  obtain ⟨-, -, -, hiff⟩ :=
    MMP.Mori.isSmoothResolution_comp_and_isExceptionalCurve_comp_iff hXn hdim hac.1 hh
  rcases (hiff _).1 hE with ⟨E0, hE0, hEE0⟩ | hEe
  · obtain ⟨P0, rfl⟩ := exists_primeDivisor_idealSheaf_eq hXn hdim hac.1 hE0
    rw [hbE P0 E hE0 hEE0]
    exact hbd P0 hE0
  · exact absurd hEe (not_isExceptionalCurve_of_injective e.hom.isOpenEmbedding.injective _)

end DiscrepancyBound

section TerminalIffMult

universe u
universe w

open MMP.Threefold.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Exceptional divisors -/

/-- A divisor over a normal variety is exceptional if and only if its center has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type w} [Field k] {X : Scheme.{w}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- The restriction to an open `U` of an exceptional divisor over `X` whose center meets `U` is
exceptional over `U`. -/
private theorem isExceptional_restrict {k : Type w} [Field k] {X : Scheme.{w}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {U : X.Opens} [Nonempty U] (D : DivisorOver k sX)
    (hD : D.IsExceptional) (hU : IsNormalVariety k (U.ι ≫ sX))
    (hY : IsNormalVariety k ((D.f ∣_ U) ≫ U.ι ≫ sX)) (hf : IsBirationalMorphism (D.f ∣_ U))
    (E' : MMP.Mori.PrimeDivisor (D.f ⁻¹ᵁ U).toScheme)
    (hE' : OpenWeilRestriction.primeDivisorMap (D.f ⁻¹ᵁ U).ι E' = D.E) :
    (⟨_, D.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX)).IsExceptional := by
  rw [isExceptional_iff_two_le_coheight hU]
  rw [isExceptional_iff_two_le_coheight hX] at hD
  change 2 ≤ Order.coheight ((D.f ∣_ U) E'.genericPoint)
  rw [← coheight_eq_of_isOpenImmersion U.ι]
  have : U.ι ((D.f ∣_ U) E'.genericPoint) = D.f D.E.genericPoint := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, ← hE']
    exact congrArg D.f (OpenWeilRestriction.genericPoint_primeDivisorMap _ E').symm
  rw [this]
  exact hD

/-! ### Multiplicities -/

/-- The multiplicity of a prime divisor at a point is the order of its ideal sheaf there. -/
private theorem multiplicityAt_eq_multAt {X : Scheme.{w}} (P : MMP.Mori.PrimeDivisor X) (y : X) :
    P.multiplicityAt y = MMP.Resolution.multAt P.idealSheaf y := by
  simp only [MMP.Mori.PrimeDivisor.multiplicityAt, MMP.Resolution.multAt,
    MMP.Resolution.idealOrder, Scheme.IdealSheafData.stalkIdeal_eq_stalk]

/-- Along an open immersion, `ord_u (j^*I) = ord_{j u} I`. -/
private theorem multAt_comap_of_isOpenImmersion {X Y : Scheme.{w}} (f : Y ⟶ X)
    [IsOpenImmersion f] (I : X.IdealSheafData) (y : Y) :
    MMP.Resolution.multAt (I.comap f) y = MMP.Resolution.multAt I (f y) := by
  rw [MMP.Resolution.multAt, MMP.Resolution.multAt, IdealSheafData.stalk_comap]
  exact idealOrder_map_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv _

/-- The multiplicity of the restriction `Δ|_U` at `p` is the multiplicity of `Δ` at `p`. -/
private theorem multiplicityAt_restrictOpen {X : Scheme.{w}} (Δ : QDivisor X) (U : X.Opens)
    (p : U.toScheme) : (Δ.restrictOpen U).multiplicityAt p = Δ.multiplicityAt (U.ι p) := by
  classical
  have hmult : ∀ W : MMP.Mori.PrimeDivisor U.toScheme, W.multiplicityAt p =
      MMP.Mori.PrimeDivisor.multiplicityAt (OpenWeilRestriction.primeDivisorMap U.ι W)
        (U.ι p) := by
    intro W
    rw [multiplicityAt_eq_multAt, multiplicityAt_eq_multAt,
      ← multAt_comap_of_isOpenImmersion U.ι,
      MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap]
  have hcoeff : ∀ W, (Δ.restrictOpen U) W = Δ (OpenWeilRestriction.primeDivisorMap U.ι W) :=
    fun W => rfl
  unfold DivisorWithCoeffs.multiplicityAt Finsupp.sum
  refine Finset.sum_bij_ne_zero (fun W _ _ => OpenWeilRestriction.primeDivisorMap U.ι W)
    ?_ ?_ ?_ ?_
  · intro W hW _
    rw [Finsupp.mem_support_iff, ← hcoeff]
    exact Finsupp.mem_support_iff.mp hW
  · intro W _ _ W' _ _ h
    exact OpenWeilRestriction.primeDivisorMap_injective U.ι h
  · intro P hP hne
    dsimp only at hne
    have hpP : U.ι p ∈ P.support := by
      by_contra h
      rw [MMP.Mori.PrimeDivisor.multiplicityAt_eq_zero_of_notMem P h] at hne
      simp at hne
    obtain ⟨W, rfl⟩ :=
      MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support U.ι P p hpP
    refine ⟨W, ?_, ?_, rfl⟩
    · rw [Finsupp.mem_support_iff, hcoeff]
      exact Finsupp.mem_support_iff.mp hP
    · dsimp only
      rwa [hcoeff, hmult]
  · intro W _ _
    dsimp only
    rw [hcoeff, hmult]

/-- **Upper semicontinuity of the multiplicity.** On a smooth scheme over a field of
characteristic zero, an effective `ℚ`-divisor `Δ` has `mult_p Δ ≤ mult_x Δ` for all `p` in some
open neighbourhood of `x`. -/
private theorem exists_mem_forall_multiplicityAt_le {k : Type w} [Field k] [CharZero k]
    {X : Scheme.{w}} [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} [Smooth sX]
    (hXs : IsSmoothScheme sX) {Δ : QDivisor X} (hΔ : 0 ≤ Δ) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ p ∈ U, Δ.multiplicityAt p ≤ Δ.multiplicityAt x := by
  classical
  have hcl : ∀ P : MMP.Mori.PrimeDivisor X, IsClosed (P.support : Set X) := fun P => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isClosed_closure
  have hfin : ∀ P : MMP.Mori.PrimeDivisor X,
      MMP.Resolution.multAt P.idealSheaf x = ((P.multiplicityAt x).toNat : ℕ∞) := fun P => by
    rw [← multiplicityAt_eq_multAt, ENat.coe_toNat (multiplicityAt_ne_top P
      (isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hXs P) x)]
  let C : MMP.Mori.PrimeDivisor X → Set X := fun P =>
    {p | (((P.multiplicityAt x).toNat + 1 : ℕ) : ℕ∞) ≤ MMP.Resolution.multAt P.idealSheaf p} ∪
      (if x ∈ P.support then ∅ else (P.support : Set X))
  have hC : ∀ P, IsClosed (C P) := fun P =>
    (MMP.Resolution.isClosed_setOf_le_multAt sX _ _).union (by
      split_ifs
      exacts [isClosed_empty, hcl P])
  refine ⟨⟨(⋃ P ∈ Δ.support, C P)ᶜ, (isClosed_biUnion_finset fun P _ => hC P).isOpen_compl⟩,
    ?_, ?_⟩
  · simp only [Opens.mem_mk, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro P _ hxC
    rcases hxC with h | h
    · rw [Set.mem_setOf_eq, hfin P] at h
      exact absurd (by exact_mod_cast h : (P.multiplicityAt x).toNat + 1 ≤ _) (by omega)
    · split_ifs at h with hx
      exacts [h, hx h]
  · intro p hp
    simp only [Opens.mem_mk, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hp
    unfold DivisorWithCoeffs.multiplicityAt Finsupp.sum
    refine Finset.sum_le_sum fun P hP => nsmul_le_nsmul_left (hΔ P) ?_
    have hpC := hp P hP
    by_cases hxP : x ∈ P.support
    · have h1 : ¬ (((P.multiplicityAt x).toNat + 1 : ℕ) : ℕ∞) ≤
          MMP.Resolution.multAt P.idealSheaf p := fun h => hpC (Or.inl h)
      rw [not_le] at h1
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h1)
      rw [multiplicityAt_eq_multAt, ← hm, ENat.toNat_coe]
      rw [← hm] at h1
      have : m < (P.multiplicityAt x).toNat + 1 := by exact_mod_cast h1
      omega
    · have h1 : p ∉ P.support := fun h => hpC (Or.inr (by rwa [if_neg hxP]))
      rw [MMP.Mori.PrimeDivisor.multiplicityAt_eq_zero_of_notMem P h1]
      simp

/-! ### The blow-up of a point -/

/-- The exceptional curve `F` of the blow-up of a closed point `x` of a smooth surface is an
exceptional divisor over `X` lying over `x`, with discrepancy `a(F, X, Δ) = 1 - mult_x Δ`. -/
public theorem exists_isExceptional_isDiscrepancy_one_sub_multiplicityAt {k : Type w} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{w}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) (hXs : IsSmoothScheme sX)
    (hdim : topologicalKrullDim X = 2) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    (Δ : QDivisor X) {x : X} (hx : IsClosed ({x} : Set X)) :
    ∃ D : DivisorOver k sX, D.IsExceptional ∧ D.f D.E.genericPoint = x ∧
      IsDiscrepancy sX 2 K Δ D (1 - Δ.multiplicityAt x) := by
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : Smooth sX := (isSmoothScheme_iff sX).mp hXs
  have hXn : IsNormalVariety k sX := ⟨hX, inferInstance⟩
  obtain ⟨hvar, -, -, -, hbir, -, F, -, hFs, -⟩ :=
    isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve sX hX hdim hx
  have hnor := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    (isSmoothScheme_blowUp_singleton hX hXs hdim hx)).2
  let D : DivisorOver k sX := ⟨_, _, ⟨hvar, hnor⟩, hbir, F⟩
  have hη : D.f D.E.genericPoint = x := by
    have h : D.E.genericPoint ∈ (F.support : Set _) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    rwa [hFs] at h
  let Z : IrreducibleCloseds X := ⟨{x}, isIrreducible_singleton, hx⟩
  have hZg : Z.isIrreducible.genericPoint = x :=
    (IsIrreducible.isGenericPoint_genericPoint_closure Z.isIrreducible).eq isGenericPoint_closure
  have hcod : codimension Z = 2 := by
    convert codimension_vanishingIdeal_singleton_eq_two hX hdim hx using 2
    ext1
    exact (Scheme.IdealSheafData.coe_support_vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).symm
  have hcen : D.center = Z := IrreducibleCloseds.ext (by
    rw [DivisorOver.center_eq_closure_genericPoint, hη, hx.closure_eq]; rfl)
  have hDe : D.IsExceptional := by
    rw [isExceptional_iff_two_le_coheight hXn, ← MMP.Positivity.DivisorOver.codimension_center,
      hcen, hcod]
  obtain ⟨-, ha⟩ := isDiscrepancy_blowUp sX hX hK Δ Z (c := 2) (by rw [hcod]; rfl) le_rfl D
    (Stacks.Blowup.blowUpIso _).inv
    (by rw [← Stacks.Blowup.blowUpIso_hom_comp]; exact Iso.inv_hom_id_assoc _ _)
    (hη.trans hZg.symm)
  refine ⟨D, hDe, hη, ?_⟩
  convert ha using 1
  have hm : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.multiplicityAlong Z = Γ.multiplicityAt x := by
    intro Γ
    let G : X → ℕ∞ := fun g => ⨆ (s : ℕ) (_ : Γ.idealSheaf.stalkIdeal g ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk g) ^ s), (s : ℕ∞)
    exact (show Γ.multiplicityAlong Z = G Z.isIrreducible.genericPoint from rfl).trans
      (congrArg G hZg)
  simp only [DivisorWithCoeffs.multiplicityAt, hm, nsmul_eq_mul, mul_comm]
  norm_num

/-! ### Numerical discrepancies on a smooth surface -/

/-- **Discrepancies are numerical discrepancies** on a smooth surface `V`: if `E` is an
exceptional curve of a resolution `g : Y ⟶ V`, the discrepancy `a(E, V, Θ)` is a numerical
discrepancy of `E` computed on `g`. -/
private theorem isNumericalDiscrepancy_of_isDiscrepancy {k : Type w} [Field k] [PerfectField k]
    {V : Scheme.{w}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV) (hVs : IsSmoothScheme sV)
    (hdim : topologicalKrullDim V = 2) {K : Divisor V} (hK : K.IsCanonicalDivisor sV 2)
    {Θ : QDivisor V} (D : DivisorOver k sV) [QuasiCompact (D.f ≫ sV)] [IsLocallyNoetherian D.Y]
    [IsNormal D.Y] (hD : IsSmoothResolution sV D.f) (hE : IsExceptionalCurve D.f D.E.idealSheaf)
    {K' : Divisor D.Y} (hK' : ∃ n : ℕ, K'.IsCanonicalDivisor (D.f ≫ sV) n) {a : ℚ}
    (ha : IsDiscrepancy sV 2 K Θ D a) : IsNumericalDiscrepancy sV D.f K' Θ D.E a := by
  haveI : QuasiCompact (𝟙 V ≫ sV) := hV.1.toQuasiCompact
  haveI : QuasiCompact ((D.f ≫ 𝟙 V) ≫ sV) := ‹QuasiCompact (D.f ≫ sV)›
  have hid : IsSmoothResolution sV (𝟙 V) :=
    ⟨inferInstance, isBirationalMorphism_of_isIso _, hVs⟩
  have h0 : IsNumericalPullbackSolution sV (𝟙 V) K Θ 0 :=
    ⟨hid, ⟨2, hK⟩, by simp, fun Ej hEj => (not_isExceptionalCurve_of_injective
      (Scheme.Hom.isOpenEmbedding (𝟙 V)).injective _ hEj).elim⟩
  obtain ⟨b, hb, -, hbF⟩ :=
    h0.exists_isNumericalPullbackSolution_comp (h := D.f) hV hdim hid hD hK'
  obtain ⟨n, hn⟩ := hbF D.E hE
  obtain rfl : n = 2 := by
    exact_mod_cast hn.2.1.topologicalKrullDim_eq.symm.trans hK.topologicalKrullDim_eq
  have hθ : logPullback (𝟙 V) Θ 0 = Θ :=
    (sub_zero _).trans (inverseTransformDivisor_id Θ)
  have hn' : IsDiscrepancy sV 2 K Θ D (b D.E) := hθ ▸ hn
  exact ⟨hE, b, hb, (ha.eq hn').symm⟩

/-- On a smooth surface `V` with `mult_p Δ ≤ μ ≤ 1` at every closed point, every exceptional
divisor over `V` has discrepancy at least `1 - μ`. -/
private theorem one_sub_le_of_isDiscrepancy {k : Type w} [Field k] [IsAlgClosed k] [CharZero k]
    {V : Scheme.{w}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV) (hVs : IsSmoothScheme sV)
    (hdim : topologicalKrullDim V = 2) {K : Divisor V} (hK : K.IsCanonicalDivisor sV 2)
    {Δ : QDivisor V} (hΔ : 0 ≤ Δ) {μ : ℚ} (hμ : μ ≤ 1)
    (hmult : ∀ p : V, IsClosed ({p} : Set V) → Δ.multiplicityAt p ≤ μ)
    {D : DivisorOver k sV} (hD : D.IsExceptional) {a : ℚ} (ha : IsDiscrepancy sV 2 K Δ D a) :
    1 - μ ≤ a := by
  obtain ⟨D', hres, hexc, hval⟩ := hD.exists_isSmoothResolution_isExceptionalCurve hV.1 hdim
  have hpair : IsPairWith sV 2 K Δ := ⟨hV, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hVs _⟩
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair.isPair hK D'
  have hae : a' = a := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hpair hval ha' ha
  haveI := D'.isLocallyNoetherian
  haveI := D'.isNormal
  haveI := D'.isIntegral
  haveI : MMP.Mori.IsVariety k (D'.f ≫ sV) := D'.isNormalVariety.1
  haveI : QuasiCompact (D'.f ≫ sV) := D'.isNormalVariety.1.toQuasiCompact
  haveI : CompactSpace D'.Y := QuasiCompact.compactSpace_of_compactSpace (D'.f ≫ sV)
  have hdY : topologicalKrullDim D'.Y = ((2 : ℕ) : WithBot ℕ∞) := by
    rw [(hres.isNormalVariety hV).2.1, hdim]; rfl
  obtain ⟨K', hK'⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (D'.f ≫ sV)
    hres.isSmoothScheme hdY
  have hnum := isNumericalDiscrepancy_of_isDiscrepancy hV hVs hdim hK D' hres hexc ⟨2, hK'⟩ ha'
  rw [← hae]
  exact IsNumericalDiscrepancy.one_sub_le_of_multiplicityAt_le hV.1 hVs hdim hΔ hμ hmult hnum

/-! ### The theorem -/

/-- Let `X` be a smooth surface over an algebraically closed field of characteristic zero, with
canonical divisor `K`, let `x ∈ X` be a closed point and `Δ` an effective `ℚ`-divisor. Then
`(U, Δ|_U)` is terminal for some open neighbourhood `U` of `x` if and only if `mult_x Δ < 1`. -/
@[mmp "lem_km4a_smooth_surface_terminal_iff_mult"]
public theorem isAt_isTerminalPair_iff_multiplicityAt_lt_one
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsVariety k sX) (hXs : IsSmoothScheme sX)
    (hdim : topologicalKrullDim X = 2)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    {Δ : QDivisor X} (hΔ : 0 ≤ Δ) {x : X} (hx : IsClosed ({x} : Set X)) :
    IsAt sX (fun sU n K Δ => IsTerminalPair sU n K Δ) 2 K Δ x ↔ Δ.multiplicityAt x < 1 := by
  have hXn : IsNormalVariety k sX := ⟨hX, inferInstance⟩
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : Smooth sX := (isSmoothScheme_iff sX).mp hXs
  have hpair : IsPairWith sX 2 K Δ :=
    ⟨hXn, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hXs _⟩
  obtain ⟨D, hD, hDx, ha⟩ :=
    exists_isExceptional_isDiscrepancy_one_sub_multiplicityAt hX hXs hdim hK Δ hx
  have hcx : x ∈ (D.center : Set X) := by
    rw [DivisorOver.center_eq_closure_genericPoint, hDx]
    exact subset_closure rfl
  constructor
  · rintro ⟨U, hxU, hne, hT⟩
    have hU : ((D.center : Set X) ∩ U).Nonempty := ⟨x, hcx, hxU rfl⟩
    obtain ⟨hY, hf, E', hE', -, hiff⟩ :=
      DivisorOver.exists_restrict_isDiscrepancy_iff hpair D U hU
    have ha' := (hiff _).mp ha
    have hle := discrep_le (isExceptional_restrict hXn D hD hT.1.1 hY hf E' hE') ha'
    exact sub_pos.mp (by exact_mod_cast hT.2.trans_le hle)
  · intro hlt
    obtain ⟨U, hxU, hU⟩ := exists_mem_forall_multiplicityAt_le hXs hΔ x
    have hDU : ((D.center : Set X) ∩ U).Nonempty := ⟨x, hcx, hxU⟩
    obtain ⟨hY, hf, E', hE', -, hiff⟩ :=
      DivisorOver.exists_restrict_isDiscrepancy_iff hpair D U hDU
    haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
    have ha' := (hiff _).mp ha
    have hUn : IsNormalVariety k (U.ι ≫ sX) := ha'.1
    have hKU : Divisor.IsCanonicalDivisor (U.ι ≫ sX) 2 (K.restrictOpen U) := ha'.2.1
    have hUs : IsSmoothScheme (U.ι ≫ sX) := isSmoothScheme_ι k hXs U
    have hUd : topologicalKrullDim U = 2 := by exact_mod_cast hKU.topologicalKrullDim_eq
    have hΔU : 0 ≤ Δ.restrictOpen U := fun W => hΔ _
    refine ⟨U, Set.singleton_subset_iff.mpr hxU, inferInstance,
      ⟨hUn, hKU, MMP.Fourfold.isQCartier_of_isSmoothScheme hUs _⟩, ?_⟩
    have hb : (((1 - Δ.multiplicityAt x : ℚ) : ℝ) : EReal) ≤
        discrep (U.ι ≫ sX) 2 (K.restrictOpen U) (Δ.restrictOpen U) :=
      le_discrep_iff.mpr fun D' a hD' ha'' => EReal.coe_le_coe_iff.mpr (by
        exact_mod_cast one_sub_le_of_isDiscrepancy hUn hUs hUd hKU hΔU hlt.le
          (fun p _ => (multiplicityAt_restrictOpen Δ U p).trans_le (hU _ p.2)) hD' ha'')
    exact lt_of_lt_of_le (by exact_mod_cast sub_pos.mpr hlt) hb

end TerminalIffMult

end MMP.Mori
