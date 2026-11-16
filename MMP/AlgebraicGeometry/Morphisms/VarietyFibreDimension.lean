module

public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
public import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
public import MMP.Analysis.Complex.HolomorphicGermPowerSeries
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericConstancy
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupFactorizationStep

/-!
# Foundational lemmas on morphisms of varieties, surfaces and holomorphic germs

This file collects foundational results used throughout the minimal model program.

* A rational map `φ : W ⤏ Y` from a locally noetherian normal integral scheme, lying over a
  proper morphism `f : Y ⟶ X`, is defined at the generic point of every prime divisor of `W`:
  the local ring there is a discrete valuation ring, and the valuative criterion of properness
  extends `φ` across its closed point.
* For a dominant morphism `f : X ⟶ Y` of varieties, every irreducible component of every fibre
  has dimension at least `dim X - dim Y`, the fibres over a dense open have pure dimension
  `dim X - dim Y`, and the local fibre dimension is upper semicontinuous.
* A finite scheme over a quasi-projective scheme over a field is quasi-projective.
* A closed subscheme `X` of a smooth `k`-scheme `P`, smooth near `x` and of codimension `c`
  there, is cut out near `x` by `c` functions with linearly independent differentials.
* A proper birational morphism of smooth surfaces that is an isomorphism over no neighbourhood
  of a closed point `P` factors through the blowup at `P`.
* A proper birational morphism onto a normal variety has nonempty connected fibres.
* Hadamard division: a holomorphic `h` satisfies `h y - h y' = ∑ i, (y i - y' i) * H i (y, y')`
  with `H i` holomorphic, and consequently germ ideals are stable under composition.
* The product of a separated complex variety with `ℙ¹`, and the irreducible components of the
  preimage of a closed set under the projection `S × ℙ¹ → S`.

## Main results

* `MMP.Flips.RationalMap.mem_domain_of_coheight_le_one` (registered for the node)
* `MMP.topologicalKrullDim_fiber_of_isDominant`
* `MMP.Intersection.isQuasiProjective_of_isFinite`
* `MMP.Foundations.exists_affineOpen_ker_eq_span_linearIndependent_D`
* `MMP.Resolution.Bridges.exists_comp_eq_pointBlowUpToBase_of_isSmoothSurface`
* `MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism` (part 2, registered)
* `MMP.Analytic.exists_sub_eq_sum_sub_mul_and_comp_sub_comp_mem`
* `MMP.Fourfold.isVariety_product_projectiveLine_and_irreducibleComponents_preimage`

## Implementation notes

* "Defined at a point" is membership in `φ.domain`; the relation `f ∘ φ = g` is
  `MMP.Flips.RationalMap.IsOver g f φ`. The general pointwise form is
  `MMP.Flips.RationalMap.mem_domain_of_coheight_le_one`, which carries the same tag.
* Fibre dimensions take values in `WithBot ℕ∞`, which has no subtraction, so the relative
  dimension `e = dim X - dim Y` enters additively: "`dim Z ≥ e`" is `dim X ≤ dim Z + dim Y`. The
  local fibre dimension at `x` is `topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)`, and the
  threshold `d` ranges over `ℕ`, since a negative threshold defines all of `X`.
* Quasi-projectivity over `Spec K` is `AlgebraicGeometry.IsQuasiProjective` of the structure
  morphism, equivalent over the affine base to an immersion into a projective space; the source
  works over `ℂ`, the statement over any field.
* For the local equations, the neighbourhood is affine, the ideal sheaf on it is
  `i.ker.ideal U`, `Ω_{P/k} ⊗ κ(x)` is `κ(x) ⊗[Γ(P, U)] Ω[Γ(P, U)⁄k]`, and the codimension is
  `dim 𝒪_{P,x} - dim 𝒪_{X,x}`, stated additively.
* A smooth surface over `k` with structure morphism `sY` is `IsVariety k sY`,
  `MMP.Mori.IsSmoothScheme sY` and `topologicalKrullDim Y = 2`; the blowup at a closed point is
  `Stacks.ResolutionOfSurfaces.pointBlowUp`. No assumption on `k` is needed.
* Connectedness of a fibre is `IsConnected (g ⁻¹' {x})`, which includes nonemptiness. The
  statement together with `g_* 𝒪_Y = 𝒪_X` is
  `MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism`, which carries the
  same tag.
* "Holomorphic near `p`" is `∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y`, the convention of
  `MMP.Analytic.holGerms`; membership of the germ of `f` in an ideal `I` of `holGerms a` is
  `∃ g ∈ I, (g : Germ (𝓝 a) ℂ) = ↑f`. Monomials in `(w, u)` are indexed by `(ι ⊕ ι) →₀ ℕ`, and
  the coordinate `uᵢ` extracted from a monomial is chosen, so no order on `ι` is needed.
* A reduced closed subscheme of `S` is recorded by its closed support `Z`, and `Z × ℙ¹` by the
  preimage under `pullback.fst`; an irreducible component of `Z` is a maximal irreducible subset
  of `Z`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998]
* [Lazarsfeld, *Positivity in Algebraic Geometry I*, Notation and Conventions]
* [Stacks Project, Tags 0B2L, 05F7, 0C4M, 0C5R, 0AY8]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-! ### Rational maps over a proper target -/

namespace MMP.Flips.RationalMap

attribute [mmp "lem_mmp_foundation_km_relative_rational_map_codimension_one"]
  mem_domain_of_coheight_le_one

end MMP.Flips.RationalMap

/-! ### Dimensions of the fibres of a dominant morphism of varieties -/

section FibreDimension

open TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP

/-- A dominant morphism sends a generic point of an irreducible source to the generic point of
the target. -/
private lemma isGenericPoint_apply_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    {η : X} (hη : IsGenericPoint η Set.univ) : IsGenericPoint (f η) Set.univ := by
  simpa [Set.image_univ, f.denseRange.closure_range] using hη.image f.continuous

/-- For a dominant morphism of irreducible schemes locally of finite type over a field, both
dimensions are natural numbers and the target has the smaller one. -/
private lemma exists_topologicalKrullDim_eq_natCast (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDominant f] :
    ∃ n m : ℕ, topologicalKrullDim X = n ∧ topologicalKrullDim Y = m ∧ m ≤ n := by
  let η : X := genericPoint X
  have hη : IsGenericPoint η Set.univ := genericPoint_spec X
  let ξ : Y := f η
  have hξ : IsGenericPoint ξ Set.univ := isGenericPoint_apply_of_isDominant f hη
  let : Algebra k (X.residueField η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation η).hom.toAlgebra
  let : Algebra k (Y.residueField ξ) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation ξ).hom.toAlgebra
  have hηtrdeg : Algebra.trdeg k (X.residueField η) < Cardinal.aleph0 := by
    let : FinTrdeg k (X.residueField η) := residueField_finTrdeg k pX η
    exact trdeg_lt_aleph0 k _
  let : Algebra (Y.residueField ξ) (X.residueField η) := (f.residueFieldMap η).hom.toAlgebra
  have : IsScalarTower k (Y.residueField ξ) (X.residueField η) := by
    apply IsScalarTower.of_algebraMap_eq'
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation η).hom =
      (f.residueFieldMap η).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation ξ).hom
    have hcat : (Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation η =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation ξ) ≫
          f.residueFieldMap η := by
      rw [← hf, Scheme.Hom.comp_appTop, Category.assoc, Category.assoc, Category.assoc,
        Scheme.Γevaluation_naturality f η]
    simpa [CommRingCat.hom_comp, RingHom.comp_assoc] using congrArg CommRingCat.Hom.hom hcat
  have htower : Algebra.trdeg k (Y.residueField ξ) +
      Algebra.trdeg (Y.residueField ξ) (X.residueField η) = Algebra.trdeg k (X.residueField η) :=
    trdeg_add_eq k (Y.residueField ξ)
  have hle : Algebra.trdeg k (Y.residueField ξ) ≤ Algebra.trdeg k (X.residueField η) :=
    htower ▸ le_self_add
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hηtrdeg
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt hηtrdeg)
  refine ⟨n, m, ?_, ?_, by exact_mod_cast hn ▸ hm ▸ hle⟩
  · rw [topologicalKrullDim_eq_trdeg_residueField k X pX η hη, hn, Cardinal.toENat_nat]
    rfl
  · rw [topologicalKrullDim_eq_trdeg_residueField k Y pY ξ hξ, hm, Cardinal.toENat_nat]
    rfl

/-- The reduced closed subscheme on the closure of the image of a dominant morphism is
homeomorphic to the target, so it has the dimension of the target. -/
private lemma topologicalKrullDim_subscheme_closure_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Set.range (fun x : X => f x)))).subscheme = topologicalKrullDim Y := by
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range (fun x : X => f x)))
  have hsurj : Function.Surjective I.subschemeι := by
    rw [← Set.range_eq_univ, I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure]
    exact f.denseRange.closure_range
  exact (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨I.subschemeι.isEmbedding, hsurj⟩).topologicalKrullDim_eq

/-- At the generic point of an irreducible component `Z` of a fibre of a morphism locally of
finite type over a field, the local dimension of the fibre is at most `dim Z`. -/
private lemma exists_topologicalKrullDimAt_fiber_le (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType pX]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (y : Y) (Z : Set (f.fiber y))
    (hZ : Z ∈ irreducibleComponents (f.fiber y)) :
    ∃ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ topologicalKrullDim Z := by
  let pF : f.fiber y ⟶ Spec (.of (Y.residueField y)) := f.fiberToSpecResidueField y
  have : LocallyOfFiniteType pF := locallyOfFiniteType_fiberToSpecResidueField k pX pY f hf y
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  set z := hZ.1.genericPoint
  have hz : IsGenericPoint z Z := by
    simpa [hZc.closure_eq] using hZ.1.isGenericPoint_genericPoint_closure
  have htrans : ∀ (y' : Y), y' = y → ∀ w : f.fiber y', f.fiberι y' w = f.fiberι y z →
      topologicalKrullDimAt (f.fiber y') w = topologicalKrullDimAt (f.fiber y) z := by
    rintro _ rfl w hw
    rw [f.fiberι_injective _ hw]
  refine ⟨f.fiberι y z, ?_⟩
  rw [htrans _ (f.apply_fiberι y z) _ (f.fiberι_asFiber _),
    topologicalKrullDimAt_eq_iSup_irreducibleComponents (Y.residueField y) _ pF]
  refine iSup₂_le fun Z' hZ' => ?_
  have hsub : Z ⊆ Z' := by
    rw [← hz.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hZ'.2)
      (isClosed_of_mem_irreducibleComponents Z' hZ'.1)
  rw [← hZ.eq_of_le hZ'.1.1 hsub]

/-- **Dimensions of fibres of a dominant morphism of varieties.** Let `f : X ⟶ Y` be a dominant
morphism of varieties over a field `k`. Then every irreducible component `Z` of every fibre of `f`
satisfies `dim X ≤ dim Z + dim Y`; there is a dense open `V` of `Y` over every point of which each
irreducible component `Z` of the fibre satisfies `dim Z + dim Y = dim X`; and for every `d`, the
locus of `x : X` with `d ≤ dim_x f⁻¹(f(x))` is closed. See Stacks Tags 0B2L, 05F7. -/
@[mmp "lem_mmp_foundation_km_variety_fibre_dimensions"]
public theorem topologicalKrullDim_fiber_of_isDominant (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [IsVariety k pX] [IsVariety k pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDominant f] :
    (∀ (y : Y), ∀ Z ∈ irreducibleComponents (f.fiber y),
      topologicalKrullDim X ≤ topologicalKrullDim Z + topologicalKrullDim Y) ∧
    (∃ V : Y.Opens, Dense (V : Set Y) ∧ ∀ y ∈ V, ∀ Z ∈ irreducibleComponents (f.fiber y),
      topologicalKrullDim Z + topologicalKrullDim Y = topologicalKrullDim X) ∧
    (∀ d : ℕ, IsClosed
      {x : X | (d : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)}) := by
  have : IsIntegral X := IsVariety.toIsIntegral (k := k) pX
  have : IsIntegral Y := IsVariety.toIsIntegral (k := k) pY
  have : LocallyOfFiniteType pX := IsVariety.toLocallyOfFiniteType (k := k)
  have : LocallyOfFiniteType pY := IsVariety.toLocallyOfFiniteType (k := k)
  have : QuasiCompact pX := IsVariety.toQuasiCompact (k := k)
  have : IsSeparated pY := IsVariety.toIsSeparated (k := k)
  have : LocallyOfFiniteType (f ≫ pY) := hf ▸ inferInstance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pY
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace pX
  have : QuasiSeparatedSpace Y := (quasiSeparated_iff_quasiSeparatedSpace pY).mp inferInstance
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  obtain ⟨n, m, hn, hm, hmn⟩ := exists_topologicalKrullDim_eq_natCast k pX pY f hf
  have hI := topologicalKrullDim_subscheme_closure_range f
  -- the lower bound on every component of every fibre
  have lower : ∀ (y : Y), ∀ Z ∈ irreducibleComponents (f.fiber y),
      topologicalKrullDim X ≤ topologicalKrullDim Z + topologicalKrullDim Y := by
    intro y Z hZ
    obtain ⟨x, hx⟩ := exists_topologicalKrullDimAt_fiber_le k pX pY f hf y Z hZ
    have key := topologicalKrullDim_le_fiber_add_imageClosure k pX pY f hf x
    rw [hI] at key
    exact key.trans (add_le_add_left hx _)
  refine ⟨lower, ?_, MMP.isClosed_setOf_le_fiberDimensionAt k pX pY f hf⟩
  -- the generic fibre has dimension `n - m`, and so do the fibres over a nonempty open
  let η : X := genericPoint X
  have hη : IsGenericPoint η Set.univ := genericPoint_spec X
  have hgen := topologicalKrullDim_fiber_genericPoint_eq_imageClosure_sub k pX pY f hf η hη
  rw [hn, show Set.range f.base = Set.range (fun x : X => f x) from rfl, hI, hm] at hgen
  simp only [WithBot.unbotD_coe, ENat.toNat_coe] at hgen
  obtain ⟨V, hVne, hV⟩ := exists_nonempty_open_fiberDimension_eq f (n - m) (f η)
    (isGenericPoint_apply_of_isDominant f hη) hgen
  refine ⟨V, V.isOpen.dense hVne, fun y hy Z hZ => le_antisymm ?_ (lower y Z hZ)⟩
  have hZle : topologicalKrullDim Z ≤ ((n - m : ℕ) : WithBot ℕ∞) := by
    rw [← hV y hy]
    exact Topology.IsInducing.subtypeVal.topologicalKrullDim_le
  rw [hm, hn]
  calc topologicalKrullDim Z + (m : WithBot ℕ∞) ≤ ((n - m : ℕ) : WithBot ℕ∞) + (m : WithBot ℕ∞) :=
        by gcongr
    _ = (n : WithBot ℕ∞) := by exact_mod_cast Nat.sub_add_cancel hmn

end MMP

end FibreDimension

/-! ### Finite schemes over quasi-projective schemes -/

namespace MMP.Intersection

/-- **A finite scheme over a quasi-projective scheme is quasi-projective.** Let `f : Y ⟶ X` be a
finite morphism of separated schemes of finite type over a field `K`. If `X` is quasi-projective
over `K`, then so is `Y`. See Stacks Tag 0C4M. -/
@[mmp "lem_mmp_foundation_laz_finite_over_quasiprojective"]
public theorem isQuasiProjective_of_isFinite (K : Type u) [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [IsSeparatedAlgebraicScheme K X] [IsSeparatedAlgebraicScheme K Y]
    (f : Y ⟶ X) [f.IsOver (Spec (.of K))] [IsFinite f]
    (hX : IsQuasiProjective (X ↘ Spec (.of K))) :
    IsQuasiProjective (Y ↘ Spec (.of K)) := by
  rw [← comp_over f (Spec (.of K))]
  exact (AlgebraicGeometry.isQuasiProjective_of_isFinite f).comp f _ hX

end MMP.Intersection

/-! ### Local equations of a smooth closed subscheme -/

namespace MMP.Foundations

open TensorProduct

/-- If `i : X ⟶ P` is a closed immersion and `X` is smooth over `k` near `x`, then the quotient
`𝒪_{P, i x} / I_{X, i x}` (which is `𝒪_{X, x}`) is a regular local ring, formally smooth over the
base, of the same Krull dimension as `𝒪_{X, x}`. -/
private lemma stalk_quotient_ker_of_smooth {k : Type*} [Field k] {P X : Scheme}
    (π : P ⟶ Spec (.of k)) (i : X ⟶ P) [IsClosedImmersion i] {x : X} {V : X.Opens}
    (hxV : x ∈ V) (hV : Smooth (V.ι ≫ i ≫ π)) :
    IsRegularLocalRing (P.presheaf.stalk (i x) ⧸ IdealSheafData.stalk i.ker (i x)) ∧
    (letI := (π.stalkMap (i x)).hom.toAlgebra;
      Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (π (i x)))
        (P.presheaf.stalk (i x) ⧸ IdealSheafData.stalk i.ker (i x))) ∧
    ringKrullDim (P.presheaf.stalk (i x) ⧸ IdealSheafData.stalk i.ker (i x)) =
      ringKrullDim (X.presheaf.stalk x) := by
  obtain ⟨W0, hW0, hxW0, -⟩ := exists_isAffineOpen_mem_and_subset
    (show i x ∈ (⊤ : P.Opens) from trivial)
  let e : (P.presheaf.stalk (i x) ⧸ IdealSheafData.stalk i.ker (i x)) ≃+* X.presheaf.stalk x :=
    (Ideal.quotEquivOfEq (stalk_ker_eq_of_affine_target i x W0 hW0 hxW0)).trans
      (RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective x))
  let v : V := ⟨x, hxV⟩
  have := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ i ≫ π) v
  have : IsIso (V.ι.stalkMap v) := IsOpenImmersion.instIsIsoCommRingCatStalkMap V.ι v
  have hXreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    IsRegularLocalRing.of_ringEquiv (asIso (V.ι.stalkMap v)).commRingCatIsoToRingEquiv.symm
  have hsa : InfinitesimalLifting.SmoothAt (i ≫ π) x := by
    refine ⟨V, hxV, ?_⟩
    have he : (i ≫ π).resLE ⊤ V le_top = V.ι ≫ (i ≫ π) ≫ (Spec (.of k)).topIso.inv := by
      apply (cancel_mono (⊤ : (Spec (.of k)).Opens).ι).1
      simpa using Scheme.Hom.resLE_comp_ι _ le_top
    rw [he, ← Category.assoc]
    infer_instance
  refine ⟨IsRegularLocalRing.of_ringEquiv e.symm, ?_, ringKrullDim_eq_of_ringEquiv e⟩
  letI := (π.stalkMap (i x)).hom.toAlgebra
  letI : Algebra ((Spec (.of k)).presheaf.stalk (π (i x))) (X.presheaf.stalk x) :=
    ((i ≫ π).stalkMap x).hom.toAlgebra
  have : Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (π (i x)))
      (X.presheaf.stalk x) := hsa.formallySmooth_stalkMap
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofRingEquiv (f := e) (fun a => by
    change (i.stalkMap x).hom ((π.stalkMap (i x)).hom a) = ((i ≫ π).stalkMap x).hom a
    rw [Scheme.Hom.stalkMap_comp]
    rfl)).symm

/-- A closed subscheme `X` of a smooth `k`-scheme `P`, smooth over `k` near `x` and of
codimension `c` in `P` at `x`, is cut out near `x` by `c` functions `f j` with linearly
independent differentials in `κ(x) ⊗ Ω_{P/k}` on an affine open neighbourhood of `i x`. -/
@[mmp "lem_mmp_foundation_smooth_closed_subscheme_local_equations"]
public theorem exists_affineOpen_ker_eq_span_linearIndependent_D
    {k : Type*} [Field k] {P X : Scheme} (π : P ⟶ Spec (.of k)) [Smooth π]
    (i : X ⟶ P) [IsClosedImmersion i] (x : X)
    (hx : ∃ V : X.Opens, x ∈ V ∧ Smooth (V.ι ≫ i ≫ π))
    (c : ℕ) (hc : ringKrullDim (P.presheaf.stalk (i x)) =
      ringKrullDim (X.presheaf.stalk x) + c) :
    ∃ (U : P.affineOpens) (hU : i x ∈ (U : P.Opens)) (f : Fin c → Γ(P, U)),
      i.ker.ideal U = Ideal.span (Set.range f) ∧
      letI : Algebra k Γ(P, U) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appLE ⊤ U le_top).hom.toAlgebra
      letI : Algebra Γ(P, U) (P.residueField (i x)) :=
        (P.evaluation U (i x) hU).hom.toAlgebra
      LinearIndependent (P.residueField (i x))
        (fun j ↦ (1 : P.residueField (i x)) ⊗ₜ[Γ(P, U)] KaehlerDifferential.D k Γ(P, U) (f j)) := by
  obtain ⟨V, hxV, hV⟩ := hx
  obtain ⟨hreg, hsm, hdim⟩ := stalk_quotient_ker_of_smooth π i hxV hV
  have hr : ringKrullDim (P.presheaf.stalk (i x)) =
      ringKrullDim (P.presheaf.stalk (i x) ⧸ IdealSheafData.stalk i.ker (i x)) + c := hdim ▸ hc
  obtain ⟨hcn, U, hU, hpU, xs, hloc, -, hcut⟩ :=
    MMP.Resolution.Bridges.exists_isLocalCoordinates_isCutOutByFirst_of_stalk π i.ker i.ker
      le_rfl (i x) hreg hreg hsm hr hr
  refine ⟨⟨U, hU⟩, hpU, fun j ↦ xs (Fin.castLE hcn j), ?_, ?_⟩
  · have hcut' := hcut ⟨U, hU⟩ le_rfl
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply] at hcut'
    rw [hcut', Set.range_comp', Fin.range_castLE]
  · obtain ⟨b, hb⟩ := MMP.Threefold.Resolution.exists_basis_D_of_isLocalCoordinates π hU xs hloc
    letI : Algebra k Γ(P, U) := MMP.Mori.sectionAlgebra π U
    letI : Algebra Γ(P, U) (P.residueField (i x)) := (P.evaluation U (i x) hpU).hom.toAlgebra
    convert ((b.baseChange (P.residueField (i x))).linearIndependent).comp _
      (Fin.castLE_injective hcn) using 1
    funext j
    simp [Module.Basis.baseChange_apply, hb]

end MMP.Foundations

/-! ### Factorization through the blowup of a fundamental point -/

namespace MMP.Resolution.Bridges

/-- A smooth surface over a field is an integral Noetherian scheme, regular of dimension two. -/
private theorem isIntegralRegularSurface_of_isSmoothSurface (k : Type u) [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : IsVariety k sY)
    (hYs : MMP.Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) :
    Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface Y := by
  have hreg := MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hYs
  have := ((isRegular_iff_regular_stalks Y).1 hreg).1
  have := hY.toQuasiCompact
  have := QuasiCompact.compactSpace_of_compactSpace sY
  exact ⟨hY.toIsIntegral, ⟨⟩, hreg, hYd⟩

/-- **Factorization through the blowup of a fundamental point.** Let `h : Y' ⟶ U` be a proper
birational morphism of smooth surfaces over a field `k`, and `P` a closed point of `U` such that
`h` restricts to an isomorphism over no open neighbourhood of `P`. Then `h` factors through the
blowup of `U` at `P`: there is `h'' : Y' ⟶ Bl_P U` with
`h'' ≫ Stacks.ResolutionOfSurfaces.pointBlowUpToBase hP = h`. See Stacks Tag 0C5R. -/
@[mmp "lem_mmp_foundation_surface_factor_through_selected_point_blowup"]
public theorem exists_comp_eq_pointBlowUpToBase_of_isSmoothSurface (k : Type u) [Field k]
    {U Y' : Scheme.{u}} {sU : U ⟶ Spec (.of k)} {sY' : Y' ⟶ Spec (.of k)}
    (hU : IsVariety k sU) (hUs : MMP.Mori.IsSmoothScheme sU) (hUd : topologicalKrullDim U = 2)
    (hY' : IsVariety k sY') (hY's : MMP.Mori.IsSmoothScheme sY')
    (hY'd : topologicalKrullDim Y' = 2) (h : Y' ⟶ U) (hh : h ≫ sU = sY') [IsProper h]
    (hb : IsBirational h) {P : U} (hP : IsClosed ({P} : Set U))
    (hPh : ∀ V : U.Opens, P ∈ V → ¬ IsIso (h ∣_ V)) :
    ∃ h'' : Y' ⟶ Stacks.ResolutionOfSurfaces.pointBlowUp hP,
      h'' ≫ Stacks.ResolutionOfSurfaces.pointBlowUpToBase hP = h :=
  Stacks.ResolutionOfSurfaces.exists_comp_eq_pointBlowUpToBase_of_not_mem_isomorphismLocus
    (isIntegralRegularSurface_of_isSmoothSurface k hU hUs hUd)
    (isIntegralRegularSurface_of_isSmoothSurface k hY' hY's hY'd) h ‹_› hb hP
    fun V hV hPV => hPh V hPV hV.1

end MMP.Resolution.Bridges

/-! ### Connected fibres of a proper birational morphism -/

attribute [mmp "lem_mmp_foundation_surface_resolution_connected_fibres" "2"]
  MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism

/-! ### Hadamard division for holomorphic functions -/

section Hadamard

open Filter Topology

namespace MMP.Analytic

/-- The monomial `zᵅ`. -/
private noncomputable abbrev mono {σ : Type*} (z : σ → ℂ) (α : σ →₀ ℕ) : ℂ :=
  α.prod fun j n => z j ^ n

private lemma norm_mono_le {σ : Type*} {z z' : σ → ℂ} (h : ∀ j, ‖z j‖ ≤ ‖z' j‖)
    (α : σ →₀ ℕ) : ‖mono z α‖ ≤ ‖mono z' α‖ := by
  unfold mono Finsupp.prod
  rw [norm_prod, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => by
    rw [norm_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h j) _

private lemma mono_add_single {σ : Type*} [DecidableEq σ] (z : σ → ℂ) (β : σ →₀ ℕ) (j : σ) :
    mono z (β + Finsupp.single j 1) = mono z β * z j := by
  unfold mono
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (h := fun x n => z x ^ n) (pow_zero _), pow_one]

open Classical in
/-- Some `i` with `α (Sum.inr i) ≠ 0`, if there is one. -/
private noncomputable def selectInr {ι : Type*} (α : (ι ⊕ ι) →₀ ℕ) : Option ι :=
  if h : ∃ i, α (Sum.inr i) ≠ 0 then some h.choose else none

private lemma selectInr_ne_zero {ι : Type*} {α : (ι ⊕ ι) →₀ ℕ} {i : ι}
    (h : selectInr α = some i) : α (Sum.inr i) ≠ 0 := by
  unfold selectInr at h
  split_ifs at h with h'
  cases h
  exact h'.choose_spec

private lemma selectInr_eq_none {ι : Type*} {α : (ι ⊕ ι) →₀ ℕ} (h : selectInr α = none)
    (i : ι) : α (Sum.inr i) = 0 := by
  unfold selectInr at h
  split_ifs at h with h'
  push Not at h'
  exact h' i

open Classical in
/-- The coefficients `c (β + eᵢ)` of the multi-indices whose selected variable is `i`. -/
private noncomputable def selectCoeff {ι : Type*} (c : ((ι ⊕ ι) →₀ ℕ) → ℂ) (i : ι)
    (β : (ι ⊕ ι) →₀ ℕ) : ℂ :=
  if selectInr (β + Finsupp.single (Sum.inr i) 1) = some i then
    c (β + Finsupp.single (Sum.inr i) 1) else 0

open Classical in
/-- The part of the series `∑ α, c α zᵅ` with no selected variable. -/
private noncomputable def selectRest {ι : Type*} (c : ((ι ⊕ ι) →₀ ℕ) → ℂ) (z : ι ⊕ ι → ℂ) :
    ℂ :=
  ∑' α, if selectInr α = none then c α * mono z α else 0

private lemma selectRest_eq {ι : Type*} (c : ((ι ⊕ ι) →₀ ℕ) → ℂ) (z : ι ⊕ ι → ℂ) :
    selectRest c z = selectRest c (Sum.elim (fun i => z (Sum.inl i)) 0) := by
  unfold selectRest
  refine tsum_congr fun α => ?_
  split_ifs with hα
  · congr 1
    refine Finsupp.prod_congr fun j hj => ?_
    cases j with
    | inl i => rfl
    | inr i => exact absurd (selectInr_eq_none hα i) (Finsupp.mem_support_iff.1 hj)
  · rfl

private lemma eq_selectRest_add {ι : Type*} [Fintype ι] {c : ((ι ⊕ ι) →₀ ℕ) → ℂ}
    {z : ι ⊕ ι → ℂ} {k : ℂ} (hk : HasSum (fun α => c α * mono z α) k) :
    k = selectRest c z + ∑ i, z (Sum.inr i) * ∑' β, selectCoeff c i β * mono z β := by
  classical
  have hsplit : ∀ α, c α * mono z α = (if selectInr α = none then c α * mono z α else 0) +
      ∑ i, (if selectInr α = some i then c α * mono z α else 0) := by
    intro α
    rcases h : selectInr α with _ | i0
    · simp
    · simp [Finset.sum_ite_eq]
  have hpiece : ∀ (P : ((ι ⊕ ι) →₀ ℕ) → Prop) [DecidablePred P],
      Summable fun α => if P α then c α * mono z α else 0 := by
    intro P _
    refine Summable.of_norm_bounded (summable_norm_iff.2 hk.summable) fun α => ?_
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      exact norm_nonneg _
  rw [← hk.tsum_eq, tsum_congr hsplit, Summable.tsum_add (hpiece _)
    (summable_sum fun i _ => hpiece _), Summable.tsum_finsetSum fun i _ => hpiece _, selectRest]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsupp : Function.support (fun α => if selectInr α = some i then c α * mono z α else 0) ⊆
      Set.range (· + Finsupp.single (Sum.inr i) 1) := by
    intro α hα
    have hs : selectInr α = some i := by
      by_contra hne
      exact hα (if_neg hne)
    refine ⟨α - Finsupp.single (Sum.inr i) 1, tsub_add_cancel_of_le ?_⟩
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.2 (selectInr_ne_zero hs)
  rw [← (add_left_injective (Finsupp.single (Sum.inr i) 1)).tsum_eq hsupp, mul_comm,
    ← tsum_mul_right]
  refine tsum_congr fun β => ?_
  simp only [selectCoeff]
  split_ifs
  · rw [mono_add_single]
    ring
  · simp

/-- A power series in the variables `(w, u)` converging near `0` to a function vanishing on
`u = 0` is a combination `∑ i, uᵢ Kᵢ` of power series `Kᵢ` converging near `0`. -/
private lemma exists_decomp {ι : Type*} [Fintype ι] (k : (ι ⊕ ι → ℂ) → ℂ)
    (c : ((ι ⊕ ι) →₀ ℕ) → ℂ)
    (hc : ∀ᶠ z in 𝓝 (0 : ι ⊕ ι → ℂ), HasSum (fun α => c α * mono z α) (k z))
    (hk0 : ∀ w : ι → ℂ, k (Sum.elim w 0) = 0) :
    ∃ K : ι → ((ι ⊕ ι) →₀ ℕ) → ℂ, (∀ i, ∀ᶠ z in 𝓝 (0 : ι ⊕ ι → ℂ),
      HasSum (fun β => K i β * mono z β) (∑' β, K i β * mono z β)) ∧
      ∀ᶠ z in 𝓝 (0 : ι ⊕ ι → ℂ), k z = ∑ i, z (Sum.inr i) * ∑' β, K i β * mono z β := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hc
  set ρ : ℝ := r / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  set z0 : ι ⊕ ι → ℂ := fun _ => (ρ : ℂ)
  have hz0j : ∀ j, ‖z0 j‖ = ρ := fun j => by simp [z0, abs_of_pos hρ]
  have hz0 : z0 ∈ Metric.ball 0 r := by
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hρ.le).2 fun j => (hz0j j).le) ?_
    linarith
  have hsum0 : Summable fun α => ‖c α * mono z0 α‖ :=
    summable_norm_iff.2 (hball z0 hz0).summable
  have hcomp : ∀ z ∈ Metric.ball (0 : ι ⊕ ι → ℂ) ρ, ∀ j, ‖z j‖ ≤ ‖z0 j‖ := by
    intro z hz j
    rw [mem_ball_zero_iff] at hz
    rw [hz0j j]
    exact (norm_le_pi_norm z j).trans hz.le
  have hKsum : ∀ i, ∀ z ∈ Metric.ball (0 : ι ⊕ ι → ℂ) ρ,
      Summable fun β => selectCoeff c i β * mono z β := by
    intro i z hz
    refine Summable.of_norm_bounded ((hsum0.comp_injective
      (add_left_injective (Finsupp.single (Sum.inr i) 1))).div_const ρ) fun β => ?_
    simp only [Function.comp_apply]
    rw [le_div_iff₀ hρ, mono_add_single, norm_mul, norm_mul, norm_mul, hz0j (Sum.inr i)]
    have h1 : ‖selectCoeff c i β‖ ≤ ‖c (β + Finsupp.single (Sum.inr i) 1)‖ := by
      unfold selectCoeff
      split_ifs <;> simp
    have h2 := norm_mono_le (hcomp z hz) β
    calc ‖selectCoeff c i β‖ * ‖mono z β‖ * ρ ≤
          ‖c (β + Finsupp.single (Sum.inr i) 1)‖ * ‖mono z0 β‖ * ρ := by gcongr
      _ = _ := by ring
  have hid : ∀ z ∈ Metric.ball (0 : ι ⊕ ι → ℂ) ρ,
      k z = selectRest c z + ∑ i, z (Sum.inr i) * ∑' β, selectCoeff c i β * mono z β :=
    fun z hz => eq_selectRest_add (hball z (Metric.ball_subset_ball (by linarith) hz))
  have hball_sub : ∀ z ∈ Metric.ball (0 : ι ⊕ ι → ℂ) ρ,
      (Sum.elim (fun i => z (Sum.inl i)) 0 : ι ⊕ ι → ℂ) ∈ Metric.ball 0 ρ := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun j => ?_) hz
    cases j with
    | inl i => exact norm_le_pi_norm z (Sum.inl i)
    | inr i => simp
  refine ⟨selectCoeff c, fun i => ?_, ?_⟩
  · filter_upwards [Metric.ball_mem_nhds 0 hρ] with z hz
    exact (hKsum i z hz).hasSum
  · filter_upwards [Metric.ball_mem_nhds 0 hρ] with z hz
    have h0 := hid _ (hball_sub z hz)
    rw [hk0] at h0
    simp only [Sum.elim_inr, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at h0
    rw [hid z hz, selectRest_eq c z, ← h0, zero_add]

/-- The Hadamard decomposition `h y - h y' = ∑ i, (y i - y' i) * H i (y, y')` near `(b, b)`. -/
private lemma exists_hadamard {ι : Type*} [Fintype ι] {h : (ι → ℂ) → ℂ} {b : ι → ℂ}
    (hh : ∀ᶠ y in 𝓝 b, DifferentiableAt ℂ h y) :
    ∃ H : ι → (ι → ℂ) × (ι → ℂ) → ℂ,
      (∀ i, ∀ᶠ p in 𝓝 (b, b), DifferentiableAt ℂ (H i) p) ∧
      ∀ᶠ p in 𝓝 (b, b), h p.1 - h p.2 = ∑ i, (p.1 i - p.2 i) * H i p := by
  have C := (MMP.Analytic.eventually_differentiableAt_iff_exists_hasSum_mvPowerSeries.{_, 0}
    (0 : ι ⊕ ι → ℂ)).1
  set P₁ : (ι ⊕ ι → ℂ) → ι → ℂ := fun z i => b i + z (Sum.inl i) + z (Sum.inr i)
  set P₂ : (ι ⊕ ι → ℂ) → ι → ℂ := fun z i => b i + z (Sum.inl i)
  have hP₁d : Differentiable ℂ P₁ := by fun_prop
  have hP₂d : Differentiable ℂ P₂ := by fun_prop
  have hP₁t : Tendsto P₁ (𝓝 0) (𝓝 b) := by
    simpa [P₁] using hP₁d.continuous.tendsto (0 : ι ⊕ ι → ℂ)
  have hP₂t : Tendsto P₂ (𝓝 0) (𝓝 b) := by
    simpa [P₂] using hP₂d.continuous.tendsto (0 : ι ⊕ ι → ℂ)
  set k : (ι ⊕ ι → ℂ) → ℂ := fun z => h (P₁ z) - h (P₂ z)
  have hkd : ∀ᶠ z in 𝓝 (0 : ι ⊕ ι → ℂ), DifferentiableAt ℂ k z := by
    filter_upwards [hP₁t.eventually hh, hP₂t.eventually hh] with z h₁ h₂
    exact (h₁.comp z (hP₁d z)).sub (h₂.comp z (hP₂d z))
  have hmono : ∀ (z : ι ⊕ ι → ℂ) (α : (ι ⊕ ι) →₀ ℕ),
      (α.prod fun i k => (z i - (0 : ι ⊕ ι → ℂ) i) ^ k) = mono z α := fun z α => by simp [mono]
  obtain ⟨a, ha⟩ := (C k).1 hkd
  simp only [hmono] at ha
  obtain ⟨K, hK, hid⟩ := exists_decomp k (fun α => MvPowerSeries.coeff α a) ha
    (fun w => by simp [k, P₁, P₂])
  set Kf : ι → (ι ⊕ ι → ℂ) → ℂ := fun i z => ∑' β, K i β * mono z β
  have hKf : ∀ i, ∀ᶠ z in 𝓝 (0 : ι ⊕ ι → ℂ), DifferentiableAt ℂ (Kf i) z := fun i =>
    (C (Kf i)).2 ⟨(K i : MvPowerSeries (ι ⊕ ι) ℂ), by
      filter_upwards [hK i] with z hz
      simp only [hmono]
      exact hz⟩
  set e : (ι → ℂ) × (ι → ℂ) → ι ⊕ ι → ℂ :=
    fun p => Sum.elim (fun i => p.2 i - b i) (fun i => p.1 i - p.2 i)
  have hed : Differentiable ℂ e := by
    refine differentiable_pi.2 fun j => ?_
    cases j with
    | inl i => simp only [e, Sum.elim_inl]; fun_prop
    | inr i => simp only [e, Sum.elim_inr]; fun_prop
  have het : Tendsto e (𝓝 (b, b)) (𝓝 0) := by
    convert hed.continuous.tendsto (b, b) using 2
    funext j
    cases j <;> simp [e]
  refine ⟨fun i p => Kf i (e p), fun i => ?_, ?_⟩
  · filter_upwards [het.eventually (hKf i)] with p hp
    exact hp.comp p (hed p)
  · filter_upwards [het.eventually hid] with p hp
    have h1 : P₁ (e p) = p.1 := funext fun i => by simp [P₁, e]
    have h2 : P₂ (e p) = p.2 := funext fun i => by simp [P₂, e]
    simp only [k, h1, h2] at hp
    rw [hp]
    rfl

/-- Given a Hadamard decomposition of `h` near `(b, b)`, the germ of `h ∘ F - h ∘ G` lies in
every ideal of `holGerms a` containing the component germs of `F - G`. -/
private lemma comp_sub_comp_mem {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {h : (ι → ℂ) → ℂ} {b : ι → ℂ} {H : ι → (ι → ℂ) × (ι → ℂ) → ℂ}
    (hHd : ∀ i, ∀ᶠ p in 𝓝 (b, b), DifferentiableAt ℂ (H i) p)
    (hHid : ∀ᶠ p in 𝓝 (b, b), h p.1 - h p.2 = ∑ i, (p.1 i - p.2 i) * H i p)
    {a : E} {F G : E → ι → ℂ} (hF : ∀ᶠ x in 𝓝 a, DifferentiableAt ℂ F x)
    (hG : ∀ᶠ x in 𝓝 a, DifferentiableAt ℂ G x) (hFa : F a = b) (hGa : G a = b)
    {I : Ideal (holGerms a)}
    (hI : ∀ i, ∃ g ∈ I, (g : Germ (𝓝 a) ℂ) = ↑(fun x => F x i - G x i)) :
    ∃ g ∈ I, (g : Germ (𝓝 a) ℂ) = ↑(fun x => h (F x) - h (G x)) := by
  choose g hgI hg using hI
  have hT : Tendsto (fun x => (F x, G x)) (𝓝 a) (𝓝 (b, b)) := by
    simpa [hFa, hGa] using
      (hF.self_of_nhds.continuousAt.prodMk hG.self_of_nhds.continuousAt).tendsto
  have hmem : ∀ i, ((fun x => H i (F x, G x) : E → ℂ) : Germ (𝓝 a) ℂ) ∈ holGerms a := fun i =>
    coe_mem_holGerms <| by
      filter_upwards [hT.eventually (hHd i), hF, hG] with x h1 h2 h3
      exact h1.comp x (h2.prodMk h3)
  refine ⟨∑ i, g i * ⟨_, hmem i⟩, Ideal.sum_mem _ fun i _ => I.mul_mem_right _ (hgI i), ?_⟩
  push_cast
  simp_rw [hg]
  change ∑ i, Germ.coeRingHom (𝓝 a) ((fun x => F x i - G x i) * fun x => H i (F x, G x)) = _
  rw [← map_sum]
  refine Germ.coe_eq.2 ?_
  filter_upwards [hT.eventually hHid] with x hx
  simp [hx]

/-- **Hadamard division.** A function `h` holomorphic near `b : ι → ℂ` satisfies
`h y - h y' = ∑ i, (y i - y' i) * H i (y, y')` near `(b, b)` for some `H i` holomorphic near
`(b, b)`. Consequently, for maps `F G : E → ι → ℂ` holomorphic near `a` with `F a = G a = b`
whose component differences have germs in an ideal `I` of `holGerms a`, the germ of
`h ∘ F - h ∘ G` lies in `I`. -/
@[mmp "lem_mmp_gaga_holomorphic_hadamard_division"]
public theorem exists_sub_eq_sum_sub_mul_and_comp_sub_comp_mem
    {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {h : (ι → ℂ) → ℂ} {b : ι → ℂ} (hh : ∀ᶠ y in 𝓝 b, DifferentiableAt ℂ h y) :
    (∃ H : ι → (ι → ℂ) × (ι → ℂ) → ℂ,
        (∀ i, ∀ᶠ p in 𝓝 (b, b), DifferentiableAt ℂ (H i) p) ∧
        ∀ᶠ p in 𝓝 (b, b), h p.1 - h p.2 = ∑ i, (p.1 i - p.2 i) * H i p) ∧
      ∀ (a : E) (F G : E → ι → ℂ),
        (∀ᶠ x in 𝓝 a, DifferentiableAt ℂ F x) → (∀ᶠ x in 𝓝 a, DifferentiableAt ℂ G x) →
        F a = b → G a = b → ∀ I : Ideal (holGerms a),
        (∀ i, ∃ g ∈ I, (g : Germ (𝓝 a) ℂ) = ↑(fun x => F x i - G x i)) →
        ∃ g ∈ I, (g : Germ (𝓝 a) ℂ) = ↑(fun x => h (F x) - h (G x)) := by
  obtain ⟨H, hHd, hHid⟩ := exists_hadamard hh
  exact ⟨⟨H, hHd, hHid⟩, fun _ _ _ hF hG hFa hGa _ => comp_sub_comp_mem hHd hHid hF hG hFa hGa⟩

end MMP.Analytic

end Hadamard

/-! ### Products of a complex variety with the projective line -/

namespace MMP.Fourfold

open Limits Stacks.AlgebraicGeometry.ProjPolyChart

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every irreducible subset of a closed set `Z` lies in a maximal irreducible subset of `Z`. -/
private theorem exists_maximal_isIrreducible_subset {Z s : Set X} (hs : IsIrreducible s)
    (hsZ : s ⊆ Z) : ∃ t, s ⊆ t ∧ Maximal (fun t ↦ IsIrreducible t ∧ t ⊆ Z) t := by
  obtain ⟨m, hsm, hm⟩ :=
    zorn_subset_nonempty { t : Set X | IsPreirreducible t ∧ t ⊆ Z }
      (fun c hc hcc _ =>
        ⟨⋃₀ c, ⟨fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ =>
          let ⟨p, hpc, hyp⟩ := Set.mem_sUnion.1 hy
          let ⟨q, hqc, hxq⟩ := Set.mem_sUnion.1 hx
          Or.casesOn (hcc.total hpc hqc)
            (fun hpq : p ⊆ q =>
              let ⟨x, hxp, hxuv⟩ := (hc hqc).1 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
              ⟨x, Set.mem_sUnion_of_mem hxp hqc, hxuv⟩)
            fun hqp : q ⊆ p =>
            let ⟨x, hxp, hxuv⟩ := (hc hpc).1 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
            ⟨x, Set.mem_sUnion_of_mem hxp hpc, hxuv⟩,
          Set.sUnion_subset fun t ht ↦ (hc ht).2⟩,
          fun _ hxc => Set.subset_sUnion_of_mem hxc⟩)
      s ⟨hs.2, hsZ⟩
  exact ⟨m, hsm, ⟨⟨hs.1.mono hsm, hm.prop.1⟩, hm.prop.2⟩, fun u hu hmu ↦ hm.2 ⟨hu.1.2, hu.2⟩ hmu⟩

/-- A maximal irreducible subset of a closed set is closed. -/
private theorem isClosed_of_maximal {Z T : Set X} (hZ : IsClosed Z)
    (hT : Maximal (fun T ↦ IsIrreducible T ∧ T ⊆ Z) T) : IsClosed T := by
  rw [← closure_subset_iff_isClosed]
  exact hT.2 ⟨hT.1.1.closure, closure_minimal hT.1.2 hZ⟩ subset_closure

/-- For a continuous surjection `p` along which preimages of irreducible sets are irreducible,
the maximal irreducible subsets of `p ⁻¹' Z` are the preimages of those of `Z`, for `Z`
closed. -/
private theorem maximal_preimage_eq {p : X → Y} (hp : Continuous p)
    (hs : Function.Surjective p) (hirr : ∀ T, IsIrreducible T → IsIrreducible (p ⁻¹' T))
    {Z : Set Y} (hZ : IsClosed Z) :
    {U : Set X | Maximal (fun U ↦ IsIrreducible U ∧ U ⊆ p ⁻¹' Z) U} =
      Set.preimage p '' {T : Set Y | Maximal (fun T ↦ IsIrreducible T ∧ T ⊆ Z) T} := by
  ext U
  constructor
  · intro hU
    obtain ⟨T, hT1, hT⟩ := exists_maximal_isIrreducible_subset
      (hU.1.1.image p hp.continuousOn).closure (closure_minimal (Set.image_subset_iff.2 hU.1.2) hZ)
    have hUT : U ⊆ p ⁻¹' T := fun x hx ↦ hT1 (subset_closure ⟨x, hx, rfl⟩)
    exact ⟨T, hT, (hU.2 ⟨hirr T hT.1.1, Set.preimage_mono hT.1.2⟩ hUT).antisymm hUT⟩
  · rintro ⟨T, hT, rfl⟩
    refine ⟨⟨hirr T hT.1.1, Set.preimage_mono hT.1.2⟩, fun U hU hTU ↦ ?_⟩
    have hTpU : T ⊆ p '' U := (Set.image_preimage_eq T hs).symm.subset.trans (Set.image_mono hTU)
    exact Set.image_subset_iff.1
      (hT.2 ⟨hU.1.image p hp.continuousOn, Set.image_subset_iff.2 hU.2⟩ hTpU)

end Topology

/-- The projective line `Proj ℂ[T₀, T₁]` has dimension one. -/
private theorem topologicalKrullDim_projectiveLine :
    topologicalKrullDim (AlgebraicGeometry.Proj (polyGrading ℂ 1)) = 1 := by
  change topologicalKrullDim
    (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) ℂ)) = 1
  rw [Stacks.ProjectiveSpace.topologicalKrullDim_proj]
  simp

/-- For a closed subset `T` of a complex variety `S`, the preimage of `T` under the first
projection `S × ℙ¹ → S` has dimension `dim T + 1`: it is homeomorphic to `T' × ℙ¹` for the
closed subscheme `T'` of `S` with support `T`. -/
private theorem topologicalKrullDim_preimage_fst {S : Scheme.{0}} [S.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (S ↘ Spec (.of ℂ))] {T : Set S} (hT : IsClosed T) :
    topologicalKrullDim (pullback.fst (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1) ⁻¹' T) =
      topologicalKrullDim T + 1 := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff ℂ 1
  set f := pullback.fst (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1)
  let i := (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩).subschemeι
  have hi : Set.range i = T := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let ψ := pullbackRightPullbackFstIso (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1) i
  let φ := ψ.inv ≫ pullback.snd i f
  have hφ : Set.range φ = f ⁻¹' T := by
    simp only [φ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 ψ.inv.surjective, Set.image_univ]
    rw [Scheme.Pullback.range_snd, hi]
  let e := φ.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hφ)
  let e' := i.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hi)
  rw [← IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph, topologicalKrullDim_pullback ℂ,
    IsHomeomorph.topologicalKrullDim_eq e' e'.isHomeomorph, topologicalKrullDim_projectiveLine]

/-- The product of a separated complex variety `A` with `ℙ¹` is a separated complex variety of
dimension `dim A + 1`; and for a closed subset `Z` of a separated complex variety `S`, the
irreducible components of `pr₁⁻¹ Z ⊆ S × ℙ¹` are exactly the preimages `pr₁⁻¹ Aₗ` of the
irreducible components `Aₗ` of `Z`, pairwise distinct, with `dim pr₁⁻¹ Aₗ = dim Aₗ + 1`. -/
@[mmp "lem_mmp_indexd_product_components"]
public theorem isVariety_product_projectiveLine_and_irreducibleComponents_preimage :
    (∀ (A : Scheme.{0}) [A.Over (Spec (.of ℂ))] [IsIntegral A]
        [LocallyOfFiniteType (A ↘ Spec (.of ℂ))] [QuasiCompact (A ↘ Spec (.of ℂ))]
        [IsSeparated (A ↘ Spec (.of ℂ))],
      let p := pullback.fst (A ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1) ≫ A ↘ Spec (.of ℂ)
      IsIntegral (pullback (A ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1) : Scheme.{0}) ∧
        LocallyOfFiniteType p ∧ QuasiCompact p ∧ IsSeparated p ∧
        topologicalKrullDim (pullback (A ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1) : Scheme.{0}) =
          topologicalKrullDim A + 1) ∧
    (∀ (S : Scheme.{0}) [S.Over (Spec (.of ℂ))] [IsIntegral S]
        [LocallyOfFiniteType (S ↘ Spec (.of ℂ))] [QuasiCompact (S ↘ Spec (.of ℂ))]
        [IsSeparated (S ↘ Spec (.of ℂ))] (Z : Set S), IsClosed Z →
      let pr : (pullback (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1) : Scheme.{0}) → S :=
        pullback.fst (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1)
      {T : Set (pullback (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1) : Scheme.{0}) |
          Maximal (fun T ↦ IsIrreducible T ∧ T ⊆ pr ⁻¹' Z) T} =
        Set.preimage pr '' {T : Set S | Maximal (fun T ↦ IsIrreducible T ∧ T ⊆ Z) T} ∧
      Set.InjOn (Set.preimage pr) {T : Set S | Maximal (fun T ↦ IsIrreducible T ∧ T ⊆ Z) T} ∧
      ∀ T : Set S, Maximal (fun T ↦ IsIrreducible T ∧ T ⊆ Z) T →
        topologicalKrullDim (pr ⁻¹' T) = topologicalKrullDim T + 1) := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff ℂ 1
  have : GeometricallyIrreducible (projToSpecCoeff ℂ 1) :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed ℂ _ _
  refine ⟨fun A _ _ _ _ _ ↦ ?_, fun S _ _ _ _ _ Z hZ ↦ ?_⟩
  · have hA : IsVariety ℂ (A ↘ Spec (.of ℂ)) := { }
    have hP : IsVariety ℂ (projToSpecCoeff ℂ 1) := { }
    have hV := isVariety_pullback ℂ (A ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1)
    refine ⟨hV.toIsIntegral, hV.toLocallyOfFiniteType, hV.toQuasiCompact, hV.toIsSeparated, ?_⟩
    rw [topologicalKrullDim_pullback ℂ, topologicalKrullDim_projectiveLine]
  · intro pr
    set f := pullback.fst (S ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1)
    refine ⟨maximal_preimage_eq f.continuous f.surjective
        (fun T hT ↦ f.isIrreducible_preimage f.isOpenMap hT) hZ,
      fun T _ T' _ h ↦ Set.preimage_injective.2 f.surjective h,
      fun T hT ↦ topologicalKrullDim_preimage_fst (isClosed_of_maximal hZ hT)⟩

end MMP.Fourfold

end
