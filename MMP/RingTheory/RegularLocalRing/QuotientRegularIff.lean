module

public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import MMP.AlgebraicGeometry.Divisor.Canonical.PluricanonicalForms
public import MMP.AlgebraicGeometry.MMP.Fourfold.AlgebraicLemmas
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelianSmall

/-!
# Foundational results: linear systems, smooth loci, valuations, regular rings

This file collects foundational facts used throughout the minimal model program.

* A globally generated invertible sheaf `ℒ` on a proper integral `k`-scheme `X`, with a basis
  `(sᵢ)` of `H⁰(X, ℒ)`, defines a `k`-morphism `φ : X → ℙ(k^ι)` with `φ^*𝒪(1) ≅ ℒ` carrying
  `φ^*xᵢ` to `sᵢ`; its image is closed and irreducible.
* For a smooth morphism `h : Y ⟶ X` of schemes over a field `k`, `Y` is smooth over `k` at `y`
  iff `X` is smooth over `k` at `h y`; hence `Sing Y = h⁻¹(Sing X)`.
* Over a field, the composite of projective morphisms of separated algebraic schemes with
  quasi-compact final target is projective.
* If `g : X₁ ⟶ X` is a proper dominant morphism of varieties and `R` a valuation ring of `k(X₁)`
  dominating `𝒪_{X,x}`, then `R` dominates `𝒪_{X₁,x₁}` for some `x₁` over `x`.
* For a Noetherian local ring `(R, 𝔪)` and `g ∈ 𝔪` outside every minimal prime, `R ⧸ (g)` is
  regular iff `R` is regular and `g ∉ 𝔪 ^ 2`.
* A nonempty open of the smooth locus of a finite type `ℤ`-algebra `R` contains closed points of
  arbitrarily large residue characteristic `p`, at which the residue map lifts to `W₂(k)`.
* The higher direct images of sheaves of modules along a morphism of ringed sites form a
  cohomological δ-functor.

## Main results

* `MMP.Mori.exists_morphism_projectiveSpace_of_isGloballyGenerated`
* `MMP.Mori.smoothLocus_comp_of_smooth`
* `MMP.isProjective_comp_of_isSeparatedAlgebraicScheme`
* `MMP.Mori.exists_map_eq_and_dominates_of_isProper`
* `MMP.isRegularLocalRing_quotient_span_singleton_iff`
* `MMP.exists_isMaximal_mem_smoothLocus_witt_lift`
* `MMP.SheafOfModules.exists_deltaFunctor_functor_eq_pushforward_rightDerived`

## Implementation notes

The morphism to projective space is stated for an invertible sheaf `ℒ`, which covers
`ℒ = 𝒪_X(M)` for a Cartier divisor `M`
(`MMP.Mori.Divisor.IsCartier.isInvertibleModule_divisorialSheaf`); the basis may be indexed by any
type, which properness forces to be finite. The sections generate `ℒ` at every point: on a
trivializing open, global generation writes the local frame as `∑ rᵢ sᵢ`, so some `sᵢ` has a unit
germ. Since `ℙ` is separated over `k`, `φ` is proper, so its image is closed.

Descent of smoothness along a smooth `h` restricts `h` to an open `U` on which `Y` is smooth;
`h(U)` is open as smooth morphisms are universally open, and smoothness descends along the smooth
surjection `U ⟶ h(U)`. The permanence properties of smooth morphisms themselves are Mathlib's
(`AlgebraicGeometry.smooth_comp`, `AlgebraicGeometry.UniversallyOpen.of_flat`, …).

Domination of a local ring `A ⊆ K` by a valuation subring `R` of `K` is spelled with
`R.valuation`: `≤ 1` on `A` and `< 1` on its maximal ideal. The centre is produced by the
valuative criterion applied to the square with top side the generic point `Spec k(X₁) ⟶ X₁`.

For regular hypersurface sections, write `μ` for the minimal number of generators. Cutting by `g`
lowers the dimension by one, `μ(𝔪) ≤ μ(𝔪/(g)) + 1`, `μ(𝔪) ≤ μ(𝔪/(g))` when `g ∈ 𝔪 ^ 2`
(Nakayama), and `μ(𝔪/(g)) + 1 ≤ μ(𝔪)` when `g ∉ 𝔪 ^ 2` (exchange a generator for `g`).

`W₂(k)` is `TruncatedWittVector p 2 k` and the reduction `W₂(k) → k` is the zeroth coordinate;
its kernel squares to zero, so formal smoothness of `R_𝔪` over `ℤ` lifts the residue map.
Smoothness over `ℤ` forces flatness, so a nonempty open of the smooth locus meets `D(N!)`, and
`R` being Jacobson it contains a closed point there.

The δ-functor statement is made for a morphism of ringed sites; the ringed-space case is the one
on the sites of opens. Additivity of `SheafOfModules.pushforward φ` holds by `rfl`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.59
* [R. Hartshorne, *Algebraic geometry*][Har77], II.7.1
* [Kollár, *Lectures on resolution of singularities*][kollar2007]
* [EGA IV, 17.7.7]
* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004]
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
* [Deligne, Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*][DI87]
* [The Stacks Project, Tags 01W8, 010Q, 01E0][stacks-project]
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)` and
-- `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel

/-! ### The morphism of a globally generated line bundle -/

section FreeSystem

open TopologicalSpace
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule
  degreeOneElement grading morphismOfGeneratingSections twistIsoOfGeneratingSections
  twistIso_pullbackSectionOne)
open Stacks.AlgebraicGeometry.ProjDegreeOneRepresents (pullbackTwistOne pullbackSectionOne)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare
  (morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec)

attribute [local instance] globalSectionsModule

namespace MMP.Mori

/-- The trivializing function of a global section commutes with restriction to a smaller open
inside the trivializing open. -/
private theorem triv_res_trivTop {X : Scheme.{u}} {L : X.Modules} {V W : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf L.val V) (hWV : W ≤ V) (s : Γ(L, ⊤)) :
    Stacks.NonvanishingOpen.triv t (homOfLE hWV) (L.presheaf.map (homOfLE le_top).op s) =
      X.presheaf.map (homOfLE hWV).op (Stacks.NonvanishingOpen.trivTop t s) := by
  rw [Stacks.NonvanishingOpen.trivTop, ← Stacks.NonvanishingOpen.triv_res t (𝟙 _) (homOfLE hWV),
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- A globally generated invertible module is generated, at every point, by a global section
nonvanishing there: on a trivializing open around `x`, global generation writes the local frame
as `∑ rᵢ sᵢ`, so `1 = ∑ rᵢ · triv(sᵢ)` near `x`, and some `triv(sᵢ)` has a unit germ. -/
private theorem exists_mem_nonvanishingOpen {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : MMP.Intersection.IsGloballyGenerated L)
    (x : X) : ∃ s : Γ(L, ⊤), x ∈ nonvanishingOpen X L s := by
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 L
  obtain ⟨z, hz⟩ : ∃ z : X, x ∈ V z := Opens.mem_iSup.mp (hV ▸ Opens.mem_top x)
  obtain ⟨t⟩ := htriv z
  obtain ⟨W, hWV, hxW, n, s, r, hsum⟩ :=
    hL x (Set.mem_univ x) (V z) hz (Stacks.NonvanishingOpen.basis t)
  have key : (1 : Γ(X, W)) = ∑ i, r i *
      X.presheaf.map (homOfLE hWV).op (Stacks.NonvanishingOpen.trivTop t (s i)) := by
    rw [← Stacks.NonvanishingOpen.triv_res_basis t (homOfLE hWV), hsum]
    refine (map_sum (AddMonoidHom.mk' (Stacks.NonvanishingOpen.triv t (homOfLE hWV))
      (Stacks.NonvanishingOpen.triv_add t _)) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [AddMonoidHom.mk'_apply, Stacks.NonvanishingOpen.triv_smul, triv_res_trivTop]
  have hgerm := congrArg (X.presheaf.germ W x hxW).hom key
  simp only [map_one, map_sum, map_mul, TopCat.Presheaf.germ_res_apply] at hgerm
  by_contra hne
  push Not at hne
  refine IsLocalRing.notMem_maximalIdeal.mpr isUnit_one (hgerm ▸ Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr fun hu => hne (s i) ?_))
  exact (Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit t (s i) hz).mpr hu

/-- **The morphism of a globally generated line bundle.** On a proper integral `k`-scheme `X`,
an invertible globally generated `𝒪_X`-module `L` with a `k`-basis `(bᵢ)_{i ∈ ι}` of `H⁰(X, L)`
admits a `k`-morphism `φ : X ⟶ ℙ(k^ι)` and an isomorphism `e : φ^*𝒪(1) ≅ L` sending the pull-back
of each coordinate section `xᵢ` to `bᵢ`; the image of `φ` is closed and irreducible. -/
@[mmp "lem_mmp_foundation_km_free_system_morphism"]
theorem exists_morphism_projectiveSpace_of_isGloballyGenerated (k : Type u) [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X] [IsProper (X ↘ Spec (.of k))]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : MMP.Intersection.IsGloballyGenerated L)
    {ι : Type u} (b : Module.Basis ι k Γ(L, ⊤)) :
    ∃ φ : X ⟶ projectiveSpaceOfModule k (ι →₀ k),
      φ.IsOver (Spec (.of k)) ∧
      ∃ e : pullbackTwistOne (grading k (ι →₀ k)) φ ≅ L,
        (∀ i : ι, e.hom.app ⊤ (pullbackSectionOne (grading k (ι →₀ k)) φ
            (degreeOneElement k (ι →₀ k) (Finsupp.single i 1))) = b i) ∧
        IsClosed (Set.range φ.base) ∧ IsIrreducible (Set.range φ.base) := by
  have hψ : ⨆ v : ι →₀ k, nonvanishingOpen X L (b.repr.symm.toLinearMap v) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨s, hs⟩ := exists_mem_nonvanishingOpen L hL x
    exact Opens.mem_iSup.mpr ⟨b.repr s, by simpa using hs⟩
  let φ := morphismOfGeneratingSections k (ι →₀ k) L b.repr.symm.toLinearMap hψ
  have hover : φ ≫ projectiveSpaceOfModuleToSpec k (ι →₀ k) = X ↘ Spec (.of k) :=
    morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec _ hψ
  have : IsSeparated (projectiveSpaceOfModuleToSpec k (ι →₀ k)) := by
    unfold projectiveSpaceOfModuleToSpec
    infer_instance
  have : IsProper (φ ≫ projectiveSpaceOfModuleToSpec k (ι →₀ k)) := hover ▸ inferInstance
  have : IsProper φ := IsProper.of_comp φ (projectiveSpaceOfModuleToSpec k (ι →₀ k))
  refine ⟨φ, ⟨hover⟩, twistIsoOfGeneratingSections k (ι →₀ k) L b.repr.symm.toLinearMap hψ,
    fun i => ?_, φ.isClosedMap.isClosed_range, ?_⟩
  · rw [twistIso_pullbackSectionOne]
    simp
  · rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ X).image _ φ.continuous.continuousOn

end MMP.Mori

end FreeSystem

/-! ### Smoothness over a field along a smooth morphism -/

namespace MMP.Mori

/-- Smoothness at a point over a base is detected along a smooth morphism. -/
private theorem mem_smoothLocus_comp_iff {S X Y : Scheme} (sX : X ⟶ S) (h : Y ⟶ X) [Smooth h]
    (y : Y) : y ∈ smoothLocus (h ≫ sX) ↔ h.base y ∈ smoothLocus sX := by
  rw [mem_smoothLocus_iff, mem_smoothLocus_iff]
  refine ⟨fun ⟨U, hyU, hU⟩ => ?_, fun ⟨V, hyV, hV⟩ => ⟨h ⁻¹ᵁ V, hyV, ?_⟩⟩
  · have : UniversallyOpen h := UniversallyOpen.of_flat h
    let V : X.Opens := ⟨_, h.isOpenMap _ U.2⟩
    have e : U ≤ h ⁻¹ᵁ V := fun z hz => ⟨z, hz, rfl⟩
    have hf : h.resLE V U e ≫ V.ι = U.ι ≫ h := Scheme.Hom.resLE_comp_ι _ _
    have : Surjective (h.resLE V U e) :=
      ⟨fun ⟨_, z, hz, rfl⟩ => ⟨⟨z, hz⟩, Subtype.ext (by simp)⟩⟩
    have : Smooth (h.resLE V U e ≫ V.ι ≫ sX) := by rwa [← Category.assoc, hf, Category.assoc]
    exact ⟨V, e hyU, Stacks.Smooth.smooth_of_comp_surjective_smooth (h.resLE V U e) (V.ι ≫ sX)⟩
  · rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι h (le_refl (h ⁻¹ᵁ V)), Category.assoc]
    infer_instance

/-- **Smoothness over a field along a smooth morphism.** If `h : Y ⟶ X` is smooth and `X`, `Y`
are of finite type over a field `k`, then `Y` is smooth over `k` at `y` iff `X` is smooth over
`k` at `h y`; consequently `h⁻¹(Sing X) = Sing Y`. -/
@[mmp "lem_mmp_foundation_kr_smooth_morphism_basics"]
theorem smoothLocus_comp_of_smooth {k : Type*} [Field k] {X Y : Scheme}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (h : Y ⟶ X) [Smooth h] [QuasiCompact (h ≫ sX)] :
    (∀ y : Y, y ∈ smoothLocus (h ≫ sX) ↔ h.base y ∈ smoothLocus sX) ∧
      (singularLocus (h ≫ sX) : Set Y) = h.base ⁻¹' (singularLocus sX : Set X) :=
  ⟨mem_smoothLocus_comp_iff sX h, Set.ext fun y => (mem_smoothLocus_comp_iff sX h y).not⟩

end MMP.Mori

/-! ### Composites of projective morphisms -/

namespace MMP

open MMP.Intersection in
/-- Over a field `K`, the composite of projective morphisms `g : W'' ⟶ W'` and `h : W' ⟶ W`
between separated algebraic `K`-schemes, with `W` quasi-compact, is projective. -/
@[mmp "lem_mmp_foundation_laz_ega_projective_composite"]
theorem isProjective_comp_of_isSeparatedAlgebraicScheme (K : Type u) [Field K]
    {W'' W' W : Scheme.{u}} [W''.Over (Spec (.of K))] [W'.Over (Spec (.of K))]
    [W.Over (Spec (.of K))] [IsSeparatedAlgebraicScheme K W'']
    [IsSeparatedAlgebraicScheme K W'] [hW : IsSeparatedAlgebraicScheme K W] [CompactSpace W]
    {g : W'' ⟶ W'} {h : W' ⟶ W} (hg : IsProjective g) (hh : IsProjective h) :
    IsProjective (g ≫ h) :=
  have : IsSeparated (W ↘ Spec (.of K)) := hW.isSeparated
  have : QuasiSeparatedSpace W := quasiSeparatedSpace_of_quasiSeparated (W ↘ Spec (.of K))
  hg.comp hh

end MMP

/-! ### Centres of valuations through proper dominant morphisms -/

namespace MMP.Mori

open IsLocalRing

/-- A morphism `l : Spec R ⟶ X₁` from the spectrum of a valuation ring of `k(X₁)` that restricts
to the generic point on `Spec k(X₁)` has a centre: `R` dominates the local ring of `X₁` at the
image of the closed point. -/
private lemma dominates_stalk_closedPoint {X₁ : Scheme.{u}} [IsIntegral X₁]
    (R : ValuationSubring X₁.functionField) (l : Spec (.of R) ⟶ X₁)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap R X₁.functionField)) ≫ l =
      X₁.fromSpecStalk (genericPoint X₁)) :
    (∀ a : X₁.presheaf.stalk (l (closedPoint R)),
      R.valuation (algebraMap _ X₁.functionField a) ≤ 1) ∧
    ∀ a ∈ maximalIdeal (X₁.presheaf.stalk (l (closedPoint R))),
      R.valuation (algebraMap _ X₁.functionField a) < 1 := by
  let ψ := Scheme.stalkClosedPointTo l
  have key : ψ ≫ CommRingCat.ofHom (algebraMap R X₁.functionField) =
      X₁.presheaf.stalkSpecializes ((genericPoint_spec X₁).specializes (Set.mem_univ _)) := by
    apply Spec.map_injective
    rw [← cancel_mono (X₁.fromSpecStalk _), Spec.map_comp, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have key' : ∀ a, algebraMap _ X₁.functionField a = ((ψ a : R) : X₁.functionField) :=
    fun a ↦ (congrArg (fun f ↦ f.hom a) key).symm
  refine ⟨fun a ↦ ?_, fun a ha ↦ ?_⟩
  · rw [key', R.valuation_le_one_iff]; exact (ψ a).2
  · rw [key']; exact (R.valuation_lt_one_iff _).1 (map_nonunit ψ.hom a ha)

/-- Let `g : X₁ ⟶ X` be a proper dominant morphism of `k`-varieties and `R` a valuation ring of
`k(X₁)` containing `k`. If `𝒪_{X,x}` is dominated by `R ∩ k(X)` (through `g^*`), then there is
`x₁ ∈ X₁` with `g x₁ = x` such that `𝒪_{X₁,x₁}` is dominated by `R`. -/
@[mmp "lem_mmp_foundation_proper_valuation_center_exists"]
theorem exists_map_eq_and_dominates_of_isProper {k : Type u} [Field k]
    {X X₁ : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsVariety k sX) (g : X₁ ⟶ X)
    (hX₁ : IsVariety k (g ≫ sX)) [IsProper g] [IsDominant g]
    (R : ValuationSubring X₁.functionField)
    (_hkR : ∀ c : k, (letI := functionFieldAlgebra (g ≫ sX); algebraMap k X₁.functionField c) ∈ R)
    (x : X)
    (hx : ∀ a : X.presheaf.stalk x,
      R.valuation (functionFieldMap g (algebraMap _ X.functionField a)) ≤ 1)
    (hxm : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      R.valuation (functionFieldMap g (algebraMap _ X.functionField a)) < 1) :
    ∃ x₁ : X₁, g x₁ = x ∧
      (∀ a : X₁.presheaf.stalk x₁, R.valuation (algebraMap _ X₁.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X₁.presheaf.stalk x₁),
        R.valuation (algebraMap _ X₁.functionField a) < 1 := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral X₁ := hX₁.toIsIntegral
  set K := X₁.functionField
  -- the local homomorphism `𝒪_{X,x} → R`
  let φ : X.presheaf.stalk x →+* R :=
    ((functionFieldMap g).comp (algebraMap (X.presheaf.stalk x) X.functionField)).codRestrict
      R.toSubring fun a ↦ (R.valuation_le_one_iff _).1 (hx a)
  have : IsLocalHom φ := ⟨fun a ha ↦ by_contra fun hna ↦
    (hxm a hna).ne ((R.valuation_eq_one_iff _).1 ha)⟩
  -- the valuative square
  let i₂ : Spec (.of R) ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x
  have hsq : X₁.fromSpecStalk (genericPoint X₁) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂ := by
    have : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap R K) =
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ _)) ≫
          X.presheaf.stalkSpecializes
            (Inseparable.of_eq (map_genericPoint_of_isDominant g)).specializes ≫
            g.stalkMap (genericPoint X₁) := by
      ext a; rfl
    simp only [i₂, ← Category.assoc, ← Spec.map_comp, this]
    simp only [Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (UniversallyClosed.eq_valuativeCriterion.le _ _ g inferInstance).1
    { R := R, K := K, i₁ := X₁.fromSpecStalk (genericPoint X₁), i₂ := i₂, commSq := ⟨hsq⟩ }
  refine ⟨l (closedPoint R), ?_, dominates_stalk_closedPoint R l hl₁⟩
  have : IsLocalHom (CommRingCat.ofHom φ).hom := ‹IsLocalHom φ›
  change (l ≫ g) _ = x
  rw [hl₂]
  exact (congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := CommRingCat.ofHom φ))).trans
    Scheme.fromSpecStalk_closedPoint

end MMP.Mori

/-! ### Regular hypersurface sections of a Noetherian local ring -/

namespace MMP

open IsLocalRing Ideal
open scoped Pointwise

/-- The Krull dimension of a Noetherian local ring is a natural number. -/
private lemma exists_ringKrullDim_eq_natCast (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : ∃ d : ℕ, ringKrullDim R = d := by
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim R := ringKrullDim_nonneg_of_nontrivial
  have h1 := ringKrullDim_le_spanFinrank_maximalIdeal R
  generalize ringKrullDim R = D at h0 h1
  induction D with
  | bot => simp at h0
  | coe D =>
    induction D with
    | top => exact absurd (WithBot.coe_le_coe.mp h1) (by simp)
    | coe D => exact ⟨D, rfl⟩

/-- Cutting by `g ∈ 𝔪` outside every minimal prime drops the dimension by exactly one. -/
private lemma ringKrullDim_quotient_add_one {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {g : R} (hg : g ∈ maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, g ∉ p) :
    ringKrullDim (R ⧸ span {g}) + 1 = ringKrullDim R := by
  have h2 : span {g} = g • (⊤ : Submodule R R) := by simp [← Submodule.ideal_span_singleton_smul]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R h2).toRingEquiv,
    ← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
  refine Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (fun p hp => hmin p ?_) hg
  rwa [Module.annihilator_eq_bot.mpr inferInstance] at hp

/-- A finset spanning `J` bounds the minimal number of generators of `J`. -/
private lemma spanFinrank_le_card {R : Type*} [CommRing R] {J : Ideal R} (t : Finset R)
    (h : J = span (↑t : Set R)) : J.spanFinrank ≤ t.card := by
  subst h
  simpa using Submodule.spanFinrank_span_le_ncard_of_finite t.finite_toSet

/-- Generators of the image of `J` under a surjection lift to a finset of `J` of no larger
cardinality which, together with the kernel, generates `J`. -/
private lemma exists_finset_le_span_sup_ker {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (J : Ideal R) (hJ : (J.map f).FG) :
    ∃ t : Finset R, (↑t : Set R) ⊆ J ∧ t.card ≤ (J.map f).spanFinrank ∧
      J ≤ span (↑t : Set R) ⊔ RingHom.ker f := by
  classical
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hJ
  have hmem : ∀ y ∈ s, ∃ x ∈ J, f x = y := fun y hy =>
    (mem_map_iff_of_surjective f hf).mp (hspan ▸ Submodule.subset_span hy)
  choose! lift hliftJ hlift using hmem
  refine ⟨s.image lift, by simpa [Set.subset_def] using hliftJ, hs ▸ Finset.card_image_le,
    fun x hx => ?_⟩
  have himg : f '' ↑(s.image lift) = (↑s : Set S) := by
    ext y
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    refine ⟨?_, fun hy => ⟨lift y, ⟨y, hy, rfl⟩, hlift y hy⟩⟩
    rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rwa [hlift z hz]
  rw [← comap_map_of_surjective' f hf, mem_comap, map_span, himg]
  exact (show span (↑s : Set S) = J.map f from hspan) ▸ mem_map_of_mem f hx

/-- Lifting generators of `𝔪 / (g)` to `R` gives a finset `t ⊆ 𝔪` with `#t ≤ μ(𝔪')` and
`𝔪 ≤ (t) + (g)`. -/
private lemma exists_lift_generators {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (g : R) [IsLocalRing (R ⧸ span {g})] :
    ∃ t : Finset R, (↑t : Set R) ⊆ maximalIdeal R ∧
      t.card ≤ (maximalIdeal (R ⧸ span {g})).spanFinrank ∧
      maximalIdeal R ≤ span (↑t : Set R) ⊔ span {g} := by
  have hmap := map_maximalIdeal_of_surjective (Ideal.Quotient.mk (span {g}))
    Ideal.Quotient.mk_surjective
  have := exists_finset_le_span_sup_ker _ Ideal.Quotient.mk_surjective
    (maximalIdeal R) (hmap ▸ IsNoetherian.noetherian (maximalIdeal (R ⧸ span {g})))
  rwa [hmap, mk_ker] at this

/-- `μ(𝔪) ≤ μ(𝔪 / (g)) + 1`: lift generators and add `g`. -/
private lemma spanFinrank_le_spanFinrank_quotient_add_one {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {g : R} (hg : g ∈ maximalIdeal R)
    [IsLocalRing (R ⧸ span {g})] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ span {g})).spanFinrank + 1 := by
  classical
  obtain ⟨t, htm, htcard, htle⟩ := exists_lift_generators (R := R) g
  have heq : maximalIdeal R = span (↑(insert g t) : Set R) := by
    refine le_antisymm ?_ ?_
    · rwa [Finset.coe_insert, span_insert, sup_comm]
    · rw [span_le, Finset.coe_insert]
      exact Set.insert_subset hg htm
  exact (spanFinrank_le_card _ heq).trans ((Finset.card_insert_le _ _).trans (by omega))

/-- `μ(𝔪) ≤ μ(𝔪 / (g))` when `g ∈ 𝔪 ^ 2`, by Nakayama. -/
private lemma spanFinrank_le_spanFinrank_quotient_of_mem_sq {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {g : R} (hg2 : g ∈ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ span {g})] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ span {g})).spanFinrank := by
  obtain ⟨t, htm, htcard, htle⟩ := exists_lift_generators (R := R) g
  have hle : maximalIdeal R ≤ span (↑t : Set R) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (maximalIdeal_le_jacobson _) (htle.trans (sup_le_sup_left ?_ _))
    rwa [span_le, Set.singleton_subset_iff, smul_eq_mul, ← pow_two]
  exact (spanFinrank_le_card _ (le_antisymm hle (span_le.mpr htm))).trans htcard

/-- If `g ∈ 𝔪` is not in `𝔪 ^ 2`, then in any finite generating set of `𝔪` some generator can
be exchanged for `g`. -/
private lemma exists_le_span_erase_sup {R : Type*} [CommRing R] [IsLocalRing R] [DecidableEq R]
    {g : R} (hg : g ∈ maximalIdeal R) (hg2 : g ∉ maximalIdeal R ^ 2) (S : Finset R)
    (hS : span (↑S : Set R) = maximalIdeal R) :
    ∃ s₀ ∈ S, maximalIdeal R ≤ span (↑(S.erase s₀) : Set R) ⊔ span {g} := by
  obtain ⟨c, -, hc⟩ := (Submodule.mem_span_finset).mp (hS ▸ hg)
  obtain ⟨s₀, hs₀, ⟨u, hu⟩⟩ : ∃ s₀ ∈ S, IsUnit (c s₀) := by
    by_contra! h
    refine hg2 (hc ▸ pow_two (maximalIdeal R) ▸ sum_mem _ fun i hi => ?_)
    exact mul_mem_mul ((mem_maximalIdeal _).mpr (h i hi)) (hS ▸ subset_span hi)
  refine ⟨s₀, hs₀, ?_⟩
  rw [← hS, span_le]
  intro x hx
  by_cases hxs : x = s₀
  · subst hxs
    have hmem : c x • x ∈ span (↑(S.erase x) : Set R) ⊔ span {g} := by
      rw [show c x • x = g - ∑ i ∈ S.erase x, c i • i by
        rw [← hc, ← Finset.add_sum_erase S _ hs₀]; ring]
      exact sub_mem (mem_sup_right (mem_span_singleton_self g))
        (mem_sup_left (sum_mem _ fun i hi => mul_mem_left _ _ (subset_span hi)))
    have := mul_mem_left _ (↑u⁻¹ : R) hmem
    rwa [smul_eq_mul, ← mul_assoc, ← hu, Units.inv_mul, one_mul] at this
  · exact mem_sup_left (subset_span (Finset.mem_erase.mpr ⟨hxs, hx⟩))

/-- `μ(𝔪 / (g)) + 1 ≤ μ(𝔪)` when `g ∈ 𝔪 \ 𝔪 ^ 2`: exchange a minimal generator for `g`. -/
private lemma spanFinrank_quotient_add_one_le_of_notMem_sq {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {g : R} (hg : g ∈ maximalIdeal R)
    (hg2 : g ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {g})] :
    (maximalIdeal (R ⧸ span {g})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  classical
  obtain ⟨S, hS, hSspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (maximalIdeal R))
  obtain ⟨s₀, hs₀, hle⟩ := exists_le_span_erase_sup hg hg2 S hSspan
  have heq : maximalIdeal (R ⧸ span {g}) =
      span (↑((S.erase s₀).image (Ideal.Quotient.mk (span {g}))) : Set (R ⧸ span {g})) := by
    rw [Finset.coe_image, ← map_span,
      ← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    refine le_antisymm ((map_mono hle).trans ?_) (map_mono ?_)
    · rw [Ideal.map_sup, map_quotient_self, sup_bot_eq]
    · exact hSspan ▸ span_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
  have := (spanFinrank_le_card _ heq).trans Finset.card_image_le
  have := Finset.card_erase_add_one hs₀
  omega

/-- For a Noetherian local ring `R` and `g` in the maximal ideal avoiding every minimal prime,
`R ⧸ (g)` is regular local iff `R` is regular local and `g ∉ 𝔪 ^ 2`. -/
@[mmp "lem_mmp_foundation_regular_hypersurface_equivalence"]
theorem isRegularLocalRing_quotient_span_singleton_iff {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {g : R} (hg : g ∈ maximalIdeal R)
    (hmin : ∀ p ∈ minimalPrimes R, g ∉ p) :
    IsRegularLocalRing (R ⧸ Ideal.span {g}) ↔
      IsRegularLocalRing R ∧ g ∉ maximalIdeal R ^ 2 := by
  have : Nontrivial (R ⧸ span {g}) := Ideal.Quotient.nontrivial_iff.mpr
    (by rw [Ne, span_singleton_eq_top]; exact (mem_maximalIdeal g).mp hg)
  have : IsLocalRing (R ⧸ span {g}) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast (R ⧸ span {g})
  have hR : ringKrullDim R = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← ringKrullDim_quotient_add_one hg hmin, hd]; rfl
  have hK : d + 1 ≤ (maximalIdeal R).spanFinrank := by
    exact_mod_cast hR ▸ ringKrullDim_le_spanFinrank_maximalIdeal R
  have hK' : d ≤ (maximalIdeal (R ⧸ span {g})).spanFinrank := by
    exact_mod_cast hd ▸ ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ span {g})
  have hA := spanFinrank_le_spanFinrank_quotient_add_one hg (R := R)
  rw [isRegularLocalRing_iff, isRegularLocalRing_iff, hd, hR, Nat.cast_inj, Nat.cast_inj]
  refine ⟨fun h => ⟨by omega, fun hg2 => ?_⟩, fun ⟨h, hg2⟩ => ?_⟩
  · have := spanFinrank_le_spanFinrank_quotient_of_mem_sq hg2 (R := R)
    omega
  · have := spanFinrank_quotient_add_one_le_of_notMem_sq hg hg2 (R := R)
    omega

end MMP

/-! ### Closed points of large characteristic and lifts to `W₂` -/

namespace MMP

section Witt

variable {p : ℕ} [Fact p.Prime] {k : Type*} [CommRing k]

/-- The zeroth coordinate `W₂(k) → k` as a ring homomorphism. -/
private noncomputable def coeffZero : TruncatedWittVector p 2 k →+* k :=
  (WittVector.truncate (p := p) (R := k) 2).liftOfSurjective
    (WittVector.truncate_surjective (p := p) 2 k)
    ⟨WittVector.constantCoeff, fun x hx => by
      rw [RingHom.mem_ker, WittVector.constantCoeff_apply]
      exact (WittVector.mem_ker_truncate 2 x).mp hx 0 (by norm_num)⟩

private lemma coeffZero_truncate (w : WittVector p k) :
    coeffZero (p := p) (WittVector.truncate 2 w) = w.coeff 0 := by
  unfold coeffZero
  rw [RingHom.liftOfRightInverse_comp_apply]
  rfl

private lemma coeffZero_apply (x : TruncatedWittVector p 2 k) :
    coeffZero x = x.coeff 0 := by
  obtain ⟨w, rfl⟩ := WittVector.truncate_surjective (p := p) 2 k x
  rw [coeffZero_truncate]
  exact (WittVector.coeff_truncate (n := 2) w 0).symm

private lemma coeffZero_surjective : Function.Surjective (coeffZero (p := p) (k := k)) :=
  fun a => ⟨WittVector.truncate 2 (WittVector.teichmuller p a), by
    rw [coeffZero_truncate, WittVector.teichmuller_coeff_zero]⟩

private lemma isNilpotent_ker_coeffZero [CharP k p] :
    IsNilpotent (RingHom.ker (coeffZero (p := p) (k := k))) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff]
  refine Submodule.mul_le.mpr fun x hx y hy => ?_
  obtain ⟨a, rfl⟩ := WittVector.truncate_surjective (p := p) 2 k x
  obtain ⟨b, rfl⟩ := WittVector.truncate_surjective (p := p) 2 k y
  rw [RingHom.mem_ker, coeffZero_truncate] at hx hy
  have ha := WittVector.eq_iterate_verschiebung (n := 1) (x := a)
    (fun i hi => Nat.lt_one_iff.mp hi ▸ hx)
  have hb := WittVector.eq_iterate_verschiebung (n := 1) (x := b)
    (fun i hi => Nat.lt_one_iff.mp hi ▸ hy)
  rw [Ideal.mem_bot, ← map_mul, ← RingHom.mem_ker, WittVector.mem_ker_truncate, ha, hb,
    WittVector.iterate_verschiebung_mul]
  intro i hi
  interval_cases i
  · simp only [Function.iterate_succ_apply', WittVector.verschiebung_coeff_zero]
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [show (1 : ℕ) = Nat.succ 0 from rfl, WittVector.verschiebung_coeff_succ,
      WittVector.verschiebung_coeff_zero]

/-- If `R_𝔪` is formally smooth over `ℤ` and `R ⧸ 𝔪` has characteristic `p`, the residue map
`R → R ⧸ 𝔪` lifts along the zeroth coordinate to `R → W₂(R ⧸ 𝔪)`. -/
private lemma exists_lift_truncatedWittVector {R : Type*} [CommRing R] (𝔪 : Ideal R)
    [𝔪.IsMaximal] [Algebra.FormallySmooth ℤ (Localization.AtPrime 𝔪)] [CharP (R ⧸ 𝔪) p] :
    ∃ φ : R →+* TruncatedWittVector p 2 (R ⧸ 𝔪),
      ∀ r : R, (φ r).coeff 0 = Ideal.Quotient.mk 𝔪 r := by
  let g : Localization.AtPrime 𝔪 →+* R ⧸ 𝔪 :=
    IsLocalization.lift (M := 𝔪.primeCompl) (g := Ideal.Quotient.mk 𝔪) fun y =>
      letI := Ideal.Quotient.field 𝔪
      isUnit_iff_ne_zero.mpr (Ideal.Quotient.eq_zero_iff_mem.not.mpr y.2)
  let gA : Localization.AtPrime 𝔪 →ₐ[ℤ] R ⧸ 𝔪 := { g with commutes' := by simp }
  let cA : TruncatedWittVector p 2 (R ⧸ 𝔪) →ₐ[ℤ] R ⧸ 𝔪 := { coeffZero with commutes' := by simp }
  let L := Algebra.FormallySmooth.liftOfSurjective gA cA coeffZero_surjective
    isNilpotent_ker_coeffZero
  refine ⟨L.toRingHom.comp (algebraMap R _), fun r => ?_⟩
  rw [← coeffZero_apply]
  exact (Algebra.FormallySmooth.liftOfSurjective_apply gA cA coeffZero_surjective
    isNilpotent_ker_coeffZero _).trans (IsLocalization.lift_eq _ _)

end Witt

/-- If `f` becomes a unit in a nonzero `R`-algebra `S` that is flat over `ℤ` (for instance
`S = R_f`), then `f * n` is not nilpotent for any nonzero natural number `n`. -/
private lemma not_isNilpotent_mul_natCast {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    [Algebra R S] [Algebra ℤ S] [hS : @Module.Flat ℤ S _ _ Algebra.toModule] {f : R}
    (hf : IsUnit (algebraMap R S f)) {n : ℕ} (hn : n ≠ 0) : ¬ IsNilpotent (f * n) := by
  intro h
  have h' := h.map (algebraMap R S)
  rw [map_mul, map_natCast] at h'
  obtain ⟨m, hm⟩ := (hf.isNilpotent_unit_mul_of_commute_iff (Commute.all _ _)).mp h'
  have hreg := @Module.Flat.isSMulRegular_of_nonZeroDivisors ℤ S _ _ Algebra.toModule _
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m (Int.natCast_ne_zero.mpr hn))) hS
  exact one_ne_zero (hreg (a₁ := 1) (a₂ := 0) (by simpa [Algebra.smul_def] using hm))

/-- Every nonempty open `U` of the smooth locus of a finite type `ℤ`-algebra `R` contains, for
each `N`, a maximal ideal `𝔪` with finite residue field `R ⧸ 𝔪` of prime characteristic `p > N`,
together with a ring homomorphism `φ : R →+* W₂(R ⧸ 𝔪)` lifting the residue map. -/
@[mmp "lem_mmp_lc_bpf_arithmetic_witt_lift"]
theorem exists_isMaximal_mem_smoothLocus_witt_lift {R : Type*} [CommRing R]
    [Algebra.FiniteType ℤ R] (U : Set (PrimeSpectrum R)) (hU : IsOpen U) (hne : U.Nonempty)
    (hUs : U ⊆ Algebra.smoothLocus ℤ R) (N : ℕ) :
    ∃ (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal), (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum R) ∈ U ∧
      Finite (R ⧸ 𝔪) ∧ ∃ (p : ℕ) (_ : Fact p.Prime), N < p ∧ CharP (R ⧸ 𝔪) p ∧
        ∃ φ : R →+* TruncatedWittVector p 2 (R ⧸ 𝔪),
          ∀ r : R, (φ r).coeff 0 = Ideal.Quotient.mk 𝔪 r := by
  have : IsJacobsonRing ℤ := int_isJacobsonRing
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ)
  have : Algebra.FinitePresentation ℤ R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  obtain ⟨q, hq⟩ := hne
  obtain ⟨_, ⟨f, rfl⟩, hqf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hq hU
  have : Algebra.Smooth ℤ (Localization.Away f) :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mp (hfU.trans hUs)
  have := Algebra.Smooth.flat ℤ (Localization.Away f)
  have hD : (PrimeSpectrum.basicOpen (f * N.factorial) : Set (PrimeSpectrum R)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ← TopologicalSpace.Opens.coe_bot, Ne, SetLike.coe_set_eq,
      PrimeSpectrum.basicOpen_eq_bot_iff]
    have : Nontrivial (Localization.Away f) := OreLocalization.nontrivial_iff.mpr fun h => by
      simp [(PrimeSpectrum.basicOpen_eq_bot_iff f).mpr h] at hqf
    exact not_isNilpotent_mul_natCast (S := Localization.Away f)
      (IsLocalization.Away.algebraMap_isUnit f) N.factorial_ne_zero
  obtain ⟨x, hxD, hxc⟩ :=
    nonempty_inter_closedPoints hD (PrimeSpectrum.basicOpen _).isOpen.isLocallyClosed
  have hmax : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).1 hxc
  have hxD' : f * N.factorial ∉ x.asIdeal := hxD
  have hxU : x ∈ U := hfU fun h => hxD' (x.asIdeal.mul_mem_right _ h)
  set 𝔪 := x.asIdeal
  have hft : Algebra.FiniteType ℤ (R ⧸ 𝔪) := .trans (S := R) inferInstance inferInstance
  let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  obtain ⟨hfin, hchar⟩ := @MMP.Fourfold.finite_and_charPos_of_finiteType_int (R ⧸ 𝔪) _
    (by convert hft using 1 <;> first | rfl | exact Subsingleton.elim _ _)
  set p := ringChar (R ⧸ 𝔪)
  have : NeZero p := ⟨hchar.ne'⟩
  have hp : Fact p.Prime := CharP.char_is_prime_of_pos (R ⧸ 𝔪) p
  have hNp : N < p := by
    by_contra! hle
    refine hxD' (x.asIdeal.mul_mem_left _ ?_)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]
    exact (Nat.Prime.dvd_factorial hp.out).mpr hle
  have : Algebra.FormallySmooth ℤ (Localization.AtPrime 𝔪) := hUs hxU
  exact ⟨𝔪, hmax, hxU, hfin, p, hp, hNp, inferInstance, exists_lift_truncatedWittVector 𝔪⟩

end MMP

/-! ### Higher direct images as a δ-functor -/

namespace MMP.SheafOfModules

/-- **Higher direct images form a cohomological δ-functor.** For a morphism of ringed sites given
by a continuous functor `F : C ⥤ D` and `φ : S ⟶ F_* R`, there is a cohomological δ-functor
from sheaves of `R`-modules to sheaves of `S`-modules whose `i`-th functor is the `i`-th right
derived functor `R^i f_*` of the direct image `SheafOfModules.pushforward φ`. -/
@[mmp "thm_mmp_higher_direct_images_delta_functor"]
theorem exists_deltaFunctor_functor_eq_pushforward_rightDerived
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [F.IsContinuous J K] {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    haveI : EnoughInjectives (_root_.SheafOfModules.{u} R) :=
      IsGrothendieckAbelian.enoughInjectives
    haveI : (_root_.SheafOfModules.pushforward.{u} φ).Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
    ∃ E : DeltaFunctor (_root_.SheafOfModules.{u} R) (_root_.SheafOfModules.{u} S),
      ∀ i : ℕ, E.functor i = (_root_.SheafOfModules.pushforward.{u} φ).rightDerived i :=
  ⟨_, Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor _⟩

end MMP.SheafOfModules

end
