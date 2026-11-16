module

public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Foundational facts on morphisms of schemes

This file collects foundational results used throughout the minimal model programme: generic
flatness over an integral base, generic pure dimensionality of the fibres of a dominant
morphism of varieties, closedness of the locus of positive fibre dimension of a proper
morphism, stability of smoothness under base change, the inclusion of the structure sheaf in
the sheaf of meromorphic functions, the blow-up of a stratum of a simple normal crossing
divisor, and the Milnor sequence for a tower of cochain complexes.

## Main results

* `MMP.exists_dense_isFlatOver_restrict_of_isIntegral`: generic flatness.
* `MMP.Foundations.exists_dense_isOpen_forall_irreducibleComponents_fiber_dim`: generic fibres
  of a dominant morphism of varieties have pure dimension `dim W - dim Z`.
* `MMP.isClosed_setOf_one_le_fiberDimensionAt`: upper semicontinuity of fibre dimension.
* `MMP.smooth_isStableUnderBaseChange_and_isomorphisms_le`: smoothness and base change.
* `MMP.Scheme.mono_toTotalQuotientSheaf_and_mono_unitGroupSheafMap`: `𝒪_X ⊆ 𝒦_X`.
* `MMP.Resolution.blowUp_snc_stratum`: blowing up a stratum of an snc divisor.
* `MMP.Analytic.milnor_sequence`: the Milnor `lim¹` sequence.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004]
* [R. Hartshorne, *Algebraic Geometry*][Hartshorne]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [The Stacks Project][stacks-project]
-/

universe u

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

/-!
## Generic flatness over an integral base

Let `f : Z ⟶ T` be a morphism of finite type with `T` an integral scheme, and let `F` be a
quasi-coherent `𝒪_Z`-module of finite type. Then there is a dense open `V ⊆ T` such that the
restriction `F|_{f⁻¹(V)}` is flat over `V`.

### Main results

* `MMP.exists_dense_isFlatOver_restrict_of_isIntegral`: generic flatness of a quasi-coherent
  module of finite type along a finite type morphism to an integral scheme.

### Implementation notes

Flatness of `F|_{f⁻¹(V)}` over `V` is `AlgebraicGeometry.IsFlatOver` for the restricted morphism
`f.resLE V (f ⁻¹ᵁ V) le_rfl : f⁻¹(V) ⟶ V` and the restriction `F.restrict (f ⁻¹ᵁ V).ι`.

A coherent module is of finite presentation, hence quasi-coherent of finite type, so the
statement covers coherent modules.

### References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004]
* [Stacks Project, Tag 051R](https://stacks.math.columbia.edu/tag/051R)
-/

namespace MMP

/-- **Generic flatness.** For a morphism of finite type `f : Z ⟶ T` to an integral scheme and a
quasi-coherent `𝒪_Z`-module `F` of finite type, there is a dense open `V` of `T` such that the
restriction of `F` to `f⁻¹(V)` is flat over `V`. -/
@[mmp "lem_mmp_foundation_laz_generic_flatness"]
public theorem exists_dense_isFlatOver_restrict_of_isIntegral {Z T : Scheme.{u}} (f : Z ⟶ T)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsIntegral T]
    (F : Z.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ V : T.Opens, Dense (V : Set T) ∧
      IsFlatOver (f.resLE V (f ⁻¹ᵁ V) le_rfl).toLRSHom.toShHom (F.restrict (f ⁻¹ᵁ V).ι) := by
  obtain ⟨U, hU, -, -, hflat, -⟩ := exists_dense_open_flat_finitePresentation f F
  exact ⟨U, hU, hflat⟩

end MMP

/-!
## Generic fibres of a dominant morphism of varieties have pure dimension

Let `f : W ⟶ Z` be a dominant morphism of varieties over a field `k`. There is a dense open
subset `U ⊆ Z`, contained in the image of `f`, such that for every `z ∈ U` every irreducible
component of the fibre `f⁻¹(z)` has dimension `dim W - dim Z`.

### Main results

* `MMP.Foundations.exists_dense_isOpen_forall_irreducibleComponents_fiber_dim`: generic pure
  dimensionality of the fibres of a dominant morphism of varieties.

### Implementation notes

The fibre `f⁻¹(z)` is the set-theoretic preimage of `z` with the subspace topology, which is
homeomorphic to the underlying space of the scheme-theoretic fibre
`AlgebraicGeometry.Scheme.Hom.fiber`; dimensions are topological Krull dimensions. Pure
dimension `dim W - dim Z` is written additively, `dim C + dim Z = dim W` for every irreducible
component `C`, which avoids truncated subtraction in `WithBot ℕ∞` (all dimensions are finite
for varieties). A variety is `AlgebraicGeometry.IsVariety k s` for its structure morphism `s`,
and `f` is a morphism of varieties when `f ≫ sZ = sW`.

### References

* [R. Hartshorne, *Algebraic Geometry*, Exercise II.3.22][Hartshorne]
-/

namespace MMP.Foundations

/-! ### Proof

Let `f : W ⟶ Z` be a dominant morphism of varieties over a field `k`. Over a dense open
`V₁ ⊆ Z` the morphism is flat of finite presentation (generic flatness), so the image
`U = f(f⁻¹ V₁)` is open, nonempty by dominance, hence dense. The source `f⁻¹ V₁` is covered,
densely in every fibre, by open pieces of pure relative dimension `d` (Stacks 054T), and on
a nonempty piece the flat dimension formula (Stacks 0AFE) reads `dim W = dim Z + d`, as every
nonempty open of an irreducible variety has the dimension of the variety. Every irreducible
component of a fibre over `U` contains a point of some piece at its generic point, where the
local dimension of the fibre is both `d` and the dimension of the component.
-/

/-- On a Noetherian scheme locally of finite type over a field, if a property of the local
dimension holds at every point of a dense open subset, then it holds for the dimension of every
irreducible component. -/
private theorem forall_irreducibleComponents_of_dense (k : Type u) [Field k] (X : Scheme)
    (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] [NoetherianSpace X]
    (P : WithBot ℕ∞ → Prop) {O : Set X} (hO : IsOpen O) (hd : Dense O)
    (hP : ∀ x ∈ O, P (topologicalKrullDimAt X x)) :
    ∀ C ∈ irreducibleComponents X, P (topologicalKrullDim C) := by
  intro C hC
  have hηC : IsGenericPoint hC.1.genericPoint C :=
    hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  obtain ⟨o, ho, hne, hoC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  obtain ⟨y, hyo, hyO⟩ := hd.inter_open_nonempty o ho hne
  have hηO : hC.1.genericPoint ∈ O := (hηC.specializes (hoC hyo)).mem_open hO hyO
  have honly : ∀ V ∈ irreducibleComponents X, hC.1.genericPoint ∈ V → V = C := by
    intro V hV hηV
    have hCV : C ⊆ V := hηC ▸ closure_minimal (Set.singleton_subset_iff.mpr hηV)
      (isClosed_of_mem_irreducibleComponents V hV)
    exact (hCV.antisymm (hC.2 hV.1 hCV)).symm
  have hlocal : topologicalKrullDimAt X hC.1.genericPoint = topologicalKrullDim C := by
    rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X q hC.1.genericPoint]
    refine le_antisymm (iSup_le fun V ↦ iSup_le fun hV ↦ by rw [honly V hV.1 hV.2]) ?_
    exact le_iSup_of_le C (le_iSup_of_le ⟨hC, hηC.mem⟩ le_rfl)
  rw [← hlocal]
  exact hP _ hηO

/-- The local dimension of an irreducible scheme locally of finite type over a field is the
dimension of the scheme at every point. -/
private theorem topologicalKrullDimAt_eq_topologicalKrullDim (k : Type u) [Field k]
    (X : Scheme) (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] [IrreducibleSpace X]
    (x : X) : topologicalKrullDimAt X x = topologicalKrullDim X := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X q x,
    irreducibleComponents_eq_singleton]
  have : {Z : Set X | Z ∈ ({Set.univ} : Set (Set X)) ∧ x ∈ Z} = {Set.univ} := by
    ext Z
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h ▸ Set.mem_univ x⟩⟩
  rw [this, iSup_singleton]
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph)

/-- The irreducible components of a space correspond to those of a homeomorphic space, with the
same dimensions. -/
private theorem preimage_mem_irreducibleComponents_and_topologicalKrullDim_eq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {C : Set Y}
    (hC : C ∈ irreducibleComponents Y) :
    e ⁻¹' C ∈ irreducibleComponents X ∧ topologicalKrullDim (e ⁻¹' C) = topologicalKrullDim C := by
  refine ⟨preimage_mem_irreducibleComponents hC e.isOpenEmbedding ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hC.1.nonempty
    exact ⟨c, hc, e.surjective c⟩
  · rw [← e.image_symm]
    exact (IsHomeomorph.topologicalKrullDim_eq _ (e.symm.image C).isHomeomorph).symm

/-- On a nonempty open piece `Y` of a variety `W` that maps flatly with pure relative dimension `d`
to a variety `Z`, the flat dimension formula gives `d + dim Z = dim W`: every nonempty open of a
variety has the dimension of the variety. -/
private theorem natCast_add_topologicalKrullDim_eq_of_relativeDimension (k : Type u) [Field k]
    {Y W Z : Scheme} (sW : W ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [IsVariety k sW]
    [IsVariety k sZ] (j : Y ⟶ W) [IsOpenImmersion j] (h : Y ⟶ Z) [Flat h] [LocallyOfFiniteType h]
    [IsLocallyNoetherian Y] {d : ℕ} (hd : RelativeDimension h d) (y : Y) :
    (d : WithBot ℕ∞) + topologicalKrullDim Z = topologicalKrullDim W := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  rw [← topologicalKrullDimAt_eq_topologicalKrullDim k W sW (j y),
    j.isOpenEmbedding.topologicalKrullDimAt_eq y,
    topologicalKrullDimAt_eq_add_of_relativeDimension h hd y,
    topologicalKrullDimAt_eq_topologicalKrullDim k Z sZ, add_comm]

/-- Over a point `z` of an open `V`, the fibre of the restriction of `f` to `f⁻¹ V` is
homeomorphic to the fibre of `f` over `z`. -/
private noncomputable def fiberHomeoRestrict {W Z : Scheme} (f : W ⟶ Z) (V : Z.Opens)
    {z : Z} (hz : z ∈ V) : ((f ⁻¹ᵁ V).ι ≫ f).fiber z ≃ₜ (f ⁻¹' {z} : Set W) :=
  (Scheme.Hom.fiberHomeo _ z).trans <|
    ((isHomeomorph_iff_isEmbedding_surjective
      (f := fun p : (((f ⁻¹ᵁ V).ι ≫ f) ⁻¹' {z} : Set (f ⁻¹ᵁ V)) ↦
        (⟨p.1.1, p.2⟩ : (f ⁻¹' {z} : Set W)))).mpr
      ⟨(IsEmbedding.of_comp_iff (g := ((↑) : (f ⁻¹' {z} : Set W) → W))
          IsEmbedding.subtypeVal).mp (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal :
            IsEmbedding fun p : (((f ⁻¹ᵁ V).ι ≫ f) ⁻¹' {z} : Set (f ⁻¹ᵁ V)) ↦ p.1.1),
        fun ⟨w, hw⟩ ↦ ⟨⟨⟨w, show f w ∈ V by rw [show f w = z from hw]; exact hz⟩, hw⟩,
          rfl⟩⟩).homeomorph

/-- **Generic fibres of a dominant morphism have pure dimension.** If `f : W ⟶ Z` is a dominant
morphism of varieties over `k`, there is a dense open `U ⊆ Z` contained in the image of `f` such
that for every `z ∈ U`, every irreducible component `C` of the fibre `f⁻¹(z)` satisfies
`dim C + dim Z = dim W`. -/
@[mmp "lem_mmp_foundation_dominant_generic_pure_fibres"]
public theorem exists_dense_isOpen_forall_irreducibleComponents_fiber_dim
    {k : Type u} [Field k] {W Z : Scheme.{u}} (sW : W ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    (hW : IsVariety k sW) (hZ : IsVariety k sZ) (f : W ⟶ Z) (hf : f ≫ sZ = sW)
    [IsDominant f] :
    ∃ U : Set Z, IsOpen U ∧ Dense U ∧ U ⊆ Set.range f ∧
      ∀ z ∈ U, ∀ C ∈ irreducibleComponents (f ⁻¹' {z}),
        topologicalKrullDim C + topologicalKrullDim Z = topologicalKrullDim W := by
  have : LocallyOfFiniteType (f ≫ sZ) := hf ▸ inferInstance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f sZ
  have : QuasiCompact (f ≫ sZ) := hf ▸ inferInstance
  have : QuasiCompact f := QuasiCompact.of_comp f sZ
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have : CompactSpace W := (quasiCompact_iff_compactSpace sW).mp inferInstance
  have : IsNoetherian W := ⟨⟩
  -- Generic flatness over a dense open `V₁ ⊆ Z`, so `g : f⁻¹ V₁ ⟶ Z` is flat and open.
  obtain ⟨V₁, hV₁dense, hflat, hfp⟩ := exists_dense_open_flat_finitePresentation_structureSheaf f
  have : LocallyOfFinitePresentation (f.resLE V₁ (f ⁻¹ᵁ V₁) le_rfl) :=
    hfp.locallyOfFinitePresentation
  set g : (f ⁻¹ᵁ V₁).toScheme ⟶ Z := (f ⁻¹ᵁ V₁).ι ≫ f
  have hg : g = f.resLE V₁ (f ⁻¹ᵁ V₁) le_rfl ≫ V₁.ι := (Scheme.Hom.resLE_comp_ι f le_rfl).symm
  have : Flat g := hg ▸ inferInstance
  have : LocallyOfFinitePresentation g := hg ▸ inferInstance
  have : UniversallyOpen g := UniversallyOpen.of_flat g
  have hopen : IsOpen (Set.range g) := g.isOpenMap.isOpen_range
  -- Pieces of pure relative dimension, fibrewise dense (Stacks 054T).
  obtain ⟨U, hUdense, hrel⟩ := exists_open_relativeDimension_fiberwise_dense g
  refine ⟨Set.range g, hopen, hopen.dense ?_, fun _ ⟨x, hx⟩ ↦ ⟨x.1, hx⟩, ?_⟩
  · -- The image is nonempty by dominance, hence dense in the irreducible `Z`.
    obtain ⟨v, hvV₁, w, hw⟩ := (IsDominant.denseRange (f := f)).inter_open_nonempty
      (V₁ : Set Z) V₁.2 hV₁dense.nonempty
    exact ⟨g ⟨w, show f w ∈ V₁ from hw ▸ hvV₁⟩, _, rfl⟩
  · rintro _ ⟨x₀, rfl⟩ C hC
    let Φ : g.fiber (g x₀) ≃ₜ (f ⁻¹' {g x₀} : Set W) := fiberHomeoRestrict f V₁ x₀.2
    have : NoetherianSpace (g.fiber (g x₀)) :=
      noetherianSpace_of_surjective Φ.symm Φ.symm.continuous Φ.symm.surjective
    have := g.locallyOfFiniteType_fiberToSpecResidueField (g x₀)
    obtain ⟨hC', hdimC'⟩ := preimage_mem_irreducibleComponents_and_topologicalKrullDim_eq Φ hC
    rw [← hdimC']
    refine forall_irreducibleComponents_of_dense (Z.residueField (g x₀)) (g.fiber (g x₀))
      (g.fiberToSpecResidueField (g x₀)) (· + topologicalKrullDim Z = topologicalKrullDim W)
      (((iSup U : (f ⁻¹ᵁ V₁).toScheme.Opens).isOpen).preimage (g.fiberι _).continuous)
      (hUdense _) (fun w hw ↦ ?_) _ hC'
    obtain ⟨d, hd⟩ := Opens.mem_iSup.mp hw
    rw [← Scheme.Hom.topologicalKrullDimAt_fiber_fiberι,
      topologicalKrullDimAt_fiber_eq_of_relativeDimension g (U d) d (hrel d) _ hd]
    exact natCast_add_topologicalKrullDim_eq_of_relativeDimension k sW sZ ((U d).ι ≫ (f ⁻¹ᵁ V₁).ι)
      ((U d).ι ≫ g) (hrel d) ⟨_, hd⟩

end MMP.Foundations

/-!
## The locus of positive local fibre dimension of a proper morphism is closed

Let `k` be a field and `f : Y ⟶ Z` a proper morphism of `k`-schemes of finite type. For a point
`y` of `Y`, the local dimension of the fibre `f⁻¹(f y)` at `y` is the Krull dimension at `y` of the
scheme-theoretic fibre, i.e. the infimum of the dimensions of the open neighbourhoods of `y` in
the fibre. The points where this local dimension is at least one form a closed subset of `Y`.

### Main results

* `MMP.isClosed_setOf_one_le_fiberDimensionAt`: the set of `y : Y` with
  `1 ≤ topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y)` is closed.

### Implementation notes

A scheme of finite type over `k` is a `k`-scheme whose structure morphism is locally of finite
type and quasi-compact. The point `y` is represented in its fibre by `Scheme.Hom.asFiber`, and
`dim_y f⁻¹(f y)` is `topologicalKrullDimAt` of the fibre at that point, the neighbourhood
dimension rather than the Krull dimension of the local ring.

### References

* [EGA IV, Theorem 13.1.3]
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
-/

namespace MMP

private lemma one_le_iff_not_le_zero {d : WithBot ℕ∞} : 1 ≤ d ↔ ¬d ≤ 0 := by
  induction d with
  | bot => simp
  | coe e => norm_cast; rw [Order.one_le_iff_ne_zero, nonpos_iff_eq_zero]

/-- For a proper morphism `f : Y ⟶ Z` of schemes of finite type over a field `k`, the set of
points `y` at which the fibre `f⁻¹(f y)` has local dimension at least one is closed in `Y`. -/
@[mmp "lem_mmp_foundation_proper_fibre_dimension_semicontinuity"]
public theorem isClosed_setOf_one_le_fiberDimensionAt (k : Type u) [Field k]
    {Y Z : Scheme.{u}} [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    (f : Y ⟶ Z) [f.IsOver (Spec (.of k))] [IsProper f] :
    IsClosed {y : Y | (1 : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y)} := by
  convert (isOpen_setOf_fiberDimensionAt_le f 0).isClosed_compl using 1
  ext y
  exact one_le_iff_not_le_zero

end MMP

/-!
## Smooth morphisms are stable under base change

The base change of a smooth morphism of schemes along an arbitrary morphism is smooth, and
every isomorphism of schemes is smooth. In the language of morphism properties: `@Smooth` is
stable under base change and contains the isomorphisms.

### Main results

* `MMP.smooth_isStableUnderBaseChange_and_isomorphisms_le`: `@Smooth` is stable under base
  change and contains `MorphismProperty.isomorphisms Scheme`.

### References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004]
-/

namespace MMP

/-- Smooth morphisms of schemes are stable under base change along arbitrary morphisms, and
every isomorphism of schemes is smooth. -/
@[mmp "lem_mmp_foundation_laz_smooth_base_change"]
public theorem smooth_isStableUnderBaseChange_and_isomorphisms_le :
    MorphismProperty.IsStableUnderBaseChange @Smooth ∧
      MorphismProperty.isomorphisms Scheme.{u} ≤ @Smooth := by
  exact ⟨inferInstance, fun _ _ f (_ : IsIso f) => inferInstance⟩

end MMP

/-!
## The structure sheaf inside the sheaf of meromorphic functions

For a scheme `X`, the canonical morphism `𝒪_X ⟶ 𝒦_X` from the structure sheaf to the sheaf of
total quotient rings (the sheaf of meromorphic functions) is a monomorphism of sheaves of rings,
and the induced morphism of unit-group sheaves `𝒪_X^* ⟶ 𝒦_X^*` is a monomorphism of sheaves of
abelian groups. No hypothesis on `X` is needed.

### Main results

* `MMP.Scheme.mono_toTotalQuotientSheaf_and_mono_unitGroupSheafMap`: `𝒪_X ⊆ 𝒦_X` and
  `𝒪_X^* ⊆ 𝒦_X^*`.

### References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*, §1.1.A][lazarsfeld2004]
* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
-/

namespace MMP.Scheme

/-- For a scheme `X`, the canonical map `𝒪_X ⟶ 𝒦_X` to the sheaf of total quotient rings is a
monomorphism, and so is the induced map `𝒪_X^* ⟶ 𝒦_X^*` of unit-group sheaves. -/
@[mmp "lem_mmp_foundation_laz_structure_into_meromorphic"]
public theorem mono_toTotalQuotientSheaf_and_mono_unitGroupSheafMap
    (X : AlgebraicGeometry.Scheme.{u}) :
    Mono X.toTotalQuotientSheaf ∧ Mono (unitGroupSheafMap X.toTotalQuotientSheaf) :=
  ⟨Scheme.mono_toTotalQuotientSheaf X, (Scheme.shortExact_unitGroupSheaf X).mono_f⟩

end MMP.Scheme

/-!
## Blowing up a stratum of a simple normal crossing divisor

Let `Y` be a smooth variety over a perfect field `k` and `S_j` (`j ∈ Λ`, `Λ` finite) pairwise
distinct prime divisors on `Y` whose sum `∑_j S_j` is a simple normal crossing divisor. Let
`J ⊆ Λ` have at least two elements and let `Z` be an irreducible component of `⋂_{j ∈ J} S_j`,
with its reduced structure. Let `p : Y' = B_Z Y → Y` be the blow-up along `Z` and
`E = p⁻¹(Z)` the scheme-theoretic inverse image of the centre. Then `Z` is smooth of
codimension `|J|`, `Y'` is smooth, `E` is a smooth prime divisor, `p` is an isomorphism over
`Y ∖ Z`, and `E + ∑_j p⁻¹_* S_j` is again a simple normal crossing divisor. Moreover, for
`j ∈ J` the strict transform `p⁻¹_* S_j` meets `E` along a set mapping onto `Z`, and when
`J = {i, j}` has two elements, `p⁻¹_* S_i ∩ p⁻¹_* S_j ∩ E = ∅`.

### Main results

* `MMP.Resolution.blowUp_snc_stratum`: the statement above.

### Implementation notes

Snc divisors are `MMP.Mori.DivisorWithCoeffs.IsSNC`, applied to the reduced divisor
`∑_j 1 · S_j`; irreducible components are `MMP.Resolution.componentsOf`, the reduced structure
on a component is `MMP.Resolution.componentsFamily`, and codimension is
`MMP.Mori.closedsCodimension`. The blow-up is StacksDraft's `AlgebraicGeometry.blowUp` with
`AlgebraicGeometry.blowUpToBase`, the exceptional divisor is the ideal-theoretic inverse image
`Scheme.IdealSheafData.comap`, and strict transforms are
`MMP.Mori.inverseTransformPrimeDivisor`. The source works over an algebraically closed field;
the statement holds over any perfect field. Over an imperfect field it fails: in `𝔸²` the
smooth curves `y = 0` and `y = x^p - a` (`a` not a `p`-th power) cross transversally in a closed
point with inseparable residue field, which is not smooth over `k`.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [J. Kollár, *Lectures on resolution of singularities*, 3.24]
-/

namespace MMP.Resolution

/-! ### Proof

Let `Y` be a smooth variety over a perfect field `k`, `S_j` (`j ∈ Λ`) distinct prime divisors
with `∑_j S_j` snc, `J ⊆ Λ` with `2 ≤ |J|`, and `Z` an irreducible component of
`⋂_{j ∈ J} S_j`. The blow-up `p : B_Z Y → Y` is an isomorphism off `Z`; once `Z` is known to
be smooth, `B_Z Y` is smooth by
`MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup`.
In snc coordinates `z` at a point of `Z` the stalk of the ideal of `Z` is `(z_a : a ∈ s)` with
`|s| = |J|`; hence `Z` is smooth and, at its generic point, the maximal ideal is generated by
`|J|` parameters, so `Z` has codimension `|J|`. The exceptional divisor is the prime divisor
`MMP.Resolution.exceptionalPrimeDivisor`.

The generic point `ξ_j` of each `S_j` lies on no other `S_i`, so it is off `Z` and in the
biregular locus of `p`; if `p(ξ'_j) = ξ_j`, the strict transform `p⁻¹_* S_j` is the closure of
`ξ'_j`, which is the member `π⁻¹(S_j ∖ Z)‾` of the snc family
`MMP.Resolution.blowUpTransformFamily`. Hence `E + ∑_j p⁻¹_* S_j` is snc by
`MMP.Resolution.isSNCFamily_blowUpTransformFamily`. As `p` is closed, `p(p⁻¹_* S_j)` is a closed
set containing `ξ_j`, hence equal to `S_j ⊇ Z`, which gives `p(p⁻¹_* S_j ∩ E) = Z` for `j ∈ J`.
For `J = {i, j}` and a point `x` of `p⁻¹_* S_i ∩ p⁻¹_* S_j ∩ E` over `y ∈ Z`, write
`I_{Z,y} = (z_i, z_j)` and let `w_e, w_i, w_j` be the snc coordinates of `E`, `p⁻¹_* S_i`,
`p⁻¹_* S_j` at `x`. Then `w_e` generates `p^*(z_i, z_j)`, while `p^* z_i ∈ (w_e w_i)` and
`p^* z_j ∈ (w_e w_j)`; so `w_e ∈ w_e (w_i, w_j)`, which is impossible in the regular local ring
`𝒪_{B_Z Y, x}`. This replaces the chart computation of the source by a computation in the
local ring.
-/

/-- If the inverse image in `Spec 𝒪_{Y,y}` of a closed set `T` is `V(P)` for a prime `P`, then
the ideal of every irreducible component of `T` through `y` has stalk `P` at `y`. -/
private theorem stalk_componentsFamily_eq_of_preimage_eq_zeroLocus {Y : Scheme} {T : Set Y}
    (hT : IsClosed T) {y : Y} (P : Ideal (Y.presheaf.stalk y)) [hP : P.IsPrime]
    (hTy : Y.fromSpecStalk y ⁻¹' T = PrimeSpectrum.zeroLocus (P : Set (Y.presheaf.stalk y)))
    (V : componentsOf T) (hyV : y ∈ (V : Set Y)) :
    IdealSheafData.stalk (componentsFamily T V) y = P := by
  obtain ⟨ξ, hξT, hVξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hT V.2
  have hξy : ξ ⤳ y := specializes_iff_mem_closure.mpr (hVξ ▸ hyV)
  obtain ⟨q, hq⟩ : ξ ∈ Set.range (Y.fromSpecStalk y) := by
    rwa [Scheme.range_fromSpecStalk]
  have hstalk : IdealSheafData.stalk (componentsFamily T V) y = q.asIdeal := by
    have : componentsFamily T V = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({Y.fromSpecStalk y q} : Set Y)) := by
      unfold componentsFamily
      congr 1
      ext1
      rw [Closeds.coe_closure, Closeds.coe_closure, hq, ← hVξ,
        (Aux.isClosed_of_mem_componentsOf hT V.2).closure_eq]
    rw [this]
    exact Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk y q
  have hqT : q ∈ Y.fromSpecStalk y ⁻¹' T := by
    rwa [Set.mem_preimage, hq]
  rw [hTy] at hqT
  let p' : PrimeSpectrum (Y.presheaf.stalk y) := ⟨P, hP⟩
  have hp'q : p' ≤ q := (PrimeSpectrum.mem_zeroLocus _ _).1 hqT
  have hp'T : p' ∈ Y.fromSpecStalk y ⁻¹' T := by
    rw [hTy]; exact (PrimeSpectrum.mem_zeroLocus _ _).2 le_rfl
  have hsp : Y.fromSpecStalk y p' ⤳ ξ :=
    hq ▸ ((PrimeSpectrum.le_iff_specializes _ _).1 hp'q).map (Y.fromSpecStalk y).continuous
  have hsub : (V : Set Y) ⊆ closure {Y.fromSpecStalk y p'} := by
    rw [hVξ]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp))
      isClosed_closure
  have hcl : closure {Y.fromSpecStalk y p'} = (V : Set Y) :=
    (V.2.2 ⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.2 hp'T) hT⟩ hsub).antisymm hsub
  have hpq : p' = q := by
    apply (Y.fromSpecStalk y).isEmbedding.injective
    rw [hq]
    refine Inseparable.eq ?_
    rw [inseparable_iff_closure_eq, hcl, hVξ]
  rw [hstalk, ← hpq]

/-- An intersection of supports of prime divisors is closed. -/
private theorem isClosed_biInter_support {Y : Scheme} {Λ : Type*}
    (S : Λ → MMP.Mori.PrimeDivisor Y) (J : Finset Λ) :
    IsClosed (⋂ j ∈ J, ((S j).support : Set Y)) :=
  isClosed_biInter fun j _ => (S j).idealSheaf.support.isClosed

/-- Each `S i` has coefficient one in `∑_j S_j`, so lies in its support. -/
private theorem mem_support_sum_single {Y : Scheme} {Λ : Type*} [Fintype Λ]
    (S : Λ → MMP.Mori.PrimeDivisor Y) (hS : Function.Injective S) (i : Λ) :
    S i ∈ (∑ j, Finsupp.single (S j) (1 : ℤ)).support := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, hS.eq_iff]

/-- At a point `x` of a component `W` of `⋂_{j ∈ J} S_j`, in snc coordinates `z` at `x`, the
ideal of `W` has stalk `(z_a : a ∈ s)`, with `s` the coordinates `c(j)` of the `S_j`, `j ∈ J`, so
that `|s| = |J|`. -/
private theorem exists_stalk_component_eq_span {k : Type u} [Field k]
    {Y : Scheme} (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y]
    {Λ : Type*} [Fintype Λ] (S : Λ → MMP.Mori.PrimeDivisor Y) (hS : Function.Injective S)
    (hSNC : MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ)))
    (J : Finset Λ) (W : componentsOf (⋂ j ∈ J, ((S j).support : Set Y))) (x : Y)
    (hx : x ∈ (W : Set Y)) :
    ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk x) (c : {i // x ∈ (S i).support} → Fin n)
      (s : Finset (Fin n)), s.card = J.card ∧ MMP.Mori.IsRegularSystemOfParameters z ∧
      (∀ i, IdealSheafData.stalk (S i.1).idealSheaf x = Ideal.span {z (c i)}) ∧
      Function.Injective c ∧ (∀ a ∈ s, ∃ i, i.1 ∈ J ∧ c i = a) ∧ (∀ i, i.1 ∈ J → c i ∈ s) ∧
      IdealSheafData.stalk (componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W) x =
        Ideal.span (z '' (s : Set (Fin n))) := by
  classical
  obtain ⟨n, z, c, hz, hc, hI⟩ := hSNC.2 x
  have hxT : x ∈ (⋂ j ∈ J, ((S j).support : Set Y)) := W.2.1.2 hx
  have hxS : ∀ i ∈ J, x ∈ (S i).support := fun i hi => Set.mem_iInter₂.1 hxT i hi
  let f : J → Fin n := fun i => c ⟨S i.1, mem_support_sum_single S hS i.1, hxS i.1 i.2⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (hS (congrArg Subtype.val (hc hab)))
  refine ⟨n, z, fun i => c ⟨S i.1, mem_support_sum_single S hS i.1, i.2⟩, Finset.univ.image f,
    ?_, hz, fun i => hI ⟨S i.1, mem_support_sum_single S hS i.1, i.2⟩,
    fun a b hab => Subtype.ext (hS (congrArg Subtype.val (hc hab))),
    ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_coe]
  · intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    exact ⟨⟨i.1, hxS i.1 i.2⟩, i.2, rfl⟩
  · intro i hi
    exact Finset.mem_image.2 ⟨⟨i.1, hi⟩, Finset.mem_univ _, rfl⟩
  have hT : IsClosed (⋂ j ∈ J, ((S j).support : Set Y)) :=
    isClosed_biInter_support S J
  have hP := span_image_isPrime_of_isRegularSystemOfParameters hz (Finset.univ.image f)
  refine stalk_componentsFamily_eq_of_preimage_eq_zeroLocus hT _ ?_ W hx
  ext p
  rw [Set.mem_preimage, Set.mem_iInter₂]
  refine Iff.trans ?_ (PrimeSpectrum.mem_zeroLocus _ _).symm
  rw [SetLike.coe_subset_coe, Ideal.span_le]
  constructor
  · rintro h _ ⟨a, ha, rfl⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    have h1 := (fromSpecStalk_mem_support_iff_stalk_le (S i.1).idealSheaf x p).1 (h i.1 i.2)
    rw [hI ⟨S i.1, mem_support_sum_single S hS i.1, hxS i.1 i.2⟩, Ideal.span_le] at h1
    exact h1 rfl
  · intro h i hi
    refine (fromSpecStalk_mem_support_iff_stalk_le (S i).idealSheaf x p).2 ?_
    rw [hI ⟨S i, mem_support_sum_single S hS i, hxS i hi⟩, Ideal.span_le,
      Set.singleton_subset_iff]
    exact h ⟨f ⟨i, hi⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), rfl⟩

/-- An irreducible component of an intersection of `|J|` components of an snc divisor, with its
reduced structure, is smooth. -/
private theorem isSmoothScheme_component {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme} (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY)
    (hsm : MMP.Mori.IsSmoothScheme sY)
    {Λ : Type*} [Fintype Λ] (S : Λ → MMP.Mori.PrimeDivisor Y) (hS : Function.Injective S)
    (hSNC : MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ)))
    (J : Finset Λ)
    (W : componentsOf (⋂ j ∈ J, ((S j).support : Set Y))) :
    MMP.Mori.IsSmoothScheme
      ((componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W).subschemeι ≫ sY) := by
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : Smooth sY := (MMP.Mori.isSmoothScheme_iff sY).1 hsm
  set Z := componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W
  have hT : IsClosed (⋂ j ∈ J, ((S j).support : Set Y)) :=
    isClosed_biInter_support S J
  have hreg := (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sY).1
    inferInstance
  have hZsm : Smooth (Z.subschemeι ≫ sY) := by
    rw [MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
    intro y
    have hx : Z.subschemeι y ∈ (W : Set Y) := by
      have hy : Z.subschemeι y ∈ (Z.support : Set Y) := by
        rw [← Z.range_subschemeι]; exact ⟨y, rfl⟩
      rwa [SetLike.mem_coe, ← SetLike.mem_coe, coe_support_componentsFamily hT] at hy
    obtain ⟨n, z, -, s, -, hz, -, -, -, -, hstalk⟩ :=
      exists_stalk_component_eq_span sY S hS hSNC J W _ hx
    have := hreg (Z.subschemeι y)
    obtain ⟨hq, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz s
    rw [← hstalk] at hq
    let f := (Z.subschemeι.stalkMap y).hom
    let e := f.quotientKerEquivOfSurjective (Z.subschemeι.stalkMap_surjective y)
    have hk := Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk Z y
    rw [← hk] at hq
    exact IsRegularLocalRing.of_ringEquiv (R := _ ⧸ RingHom.ker f) e
  exact (MMP.Mori.isSmoothScheme_iff _).2 hZsm

/-- An irreducible component of an intersection of `|J|` components of an snc divisor has
codimension `|J|`. -/
private theorem closedsCodimension_component {k : Type u} [Field k]
    {Y : Scheme} (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY)
    {Λ : Type*} [Fintype Λ] (S : Λ → MMP.Mori.PrimeDivisor Y) (hS : Function.Injective S)
    (hSNC : MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ)))
    (J : Finset Λ)
    (W : componentsOf (⋂ j ∈ J, ((S j).support : Set Y))) :
    MMP.Mori.closedsCodimension (Closeds.closure (W : Set Y)) = J.card := by
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hT : IsClosed (⋂ j ∈ J, ((S j).support : Set Y)) := isClosed_biInter_support S J
  obtain ⟨η, -, hWη⟩ := Aux.exists_eq_closure_of_mem_componentsOf hT W.2
  have hηW : η ∈ (W : Set Y) := hWη ▸ subset_closure rfl
  obtain ⟨n, z, -, s, hs, hz, -, -, -, -, hst⟩ :=
    exists_stalk_component_eq_span sY S hS hSNC J W η hηW
  have hmax : IdealSheafData.stalk (componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W) η =
      IsLocalRing.maximalIdeal _ := by
    have : componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W =
        Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        ({Y.fromSpecStalk η (IsLocalRing.closedPoint _)} : Set Y)) := by
      unfold componentsFamily
      congr 1
      ext1
      rw [Closeds.coe_closure, Closeds.coe_closure, Scheme.fromSpecStalk_closedPoint, ← hWη]
      exact (Aux.isClosed_of_mem_componentsOf hT W.2).closure_eq
    rw [this]
    exact Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk η _
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨-, hd, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz s
  rw [← hst, hmax, ringKrullDim_eq_zero_of_isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance)] at hd
  have hsn : s.card ≤ n := (Finset.card_le_univ s).trans (Fintype.card_fin n).le
  have hn : n = s.card := by
    have := (Nat.cast_eq_zero (R := WithBot ℕ∞)).1 hd.symm
    omega
  have hdim := hz.2
  rw [ringKrullDim_stalk_eq_coheight, hn, hs] at hdim
  have hcl : Closeds.closure (W : Set Y) =
      ⟨(IrreducibleCloseds.closureSingleton η : Set Y),
        (IrreducibleCloseds.closureSingleton η).isClosed⟩ := by
    ext1
    rw [Closeds.coe_closure, hWη, closure_closure]
    rfl
  rw [hcl, MMP.Mori.closedsCodimension_coe, MMP.Flips.codimension_closureSingleton]
  exact_mod_cast hdim

/-- The generic point of `S_j` lies on no other `S_i`: its local ring has dimension one, so it
carries a single snc coordinate. -/
private theorem genericPoint_notMem_support {k : Type u} [Field k] {Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) {Λ : Type*} [Fintype Λ] (S : Λ → MMP.Mori.PrimeDivisor Y)
    (hS : Function.Injective S)
    (hSNC : MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ)))
    {i j : Λ} (hij : i ≠ j) :
    AlgebraicGeometry.PrimeDivisor.genericPoint (S j) ∉ (S i).support := by
  intro h
  have hξ : AlgebraicGeometry.PrimeDivisor.genericPoint (S j) ∈ (S j).support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  obtain ⟨n, z, c, hz, hc, -⟩ := hSNC.2 (AlgebraicGeometry.PrimeDivisor.genericPoint (S j))
  have hn : n = 1 := by
    have h1 := hz.2
    rw [ringKrullDim_stalk_eq_coheight,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  subst hn
  have := hc (Subsingleton.elim (c ⟨S i, mem_support_sum_single S hS i, h⟩)
    (c ⟨S j, mem_support_sum_single S hS j, hξ⟩))
  exact hij (hS (congrArg Subtype.val this))

/-- The members of an snc divisor `∑_j S_j` form an snc family. -/
private theorem isSNCFamily_idealSheaf {k : Type u} [Field k] {Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) {Λ : Type*} [Fintype Λ] (S : Λ → MMP.Mori.PrimeDivisor Y)
    (hS : Function.Injective S)
    (hSNC : MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ))) :
    IsSNCFamily sY (fun j => (S j).idealSheaf) := by
  refine ⟨fun j => ⟨?_, ?_, hSNC.1 _ (mem_support_sum_single S hS j)⟩, fun x => ?_⟩
  · have := (S j).integral; infer_instance
  · intro V hV
    set C := IrreducibleCloseds.closureSingleton (AlgebraicGeometry.PrimeDivisor.genericPoint (S j))
    have hC : (C : Set Y) = (S j).support :=
      (AlgebraicGeometry.PrimeDivisor.support_eq_closure _).symm
    have hVC : V = C := by
      have hVC : (V : Set Y) ⊆ C := hC ▸ hV.1
      exact le_antisymm hVC (hV.2 (y := C) (show (C : Set Y) ⊆ _ from hC.le) hVC)
    rw [hVC]
    exact AlgebraicGeometry.PrimeDivisor.codimension_closureSingleton_genericPoint _
  · obtain ⟨n, z, c, hz, hc, hI⟩ := hSNC.2 x
    exact ⟨n, z, fun i => c ⟨S i.1, mem_support_sum_single S hS i.1, i.2⟩, hz,
      fun i => hI ⟨S i.1, mem_support_sum_single S hS i.1, i.2⟩,
      fun a b hab => Subtype.ext (hS (congrArg Subtype.val (hc hab)))⟩

/-- A component of `⋂_{j ∈ J} S_j` has simple normal crossings with the snc family `S_j`. -/
private theorem hasSNCWith_component {k : Type u} [Field k] {Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] {Λ : Type*} [Fintype Λ]
    (S : Λ → MMP.Mori.PrimeDivisor Y) (hS : Function.Injective S)
    (hSNC : MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ)))
    (J : Finset Λ) (W : componentsOf (⋂ j ∈ J, ((S j).support : Set Y))) :
    HasSNCWith (fun j => (S j).idealSheaf)
      (componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W) := by
  intro x hx
  have hT : IsClosed (⋂ j ∈ J, ((S j).support : Set Y)) :=
    isClosed_biInter_support S J
  rw [coe_support_componentsFamily hT] at hx
  obtain ⟨n, z, c, s, -, hz, hc, hinj, -, -, hst⟩ :=
    exists_stalk_component_eq_span sY S hS hSNC J W x hx
  exact ⟨n, z, c, s, hz, hc, hinj, hst⟩

/-- A member of an snc family with irreducible support is a prime divisor. -/
private theorem exists_primeDivisor_of_isSNCFamily {k : Type u} [Field k] {X : Scheme}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

/-- A morphism hits every point of its biregular locus. -/
private theorem exists_eq_of_mem_biregularLocus {X Y : Scheme} (g : X ⟶ Y) {y : Y}
    (hy : y ∈ MMP.Mori.biregularLocus g) : ∃ a, g a = y := by
  have : IsIso (g ∣_ MMP.Mori.biregularLocus g) := MMP.Mori.isBiregular_biregularLocus g
  let y' : (MMP.Mori.biregularLocus g).toScheme := ⟨y, hy⟩
  have hb : (g ∣_ MMP.Mori.biregularLocus g) (inv (g ∣_ MMP.Mori.biregularLocus g) y') = y' := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  refine ⟨(g ⁻¹ᵁ MMP.Mori.biregularLocus g).ι (inv (g ∣_ MMP.Mori.biregularLocus g) y'), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hb]
  rfl

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : MMP.Mori.DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A component of `E + ∑_j S'_j` is `E` or one of the `S'_j`. -/
private theorem mem_support_add_sum_single {X : Scheme} {Λ : Type*} [Fintype Λ]
    (E : MMP.Mori.PrimeDivisor X) (S' : Λ → MMP.Mori.PrimeDivisor X) {P : MMP.Mori.PrimeDivisor X}
    (hP : P ∈ (Finsupp.single E (1 : ℤ) + ∑ j, Finsupp.single (S' j) (1 : ℤ)).support) :
    P = E ∨ ∃ j, S' j = P := by
  classical
  rcases Finset.mem_union.1 (Finsupp.support_add hP) with h | h
  · exact Or.inl (Finset.mem_singleton.1 (Finsupp.support_single_subset h))
  · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum h)
    exact Or.inr ⟨j, (Finset.mem_singleton.1 (Finsupp.support_single_subset hj)).symm⟩

/-- In a regular local ring with regular system of parameters `w`, if `f ∈ (w_a) ∩ (w_e)` and
`g ∈ (w_b) ∩ (w_e)` with `e ∉ {a, b}`, then `w_e ∉ (f, g)`. -/
private theorem notMem_span_pair_of_isRegularSystemOfParameters {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {N : ℕ} {w : Fin N → R}
    (hw : MMP.Mori.IsRegularSystemOfParameters w)
    {e a b : Fin N} (hea : e ≠ a) (heb : e ≠ b) {f g : R} (hfa : f ∈ Ideal.span {w a})
    (hfe : f ∈ Ideal.span {w e}) (hgb : g ∈ Ideal.span {w b}) (hge : g ∈ Ideal.span {w e}) :
    w e ∉ Ideal.span {f, g} := by
  intro h
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw
  have := IsRegularLocalRing.isDomain R
  have hle : ∀ c, Ideal.span {w c} ≤ IsLocalRing.maximalIdeal R := fun c => by
    rw [← hw.1]; exact Ideal.span_mono (Set.singleton_subset_iff.2 ⟨c, rfl⟩)
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hfe
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hge
  have hr : r ∈ Ideal.span {w a} :=
    ((span_singleton_isPrime_of_isRegularSystemOfParameters hw a).mem_or_mem hfa).resolve_right
      (notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw hea.symm)
  have ht : t ∈ Ideal.span {w b} :=
    ((span_singleton_isPrime_of_isRegularSystemOfParameters hw b).mem_or_mem hgb).resolve_right
      (notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw heb.symm)
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 h
  have hne : w e ≠ 0 := fun h0 =>
    notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw hea.symm
      (h0 ▸ (Ideal.span {w a}).zero_mem)
  have h1 : x * r + y * t = 1 := by
    have : w e * (x * r + y * t - 1) = 0 := by rw [← sub_eq_zero.2 hxy]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)
  apply (IsLocalRing.maximalIdeal R).ne_top_iff_one.1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hle a hr)) (Ideal.mul_mem_left _ _ (hle b ht))

/-- If `f` maps the support of `I` into the support of `K`, then at every prime `q` of
`𝒪_{X,x}` containing the stalk of `I`, the stalk of `K` at `f x` pulls back into `q`. -/
private theorem stalk_le_comap_of_image_support_subset {X Y : Scheme} (f : X ⟶ Y)
    {I : X.IdealSheafData} {K : Y.IdealSheafData}
    (h : f '' (I.support : Set X) ⊆ K.support) (x : X) {q : Ideal (X.presheaf.stalk x)}
    [hq : q.IsPrime] (hIq : IdealSheafData.stalk I x ≤ q) :
    IdealSheafData.stalk K (f x) ≤ q.comap (f.stalkMap x).hom := by
  let q' : PrimeSpectrum (X.presheaf.stalk x) := ⟨q, hq⟩
  have h1 : X.fromSpecStalk x q' ∈ (I.support : Set X) :=
    (fromSpecStalk_mem_support_iff_stalk_le I x q').2 hIq
  have h2 : f (X.fromSpecStalk x q') =
      Y.fromSpecStalk (f x) (PrimeSpectrum.comap (f.stalkMap x).hom q') := by
    change (X.fromSpecStalk x ≫ f) q' = _
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x)]
    rfl
  exact (fromSpecStalk_mem_support_iff_stalk_le K (f x) _).1 (h2 ▸ h ⟨_, h1, rfl⟩)

/-- If a point `x` of the blow-up along `I` lies over the generic point of `S_j`, off `I`, then
the `S_j`-member of `blowUpTransformFamily` is the inverse transform of `S_j`, whose support is
the closure of `x`. -/
private theorem blowUpTransformFamily_inl_eq_inverseTransformIdeal {Y : Scheme} {Λ : Type*}
    (S : Λ → MMP.Mori.PrimeDivisor Y) {I : Y.IdealSheafData}
    (hreg : ∀ y : Y, y ∉ (I.support : Set Y) → y ∈ MMP.Mori.biregularLocus (blowUpToBase I))
    {j : Λ} (hj : AlgebraicGeometry.PrimeDivisor.genericPoint (S j) ∉ (I.support : Set Y))
    {x : blowUp I} (hx : blowUpToBase I x = AlgebraicGeometry.PrimeDivisor.genericPoint (S j)) :
    blowUpTransformFamily (fun j => (S j).idealSheaf) I (Sum.inl j) =
        MMP.Mori.inverseTransformIdeal (blowUpToBase I) (S j).idealSheaf.support ∧
      ((MMP.Mori.inverseTransform (blowUpToBase I) (S j).idealSheaf.support : Closeds _) :
        Set (blowUp I)) = closure {x} := by
  have hSξ : ((S j).support : Set Y) =
      closure {AlgebraicGeometry.PrimeDivisor.genericPoint (S j)} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure _
  have hξS : AlgebraicGeometry.PrimeDivisor.genericPoint (S j) ∈ (S j).support := by
    rw [hSξ]; exact subset_closure rfl
  have hpre : blowUpToBase I ⁻¹'
      (((S j).support : Set Y) ∩ MMP.Mori.biregularLocus (blowUpToBase I)) ⊆ closure {x} := by
    intro y hy
    rw [← specializes_iff_mem_closure]
    refine MMP.Threefold.Resolution.specializes_of_mem_biregularLocus _
      (by rw [hx]; exact hreg _ hj) hy.2 ?_
    rw [hx, specializes_iff_mem_closure, ← hSξ]
    exact hy.1
  have hinv : ((MMP.Mori.inverseTransform (blowUpToBase I) (S j).idealSheaf.support : Closeds _) :
      Set (blowUp I)) = closure {x} := by
    rw [MMP.Mori.inverseTransform, Closeds.coe_closure]
    refine (closure_minimal hpre isClosed_closure).antisymm (closure_minimal ?_ isClosed_closure)
    rw [Set.singleton_subset_iff]
    refine subset_closure ?_
    rw [Set.mem_preimage, hx]
    exact ⟨hξS, hreg _ hj⟩
  refine ⟨?_, hinv⟩
  rw [blowUpTransformFamily, Sum.elim_inl, MMP.Mori.inverseTransformIdeal]
  congr 1
  ext1
  rw [Closeds.coe_closure, hinv]
  refine (closure_minimal (fun y hy => hpre ⟨hy.1, hreg _ hy.2⟩) isClosed_closure).antisymm
    (closure_mono ?_)
  rw [Set.singleton_subset_iff, Set.mem_preimage, hx]
  exact ⟨hξS, hj⟩

/-- On the blow-up along `I`, every `S_j` whose generic point is off `I` has a strict transform
`S'_j`, the closure of a point `pt j` over that generic point, which is the `S_j`-member of
`blowUpTransformFamily`. -/
private theorem exists_strictTransform_points {k : Type u} [Field k] {Y : Scheme}
    {sY : Y ⟶ Spec (.of k)} {Λ : Type*} (S : Λ → MMP.Mori.PrimeDivisor Y) {I : Y.IdealSheafData}
    (hF : IsSNCFamily (blowUpToBase I ≫ sY) (blowUpTransformFamily (fun j => (S j).idealSheaf) I))
    (hreg : ∀ y : Y, y ∉ (I.support : Set Y) → y ∈ MMP.Mori.biregularLocus (blowUpToBase I))
    (hξ : ∀ j, AlgebraicGeometry.PrimeDivisor.genericPoint (S j) ∉ (I.support : Set Y)) :
    ∃ (pt : Λ → blowUp I) (S' : Λ → MMP.Mori.PrimeDivisor (blowUp I)),
      (∀ j, blowUpToBase I (pt j) = AlgebraicGeometry.PrimeDivisor.genericPoint (S j)) ∧
      (∀ j, ((S' j).support : Set (blowUp I)) = closure {pt j}) ∧
      (∀ j, (S' j).idealSheaf = blowUpTransformFamily (fun j => (S j).idealSheaf) I (Sum.inl j)) ∧
      ∀ j, MMP.Mori.inverseTransformPrimeDivisor (blowUpToBase I) (S j) = some (S' j) := by
  choose pt hpt using fun j => exists_eq_of_mem_biregularLocus _ (hreg _ (hξ j))
  have hC := fun j => blowUpTransformFamily_inl_eq_inverseTransformIdeal S hreg (hξ j) (hpt j)
  choose S' hS' using fun j => exists_primeDivisor_of_isSNCFamily hF (Sum.inl j) (by
    rw [(hC j).1, MMP.Mori.support_inverseTransformIdeal, (hC j).2]
    exact isIrreducible_singleton.closure)
  have hξS : ∀ j, AlgebraicGeometry.PrimeDivisor.genericPoint (S j) ∈ (S j).support := fun j => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  refine ⟨pt, S', hpt, fun j => ?_, hS', fun j =>
    MMP.Mori.inverseTransformPrimeDivisor_eq_some_iff.2
      ⟨⟨_, hξS j, hreg _ (hξ j)⟩, (hS' j).trans (hC j).1⟩⟩
  change ((S' j).idealSheaf.support : Set (blowUp I)) = _
  rw [hS', (hC j).1, MMP.Mori.support_inverseTransformIdeal, (hC j).2]

/-- In a finset of two elements containing distinct `i` and `j`, every element is `i` or `j`. -/
private theorem eq_or_eq_of_card_eq_two {α : Type*} {s : Finset α} (hs : s.card = 2) {i j : α}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) : ∀ l ∈ s, l = i ∨ l = j := by
  classical
  intro l hl
  by_contra! h
  have hsub : ({i, j, l} : Finset α) ⊆ s := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hij, Ne.symm h.1]),
    Finset.card_pair (Ne.symm h.2)] at this
  omega

/-- A closed map `p` sends `closure {x} ∩ p⁻¹(W)` onto `W` when `W ⊆ closure {p x}`. -/
private theorem image_closure_inter_preimage_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {p : X → Y} (hp : IsClosedMap p) {x : X} {W : Set Y}
    (hW : W ⊆ closure {p x}) : p '' (closure {x} ∩ p ⁻¹' W) = W := by
  rw [Set.image_inter_preimage, Set.inter_eq_right]
  exact hW.trans (closure_minimal (Set.singleton_subset_iff.2 ⟨x, subset_closure rfl, rfl⟩)
    (hp _ isClosed_closure))

/-- For `J = {i, j}`, the strict transforms of `S_i` and `S_j` do not meet on the exceptional
divisor `E = p⁻¹(Z)` of the blow-up along the component `Z` of `S_i ∩ S_j`. -/
private theorem inter_inter_exceptional_eq_empty {k : Type u} [Field k] {Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] {Λ : Type*} [Fintype Λ]
    (S : Λ → MMP.Mori.PrimeDivisor Y) (hS : Function.Injective S)
    (hSNC : MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ)))
    {J : Finset Λ} (hJ2 : J.card = 2) (W : componentsOf (⋂ j ∈ J, ((S j).support : Set Y)))
    {I : Y.IdealSheafData} (hI : componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W = I)
    [IsLocallyNoetherian (blowUp I)]
    (hF : IsSNCFamily (blowUpToBase I ≫ sY) (blowUpTransformFamily (fun j => (S j).idealSheaf) I))
    {S' : Λ → MMP.Mori.PrimeDivisor (blowUp I)}
    (hS' : ∀ j, (S' j).idealSheaf = blowUpTransformFamily (fun j => (S j).idealSheaf) I (Sum.inl j))
    (hmapS' : ∀ j, blowUpToBase I '' (S' j).support ⊆ (S j).support)
    {E : MMP.Mori.PrimeDivisor (blowUp I)} (hE : E.idealSheaf = I.comap (blowUpToBase I))
    (hEsupp : (E.support : Set (blowUp I)) = blowUpToBase I ⁻¹' W)
    {i j : Λ} (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j) :
    ((S' i).support ∩ (S' j).support ∩ E.support : Set (blowUp I)) = ∅ := by
  set p := blowUpToBase I
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨hxi, hxj⟩, hxE⟩
  have hyW : p x ∈ (W : Set Y) := by rwa [hEsupp] at hxE
  have hyi : p x ∈ (S i).support := Set.mem_iInter₂.1 (W.2.1.2 hyW) i hi
  have hyj : p x ∈ (S j).support := Set.mem_iInter₂.1 (W.2.1.2 hyW) j hj
  obtain ⟨n, z, c, s, -, hz, hc, -, hs, hs', hst⟩ :=
    exists_stalk_component_eq_span sY S hS hSNC J W (p x) hyW
  rw [hI] at hst
  obtain ⟨N, w, c', hw, hc', hinj'⟩ := hF.2 x
  have hxi' : x ∈ (blowUpTransformFamily (fun j => (S j).idealSheaf) I (Sum.inl i)).support := by
    rwa [← hS' i]
  have hxj' : x ∈ (blowUpTransformFamily (fun j => (S j).idealSheaf) I (Sum.inl j)).support := by
    rwa [← hS' j]
  have hxE' : x ∈ (blowUpTransformFamily (fun j => (S j).idealSheaf) I (Sum.inr ())).support := by
    change x ∈ (I.comap p).support
    rwa [← hE]
  have hei : c' ⟨_, hxE'⟩ ≠ c' ⟨_, hxi'⟩ := fun h => Sum.inr_ne_inl (congrArg Subtype.val (hinj' h))
  have hej : c' ⟨_, hxE'⟩ ≠ c' ⟨_, hxj'⟩ := fun h => Sum.inr_ne_inl (congrArg Subtype.val (hinj' h))
  have hEst : Ideal.span {w (c' ⟨_, hxE'⟩)} =
      Ideal.map (p.stalkMap x).hom (Ideal.span (z '' (s : Set (Fin n)))) := by
    rw [← hc' ⟨_, hxE'⟩, ← hst]
    exact IdealSheafData.stalk_comap I p x
  have key : ∀ (l : Λ) (hyl : p x ∈ (S l).support) (b : Fin N),
      IdealSheafData.stalk (S' l).idealSheaf x = Ideal.span {w b} →
        (p.stalkMap x).hom (z (c ⟨l, hyl⟩)) ∈ Ideal.span {w b} := by
    intro l hyl b hb
    have := span_singleton_isPrime_of_isRegularSystemOfParameters hw b
    have h := stalk_le_comap_of_image_support_subset p (hmapS' l) x hb.le
    rwa [hc ⟨l, hyl⟩, Ideal.span_singleton_le_iff_mem] at h
  have hfi := key i hyi _ (by rw [hS' i]; exact hc' ⟨_, hxi'⟩)
  have hfj := key j hyj _ (by rw [hS' j]; exact hc' ⟨_, hxj'⟩)
  have hfE : ∀ (l : Λ) (hyl : p x ∈ (S l).support), l ∈ J →
      (p.stalkMap x).hom (z (c ⟨l, hyl⟩)) ∈ Ideal.span {w (c' ⟨_, hxE'⟩)} := by
    intro l hyl hlJ
    rw [hEst]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨_, hs' ⟨l, hyl⟩ hlJ, rfl⟩)
  refine notMem_span_pair_of_isRegularSystemOfParameters hw hei hej hfi (hfE i hyi hi)
    hfj (hfE j hyj hj) ?_
  have hmem : w (c' ⟨_, hxE'⟩) ∈ Ideal.span ((p.stalkMap x).hom '' (z '' (s : Set (Fin n)))) := by
    rw [← Ideal.map_span, ← hEst]
    exact Ideal.mem_span_singleton_self _
  refine Ideal.span_le.2 ?_ hmem
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  obtain ⟨l, hlJ, rfl⟩ := hs m hm
  rcases eq_or_eq_of_card_eq_two hJ2 hi hj hij _ hlJ with h | h
  · obtain rfl : l = ⟨i, hyi⟩ := Subtype.ext h
    exact Ideal.subset_span (Set.mem_insert _ _)
  · obtain rfl : l = ⟨j, hyj⟩ := Subtype.ext h
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- The strict transforms of the `S_j` on the blow-up of an snc stratum, against the exceptional
divisor `E = p⁻¹(Z)`. -/
private theorem exists_strictTransforms {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme} (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY)
    {Λ : Type*} [Fintype Λ] (S : Λ → MMP.Mori.PrimeDivisor Y) (hS : Function.Injective S)
    (hSNC : MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ)))
    (J : Finset Λ) (hJ : 2 ≤ J.card)
    (W : componentsOf (⋂ j ∈ J, ((S j).support : Set Y)))
    (E : MMP.Mori.PrimeDivisor
      (blowUp (componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W)))
    (hE : E.idealSheaf = (componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W).comap
      (blowUpToBase (componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W))) :
    let I := componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W
    let p := blowUpToBase I
    ∃ S' : Λ → MMP.Mori.PrimeDivisor (blowUp I),
      (∀ j, MMP.Mori.inverseTransformPrimeDivisor p (S j) = some (S' j)) ∧
      Function.Injective S' ∧ (∀ j, S' j ≠ E) ∧
      MMP.Mori.DivisorWithCoeffs.IsSNC (p ≫ sY)
        (Finsupp.single E (1 : ℤ) + ∑ j, Finsupp.single (S' j) (1 : ℤ)) ∧
      (∀ j ∈ J, p '' ((S' j).support ∩ E.support) = (W : Set Y)) ∧
      (J.card = 2 → ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
        ((S' i).support ∩ (S' j).support ∩ E.support : Set (blowUp I)) = ∅) := by
  intro I p
  classical
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : QuasiCompact sY := ((MMP.Mori.isVariety_iff k sY).1 hY).2.2.2
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian p
  have hsupp : (I.support : Set Y) = W :=
    coe_support_componentsFamily (isClosed_biInter_support S J) W
  have hF := isSNCFamily_blowUpTransformFamily sY (isSNCFamily_idealSheaf sY S hS hSNC)
    (hasSNCWith_component sY S hS hSNC J W)
  have hWB : ∀ y : Y, y ∉ (I.support : Set Y) → y ∈ MMP.Mori.biregularLocus p :=
    fun _ hy => MMP.Mori.le_biregularLocus (inferInstance : IsIso (p ∣_ I.support.compl)) hy
  have hξW : ∀ j, AlgebraicGeometry.PrimeDivisor.genericPoint (S j) ∉ (I.support : Set Y) := by
    intro j hj
    rw [hsupp] at hj
    obtain ⟨i, hiJ, hij⟩ := Finset.exists_mem_ne hJ j
    exact genericPoint_notMem_support sY S hS hSNC hij (Set.mem_iInter₂.1 (W.2.1.2 hj) i hiJ)
  obtain ⟨pt, S', hpt, hS'supp, hS', hpS'⟩ :=
    exists_strictTransform_points (I := I) S hF hWB hξW
  have hEsupp : (E.support : Set (blowUp I)) = p ⁻¹' W := by
    change (E.idealSheaf.support : Set (blowUp I)) = _
    rw [hE, Scheme.IdealSheafData.support_comap, ← hsupp]
    rfl
  have hmapS' : ∀ j, p '' (S' j).support ⊆ (S j).support := fun j => by
    rw [hS'supp, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine (image_closure_subset_closure_image p.continuous).trans ?_
    rw [Set.image_singleton, hpt]
  refine ⟨S', hpS', ?_, ?_, ?_, ?_, fun hJ2 i hi j hj hij => inter_inter_exceptional_eq_empty
    sY S hS hSNC hJ2 W (I := I) rfl hF hS' hmapS' hE hEsupp hi hj hij⟩
  · intro i j hij
    by_contra hne
    have h1 : pt j ∈ (S' i).support := by rw [hij, hS'supp]; exact subset_closure rfl
    have h2 : AlgebraicGeometry.PrimeDivisor.genericPoint (S j) ∈ (S i).support := by
      rw [← hpt j]; exact hmapS' i ⟨pt j, h1, rfl⟩
    exact genericPoint_notMem_support sY S hS hSNC hne h2
  · intro j h
    have : pt j ∈ E.support := by rw [← h, hS'supp]; exact subset_closure rfl
    rw [hEsupp, Set.mem_preimage, hpt] at this
    exact hξW j (by rwa [hsupp])
  · refine isSNC_of_isSNCFamily hF _ fun P hP => ?_
    rcases mem_support_add_sum_single E S' hP with rfl | ⟨j, rfl⟩
    · exact ⟨Sum.inr (), hE.symm⟩
    · exact ⟨Sum.inl j, (hS' j).symm⟩
  · intro j hj
    rw [hS'supp, hEsupp]
    refine image_closure_inter_preimage_eq p.isClosedMap ?_
    rw [hpt]
    exact fun y hy => (AlgebraicGeometry.PrimeDivisor.support_eq_closure (S j)).le
      (Set.mem_iInter₂.1 (W.2.1.2 hy) j hj)

/-- The exceptional divisor and the strict transforms of the blow-up of an snc stratum. -/
private theorem exists_exceptional_strictTransforms {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme} (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY)
    (hsm : MMP.Mori.IsSmoothScheme sY)
    {Λ : Type*} [Fintype Λ] (S : Λ → MMP.Mori.PrimeDivisor Y) (hS : Function.Injective S)
    (hSNC : MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ)))
    (J : Finset Λ) (hJ : 2 ≤ J.card)
    (W : componentsOf (⋂ j ∈ J, ((S j).support : Set Y)))
    (hZ : MMP.Mori.IsSmoothScheme
      ((componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W).subschemeι ≫ sY)) :
    let I := componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W
    let p := blowUpToBase I
    ∃ (E : MMP.Mori.PrimeDivisor (blowUp I)) (S' : Λ → MMP.Mori.PrimeDivisor (blowUp I)),
      E.idealSheaf = I.comap p ∧
      MMP.Mori.IsSmoothScheme (E.idealSheaf.subschemeι ≫ p ≫ sY) ∧
      (∀ j, MMP.Mori.inverseTransformPrimeDivisor p (S j) = some (S' j)) ∧
      Function.Injective S' ∧ (∀ j, S' j ≠ E) ∧
      MMP.Mori.DivisorWithCoeffs.IsSNC (p ≫ sY)
        (Finsupp.single E (1 : ℤ) + ∑ j, Finsupp.single (S' j) (1 : ℤ)) ∧
      (∀ j ∈ J, p '' ((S' j).support ∩ E.support) = (W : Set Y)) ∧
      (J.card = 2 → ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
        ((S' i).support ∩ (S' j).support ∩ E.support : Set (blowUp I)) = ∅) := by
  intro I p
  have hT : IsClosed (⋂ j ∈ J, ((S j).support : Set Y)) :=
    isClosed_biInter_support S J
  have hsupp : (I.support : Set Y) = W := coe_support_componentsFamily hT W
  have hirr : IsIrreducible (I.support : Set Y) := hsupp ▸ W.2.1.1
  have hcodim : 1 ≤ codimension
      (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) := by
    rw [← MMP.Mori.closedsCodimension_coe]
    have h := closedsCodimension_component sY hY S hS hSNC J W
    have hcl : Closeds.closure (W : Set Y) = I.support := by
      ext1
      rw [Closeds.coe_closure, ← hsupp, I.support.isClosed.closure_eq]
    rw [hcl] at h
    change 1 ≤ MMP.Mori.closedsCodimension I.support
    rw [h]
    exact_mod_cast (by omega : 1 ≤ J.card)
  have hbl : IsSmoothBlowup sY I := ⟨hsm, hZ⟩
  obtain ⟨-, F, hF, -, -⟩ :=
    isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal sY I hbl hirr hcodim
  have hFI : F.idealSheaf = I.comap p := hF
  obtain ⟨S', h1, h2, h3, h4, h5, h6⟩ :=
    exists_strictTransforms sY hY S hS hSNC J hJ W F hFI
  have hsmE := (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup
    sY I hbl).2.1
  refine ⟨F, S', hFI, ?_, h1, h2, h3, h4, h5, h6⟩
  rw [hF]
  exact MMP.Mori.isSmoothScheme_of_smooth hsmE

/-- **Blowing up a stratum of an snc divisor.** Let `Y` be a smooth variety over a perfect
field `k`, `S : Λ → PrimeDivisor Y` a finite family of distinct prime divisors with
`∑_j S_j` snc, `J ⊆ Λ` with `2 ≤ |J|`, and `W` an irreducible component of `⋂_{j ∈ J} S_j`
with reduced ideal `I`. Let `p : B_I Y → Y` be the blow-up. Then `W` is smooth of
codimension `|J|`, `B_I Y` is smooth, the inverse image `I.comap p` is the ideal of a smooth
prime divisor `E`, `p` is an isomorphism over `Y ∖ W`, the strict transforms `S'_j = p⁻¹_* S_j`
are prime divisors with `E + ∑_j S'_j` snc, `p (S'_j ∩ E) = W` for `j ∈ J`, and
`S'_i ∩ S'_j ∩ E = ∅` when `J = {i, j}` has two elements. -/
@[mmp "lem_mmp_foundation_snc_stratum_blowup"]
public theorem blowUp_snc_stratum {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY) (hsm : MMP.Mori.IsSmoothScheme sY)
    {Λ : Type*} [Fintype Λ] (S : Λ → MMP.Mori.PrimeDivisor Y) (hS : Function.Injective S)
    (hSNC : MMP.Mori.DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ)))
    (J : Finset Λ) (hJ : 2 ≤ J.card)
    (W : componentsOf (⋂ j ∈ J, ((S j).support : Set Y))) :
    let I := componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) W
    let p := blowUpToBase I
    MMP.Mori.IsSmoothScheme (I.subschemeι ≫ sY) ∧
      MMP.Mori.closedsCodimension (Closeds.closure (W : Set Y)) = J.card ∧
      MMP.Mori.IsSmoothScheme (p ≫ sY) ∧
      IsIso (p ∣_ I.support.compl) ∧
      ∃ (E : MMP.Mori.PrimeDivisor (blowUp I)) (S' : Λ → MMP.Mori.PrimeDivisor (blowUp I)),
        E.idealSheaf = I.comap p ∧
        MMP.Mori.IsSmoothScheme (E.idealSheaf.subschemeι ≫ p ≫ sY) ∧
        (∀ j, MMP.Mori.inverseTransformPrimeDivisor p (S j) = some (S' j)) ∧
        Function.Injective S' ∧ (∀ j, S' j ≠ E) ∧
        MMP.Mori.DivisorWithCoeffs.IsSNC (p ≫ sY)
          (Finsupp.single E (1 : ℤ) + ∑ j, Finsupp.single (S' j) (1 : ℤ)) ∧
        (∀ j ∈ J, p '' ((S' j).support ∩ E.support) = (W : Set Y)) ∧
        (J.card = 2 → ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
          ((S' i).support ∩ (S' j).support ∩ E.support : Set (blowUp I)) = ∅) := by
  intro I p
  have hZ := isSmoothScheme_component sY hY hsm S hS hSNC J W
  have hbl := MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I
    ⟨hsm, hZ⟩
  exact ⟨hZ, closedsCodimension_component sY hY S hS hSNC J W,
    MMP.Mori.isSmoothScheme_of_smooth hbl.1, inferInstance,
    exists_exceptional_strictTransforms sY hY hsm S hS hSNC J hJ W hZ⟩

end MMP.Resolution

/-!
## The Milnor sequence for a tower of cochain complexes

Let `C : ℕᵒᵖ ⥤ CochainComplex AddCommGrpCat ℤ` be a tower of cochain complexes of abelian
groups whose transition maps `C_{j+1} ⟶ C_j` are surjective in every degree, and let `c` be a
limit cone of `C`. For a tower of abelian groups `G : ℕᵒᵖ ⥤ AddCommGrpCat`, the group
`lim¹ G` is the cokernel of the map `∏ G_j ⟶ ∏ G_j`, `(x_j) ↦ (x_j - t(x_{j+1}))`, whose kernel
is `lim G`. For `n + 1 = m` there is a short exact sequence
`0 ⟶ lim¹_j H^n(C_j) ⟶ H^m(c.pt) ⟶ lim_j H^m(C_j) ⟶ 0`,
whose second map is induced by the projections `c.pt ⟶ C_j`. If every transition map
`H^m(C_{j+1}) ⟶ H^m(C_j)` vanishes, then `lim_j H^m(C_j)` and `lim¹_j H^m(C_j)` are zero.

### Main results

* `MMP.Analytic.milnor_sequence`

### Implementation notes

Mathlib has no `lim¹`; it appears in the statement as the explicit cokernel of the map
`∏ G_j ⟶ ∏ G_j` above, built with `Pi.lift`.
The degree `n - 1` of the source is written as a pair `n + 1 = m`, the convention of
`ComplexShape.up ℤ`.
-/

namespace MMP.Analytic

/-! ### Proof

For a tower `C` of cochain complexes of abelian groups with degreewise surjective transition
maps and limit `c`, the map `Δ : ∏ C_j ⟶ ∏ C_j`, `(x_j) ↦ (x_j - t(x_{j+1}))`, is degreewise
surjective with kernel `c.pt`. The long exact cohomology sequence of
`0 ⟶ c.pt ⟶ ∏ C_j ⟶ ∏ C_j ⟶ 0`, together with `H^p(∏ C_j) ≅ ∏ H^p(C_j)`, gives the
short exact sequence `0 ⟶ lim¹ H^n(C_j) ⟶ H^m(c.pt) ⟶ lim H^m(C_j) ⟶ 0`.

The long exact cohomology sequence of a short exact sequence of complexes is broken at the
connecting map into `0 ⟶ coker H^n(S.g) ⟶ H^m(S.X₁) ⟶ ker H^m(S.g) ⟶ 0`
(`shortExact_cokernel_desc_δ_kernel_lift`); the Milnor sequence is its transport along the
comparison isomorphism `H^p(∏ C_j) ≅ ∏ H^p(C_j)`, which is proved for complexes of abelian
groups elementwise, through cycles and boundaries. The limit of a tower is identified with the
kernel of `Δ` in any preadditive category.
-/

open Limits Opposite HomologicalComplex

/-- Two elements of the cone point of a limit fan of abelian groups agree when all their
projections agree. -/
private lemma fan_ext {ι : Type} {X : ι → AddCommGrpCat.{0}} {F : Fan X} (hF : IsLimit F)
    {a b : F.pt} (h : ∀ j, F.proj j a = F.proj j b) : a = b :=
  Concrete.isLimit_ext _ hF a b fun ⟨j⟩ => h j

/-- A family of elements of the factors of a limit fan of abelian groups comes from an element
of its cone point. -/
private lemma fan_exists {ι : Type} {X : ι → AddCommGrpCat.{0}} {F : Fan X} (hF : IsLimit F)
    (x : ∀ j, X j) : ∃ a : F.pt, ∀ j, F.proj j a = x j := by
  let s : Fan X := Fan.mk (AddCommGrpCat.of ℤ) fun j => AddCommGrpCat.ofHom (zmultiplesHom _ (x j))
  refine ⟨hF.lift s (1 : ℤ), fun j => ?_⟩
  change (hF.lift s ≫ F.π.app ⟨j⟩) (1 : ℤ) = _
  rw [hF.fac]
  simp [s]

section Tower

variable {D : Type*} [Category* D] [Preadditive D] (G : ℕᵒᵖ ⥤ D)
  [HasProduct fun j : ℕ => G.obj (op j)]

/-- The map `(x_j) ↦ (x_j - t(x_{j+1}))` on the product of a tower. -/
private noncomputable def towerDelta :
    (∏ᶜ fun j : ℕ => G.obj (op j)) ⟶ ∏ᶜ fun j : ℕ => G.obj (op j) :=
  Pi.lift fun j => Pi.π _ j - Pi.π _ (j + 1) ≫ G.map (homOfLE (Nat.le_succ j)).op

private lemma towerDelta_π (j : ℕ) :
    towerDelta G ≫ Pi.π _ j = Pi.π _ j - Pi.π _ (j + 1) ≫ G.map (homOfLE (Nat.le_succ j)).op :=
  Pi.lift_comp_π _ _

private lemma lift_towerDelta (c : Cone G) :
    Pi.lift (fun j : ℕ => c.π.app (op j)) ≫ towerDelta G = 0 := by
  refine Pi.hom_ext _ _ fun j => ?_
  rw [Category.assoc, towerDelta_π, Preadditive.comp_sub, Pi.lift_comp_π, Pi.lift_comp_π_assoc, c.w,
    sub_self, zero_comp]

/-- The limit of a tower is the kernel of `towerDelta`. -/
private noncomputable def isLimitKernelFork (c : Cone G) (hc : IsLimit c) :
    IsLimit (KernelFork.ofι _ (lift_towerDelta G c)) :=
  KernelFork.IsLimit.ofι _ _
    (fun k hk => hc.lift ⟨_, NatTrans.ofOpSequence (F := (Functor.const _).obj _)
      (fun j => k ≫ Pi.π _ j) (fun j => by
        have := hk =≫ Pi.π _ j
        rw [Category.assoc, towerDelta_π, Preadditive.comp_sub, zero_comp, sub_eq_zero] at this
        simpa using this)⟩)
    (fun k hk => Pi.hom_ext _ _ fun j => by
      rw [Category.assoc, Pi.lift_comp_π, hc.fac]
      rfl)
    (fun k hk m hm => hc.hom_ext fun j => by
      obtain ⟨j⟩ := j
      rw [hc.fac]
      change _ = k ≫ Pi.π _ j
      rw [← hm, Category.assoc, Pi.lift_comp_π])

/-- An additive functor carries `towerDelta` of a tower to `towerDelta` of its image, under the
comparison map of products. -/
private lemma map_towerDelta_comp_piComparison {E : Type*} [Category* E] [Preadditive E]
    (F : D ⥤ E) [F.Additive] [HasLimitsOfShape (Discrete ℕ) E] :
    F.map (towerDelta G) ≫ piComparison F _ = piComparison F _ ≫ towerDelta (G ⋙ F) :=
  Pi.hom_ext _ _ fun j => by
    rw [Category.assoc, Category.assoc, piComparison_comp_π, ← F.map_comp, towerDelta_π,
      F.map_sub, F.map_comp]
    erw [towerDelta_π (G ⋙ F), Preadditive.comp_sub, piComparison_comp_π,
      piComparison_comp_π_assoc]
    rfl

end Tower

private lemma surjective_of_isLimit_fan {G : ℕᵒᵖ ⥤ AddCommGrpCat.{0}}
    (hG : ∀ j, Function.Surjective (G.map (homOfLE (Nat.le_succ j)).op))
    {F : Fan fun j : ℕ => G.obj (op j)} (hF : IsLimit F) (Δ : F.pt ⟶ F.pt)
    (hΔ : ∀ j, Δ ≫ F.proj j = F.proj j - F.proj (j + 1) ≫ G.map (homOfLE (Nat.le_succ j)).op) :
    Function.Surjective Δ := by
  intro y
  let x : ∀ j : ℕ, G.obj (op j) := fun j =>
    Nat.rec (motive := fun j => G.obj (op j)) 0 (fun j xj => (hG j (xj - F.proj j y)).choose) j
  have hx : ∀ j, G.map (homOfLE (Nat.le_succ j)).op (x (j + 1)) = x j - F.proj j y :=
    fun j => (hG j _).choose_spec
  obtain ⟨a, ha⟩ := fan_exists hF x
  refine ⟨a, fan_ext hF fun j => ?_⟩
  have := congrArg (fun f => f a) (hΔ j)
  simp only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_sub, AddMonoidHom.sub_apply] at this
  rw [this, ha, ha, hx, sub_sub_cancel]

section Homology

variable (K : CochainComplex AddCommGrpCat.{0} ℤ)

/-- A cocycle of a complex of abelian groups is an element of the cycles. -/
private lemma exists_iCycles_eq (p : ℤ) (z : K.X p) (hz : K.d p (p + 1) z = 0) :
    ∃ x : K.cycles p, K.iCycles p x = z :=
  (ShortComplex.ab_exact_iff (ShortComplex.mk _ _ (K.iCycles_d p (p + 1)))).1
    (ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel p (p + 1) (by simp))) z hz

/-- A cycle of a complex of abelian groups with zero class is a boundary. -/
private lemma exists_toCycles_eq (n p : ℤ) (hnp : n + 1 = p) (x : K.cycles p)
    (hx : K.homologyπ p x = 0) : ∃ w : K.X n, K.toCycles n p w = x :=
  (ShortComplex.ab_exact_iff (ShortComplex.mk _ _ (K.toCycles_comp_homologyπ n p))).1
    (ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel n p (by simp [← hnp]))) x hx

end Homology

/-- For a short exact sequence `S` of cochain complexes, the long exact cohomology sequence
breaks into the short exact sequence
`0 ⟶ coker H^n(S.g) ⟶ H^m(S.X₁) ⟶ ker H^m(S.g) ⟶ 0`. -/
private lemma shortExact_cokernel_desc_δ_kernel_lift {A : Type*} [Category* A] [Abelian A]
    {S : ShortComplex (CochainComplex A ℤ)} (hS : S.ShortExact) (n m : ℤ) (hnm : n + 1 = m) :
    (ShortComplex.mk (cokernel.desc _ _ (hS.comp_δ n m hnm))
      (kernel.lift (homologyMap S.g m) (homologyMap S.f m)
        (by rw [← homologyMap_comp, S.zero, homologyMap_zero]))
      (by apply coequalizer.hom_ext; apply equalizer.hom_ext; simp [hS.δ_comp n m hnm])).ShortExact
    where
  exact := by
    let S₁ := ShortComplex.mk _ _ (hS.δ_comp n m hnm)
    let S₂ := ShortComplex.mk (cokernel.desc _ _ (hS.comp_δ n m hnm)) (homologyMap S.f m)
      (by apply coequalizer.hom_ext; simp [hS.δ_comp n m hnm])
    have h₂ : S₂.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := S₁) (S₂ := S₂) { τ₁ := cokernel.π _, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }).1
      (hS.homology_exact₁ n m hnm)
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk _ (kernel.lift (homologyMap S.g m) _ _) _) (S₂ := S₂)
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι _ }).2 h₂
  mono_f := (ShortComplex.exact_iff_mono_cokernel_desc _).1 (hS.homology_exact₃ n m hnm)
  epi_g := (ShortComplex.exact_iff_epi_kernel_lift _).1 (hS.homology_exact₂ m)

section Products

variable (K : ℕ → CochainComplex AddCommGrpCat.{0} ℤ) (p : ℤ)

private lemma pi_π_lift_homologyMap_apply (j : ℕ) (x : (∏ᶜ K).homology p) :
    Pi.π (fun j => (K j).homology p) j
      ((Pi.lift fun j => HomologicalComplex.homologyMap (Pi.π K j) p) x) =
      HomologicalComplex.homologyMap (Pi.π K j) p x := by
  simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom (Pi.lift_comp_π _ j) x

private lemma homologyMap_pi_π_homologyπ_apply (j : ℕ) (x : (∏ᶜ K).cycles p) :
    HomologicalComplex.homologyMap (Pi.π K j) p ((∏ᶜ K).homologyπ p x) =
      (K j).homologyπ p (HomologicalComplex.cyclesMap (Pi.π K j) p x) := by
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (Pi.π K j) p) x

private lemma iCycles_cyclesMap_pi_π_apply (j : ℕ) (x : (∏ᶜ K).cycles p) :
    (K j).iCycles p (HomologicalComplex.cyclesMap (Pi.π K j) p x) =
      (Pi.π K j).f p ((∏ᶜ K).iCycles p x) := by
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (Pi.π K j) p) x

private lemma pi_π_f_d_apply (j : ℕ) (q q' : ℤ) (x : (∏ᶜ K).X q) :
    (Pi.π K j).f q' ((∏ᶜ K).d q q' x) = (K j).d q q' ((Pi.π K j).f q x) := by
  simpa only [ConcreteCategory.comp_apply] using
    (ConcreteCategory.congr_hom ((Pi.π K j).comm q q') x).symm

/-- The comparison map `H^p(∏ K_j) ⟶ ∏ H^p(K_j)` for complexes of abelian groups is
injective. -/
private lemma injective_lift_homologyMap_π :
    Function.Injective (Pi.lift fun j => HomologicalComplex.homologyMap (Pi.π K j) p) := by
  have hF : ∀ q, IsLimit (Fan.mk ((∏ᶜ K).X q) fun j => (Pi.π K j).f q) := fun q =>
    isLimitFanMkObjOfIsLimit (HomologicalComplex.eval _ _ q) K _ (productIsProduct K)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective ((∏ᶜ K).homologyπ p)).1 inferInstance x
  have h0 : ∀ j, (K j).homologyπ p (HomologicalComplex.cyclesMap (Pi.π K j) p c) = 0 :=
    fun j => by
      rw [← homologyMap_pi_π_homologyπ_apply, ← pi_π_lift_homologyMap_apply, hx, map_zero]
  choose w hw using fun j => exists_toCycles_eq (K j) (p - 1) p (sub_add_cancel p 1) _ (h0 j)
  obtain ⟨W, hW⟩ := fan_exists (hF (p - 1)) w
  have : (∏ᶜ K).toCycles (p - 1) p W = c := by
    apply (AddCommGrpCat.mono_iff_injective ((∏ᶜ K).iCycles p)).1 inferInstance
    have e := fun L : CochainComplex AddCommGrpCat.{0} ℤ => fun y =>
      ConcreteCategory.congr_hom (L.toCycles_i (p - 1) p) y
    simp only [ConcreteCategory.comp_apply] at e
    refine fan_ext (hF p) fun j => ?_
    change (Pi.π K j).f p _ = (Pi.π K j).f p _
    rw [e, pi_π_f_d_apply, ← iCycles_cyclesMap_pi_π_apply, ← hw j, e]
    exact congrArg _ (hW j)
  rw [← this]
  have := ConcreteCategory.congr_hom ((∏ᶜ K).toCycles_comp_homologyπ (p - 1) p) W
  simp only [ConcreteCategory.comp_apply] at this
  rw [this]
  rfl

/-- The comparison map `H^p(∏ K_j) ⟶ ∏ H^p(K_j)` for complexes of abelian groups is
surjective. -/
private lemma surjective_lift_homologyMap_π :
    Function.Surjective (Pi.lift fun j => HomologicalComplex.homologyMap (Pi.π K j) p) := by
  have hF : ∀ q, IsLimit (Fan.mk ((∏ᶜ K).X q) fun j => (Pi.π K j).f q) := fun q =>
    isLimitFanMkObjOfIsLimit (HomologicalComplex.eval _ _ q) K _ (productIsProduct K)
  intro h
  choose c hc using fun j => (AddCommGrpCat.epi_iff_surjective ((K j).homologyπ p)).1
    inferInstance (Pi.π (fun j => (K j).homology p) j h)
  obtain ⟨Z, hZ⟩ := fan_exists (hF p) fun j => (K j).iCycles p (c j)
  have hdZ : (∏ᶜ K).d p (p + 1) Z = 0 := by
    refine fan_ext (hF (p + 1)) fun j => ?_
    change (Pi.π K j).f (p + 1) _ = (Pi.π K j).f (p + 1) _
    rw [pi_π_f_d_apply, map_zero]
    change (K j).d p (p + 1) ((Fan.mk _ fun j => (Pi.π K j).f p).proj j Z) = 0
    rw [hZ]
    have := ConcreteCategory.congr_hom ((K j).iCycles_d p (p + 1)) (c j)
    simp only [ConcreteCategory.comp_apply] at this
    rw [this]
    rfl
  obtain ⟨x, hx⟩ := exists_iCycles_eq _ p Z hdZ
  refine ⟨(∏ᶜ K).homologyπ p x, fan_ext (productIsProduct fun j => (K j).homology p) fun j => ?_⟩
  change Pi.π (fun j => (K j).homology p) j _ = Pi.π (fun j => (K j).homology p) j _
  rw [pi_π_lift_homologyMap_apply, homologyMap_pi_π_homologyπ_apply, ← hc j]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective ((K j).iCycles p)).1 inferInstance
  rw [iCycles_cyclesMap_pi_π_apply, hx]
  exact hZ j

/-- Cohomology of complexes of abelian groups commutes with products. -/
private lemma isIso_lift_homologyMap_π :
    IsIso (Pi.lift fun j => HomologicalComplex.homologyMap (Pi.π K j) p) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨injective_lift_homologyMap_π K p, surjective_lift_homologyMap_π K p⟩

end Products

/-- For a tower of cochain complexes of abelian groups with surjective transition maps and a
limit cone `c`, the sequence `0 ⟶ c.pt ⟶ ∏ C_j ⟶ ∏ C_j ⟶ 0` is short exact. -/
private lemma shortExact_lift_π_towerDelta (C : ℕᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℤ)
    (hC : ∀ (j : ℕ) (p : ℤ),
      Function.Surjective ((C.map (homOfLE (Nat.le_succ j)).op).f p))
    (c : Cone C) (hc : IsLimit c) :
    (ShortComplex.mk _ (towerDelta C) (lift_towerDelta C c)).ShortExact := by
  have hK := isLimitKernelFork C c hc
  have : Mono (Pi.lift fun j : ℕ => c.π.app (op j)) := Fork.IsLimit.mono hK
  refine { exact := ShortComplex.exact_of_f_is_kernel _ hK, mono_f := this, epi_g := ?_ }
  refine epi_of_epi_f _ fun q => (AddCommGrpCat.epi_iff_surjective _).2 ?_
  refine surjective_of_isLimit_fan (G := C ⋙ eval _ _ q) (fun j => hC j q)
    (isLimitFanMkObjOfIsLimit (eval _ _ q) _ _ (productIsProduct _)) _ fun j => ?_
  simp [← comp_f, towerDelta_π]

/-- If all transition maps of a tower of abelian groups vanish, its limit and its `lim¹`, the
cokernel of `towerDelta`, vanish. -/
private lemma isZero_limit_and_cokernel_towerDelta {G : ℕᵒᵖ ⥤ AddCommGrpCat.{0}}
    (h0 : ∀ j : ℕ, G.map (homOfLE (Nat.le_succ j)).op = 0) :
    IsZero (limit G) ∧ IsZero (cokernel (towerDelta G)) := by
  refine ⟨?_, ?_⟩
  · rw [IsZero.iff_id_eq_zero]
    refine limit.hom_ext fun j => ?_
    obtain ⟨j⟩ := j
    rw [Category.id_comp, zero_comp, ← limit.w G (homOfLE (Nat.le_succ j)).op, h0, comp_zero]
  · have hT : towerDelta G = 𝟙 _ := Pi.hom_ext _ _ fun j => by
      rw [towerDelta_π, h0, comp_zero, sub_zero, Category.id_comp]
    rw [hT]
    exact isZero_cokernel_of_epi _

/-- Read in products, the comparison `F c.pt ⟶ lim (C ⋙ F)` is `F` applied to the projections
of `c`. -/
private lemma limit_lift_mapCone_comp_lift_π {D E : Type*} [Category* D] [Category* E]
    (C : ℕᵒᵖ ⥤ D) (F : D ⥤ E) [HasLimit (C ⋙ F)] [HasProduct fun j : ℕ => C.obj (op j)]
    [HasProduct fun j : ℕ => (C ⋙ F).obj (op j)] (c : Cone C) :
    limit.lift (C ⋙ F) (F.mapCone c) ≫ Pi.lift (fun j : ℕ => limit.π (C ⋙ F) (op j)) =
      F.map (Pi.lift fun j : ℕ => c.π.app (op j)) ≫
        Pi.lift (f := fun j : ℕ => (C ⋙ F).obj (op j)) fun j =>
          F.map (Pi.π (fun j : ℕ => C.obj (op j)) j) :=
  Pi.hom_ext _ _ fun j => by simp [← F.map_comp]

/-- **Milnor sequence.** For a tower `C` of cochain complexes of abelian groups with
degreewise surjective transition maps and a limit cone `c`, and `n + 1 = m`, there is a short
exact sequence `0 ⟶ lim¹_j H^n(C_j) ⟶ H^m(c.pt) ⟶ lim_j H^m(C_j) ⟶ 0` whose second map is
induced by the projections of `c`; here `lim¹ G` is the cokernel of
`(x_j) ↦ (x_j - t(x_{j+1}))` on `∏ G_j`. Moreover, if all transition maps
`H^m(C_{j+1}) ⟶ H^m(C_j)` are zero, then `lim_j H^m(C_j)` and `lim¹_j H^m(C_j)` vanish. -/
@[mmp "lem_mmp_gaga_milnor_sequence"]
public theorem milnor_sequence (C : ℕᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℤ)
    (hC : ∀ (j : ℕ) (p : ℤ),
      Function.Surjective ((C.map (homOfLE (Nat.le_succ j)).op).f p))
    (c : Cone C) (hc : IsLimit c) (n m : ℤ) (hnm : n + 1 = m) :
    let Δ : (G : ℕᵒᵖ ⥤ AddCommGrpCat.{0}) →
        ((∏ᶜ fun j : ℕ => G.obj (op j)) ⟶ ∏ᶜ fun j : ℕ => G.obj (op j)) := fun G =>
      Pi.lift fun j => Pi.π _ j - Pi.π _ (j + 1) ≫ G.map (homOfLE (Nat.le_succ j)).op
    let H : ℤ → (ℕᵒᵖ ⥤ AddCommGrpCat.{0}) := fun p =>
      C ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) p
    let g : c.pt.homology m ⟶ limit (H m) :=
      limit.lift (H m)
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) m).mapCone c)
    (∃ (f : cokernel (Δ (H n)) ⟶ c.pt.homology m) (w : f ≫ g = 0),
        (ShortComplex.mk f g w).ShortExact) ∧
      ((∀ j : ℕ, (H m).map (homOfLE (Nat.le_succ j)).op = 0) →
        IsZero (limit (H m)) ∧ IsZero (cokernel (Δ (H m)))) := by
  intro Δ H g
  change (∃ (f : cokernel (towerDelta (H n)) ⟶ c.pt.homology m) (w : f ≫ g = 0),
        (ShortComplex.mk f g w).ShortExact) ∧
      ((∀ j : ℕ, (H m).map (homOfLE (Nat.le_succ j)).op = 0) →
        IsZero (limit (H m)) ∧ IsZero (cokernel (towerDelta (H m))))
  refine ⟨?_, isZero_limit_and_cokernel_towerDelta⟩
  -- the short exact sequence `0 ⟶ c.pt ⟶ ∏ C_j ⟶ ∏ C_j ⟶ 0`
  let ι : c.pt ⟶ ∏ᶜ fun j : ℕ => C.obj (op j) := Pi.lift fun j => c.π.app (op j)
  let S := ShortComplex.mk ι (towerDelta C) (lift_towerDelta C c)
  have hS : S.ShortExact := shortExact_lift_π_towerDelta C hC c hc
  -- cohomology commutes with the products
  let φ : ∀ p, (∏ᶜ fun j : ℕ => C.obj (op j)).homology p ⟶ ∏ᶜ fun j : ℕ => (H p).obj (op j) :=
    fun p => Pi.lift (f := fun j : ℕ => (H p).obj (op j)) fun j =>
      homologyMap (Pi.π (fun j : ℕ => C.obj (op j)) j) p
  have hφiso : ∀ p, IsIso (φ p) := fun p =>
    isIso_lift_homologyMap_π (fun j : ℕ => C.obj (op j)) p
  have hφ : ∀ p, homologyMap (towerDelta C) p ≫ φ p = φ p ≫ towerDelta (H p) := fun p =>
    map_towerDelta_comp_piComparison C (homologyFunctor _ _ p)
  have key := shortExact_cokernel_desc_δ_kernel_lift hS n m hnm
  -- the limit of `H m` is the kernel of `towerDelta (H m)`
  let ιL : limit (H m) ⟶ ∏ᶜ fun j : ℕ => (H m).obj (op j) :=
    Pi.lift (f := fun j : ℕ => (H m).obj (op j)) fun j => limit.π (H m) (op j)
  have hL := isLimitKernelFork (H m) (limit.cone _) (limit.isLimit _)
  have : Mono ιL := Fork.IsLimit.mono hL
  have hgι : g ≫ ιL = homologyMap ι m ≫ φ m :=
    limit_lift_mapCone_comp_lift_π C (homologyFunctor _ _ m) c
  -- transport along `φ`
  let e₁ : cokernel (towerDelta (H n)) ≅ cokernel (homologyMap S.g n) :=
    cokernel.mapIso _ _ (asIso (φ n)).symm (asIso (φ n)).symm
      (by simp [IsIso.eq_inv_comp, ← reassoc_of% (hφ n), S])
  let e₂ : kernel (homologyMap S.g m) ≅ limit (H m) :=
    kernel.mapIso _ _ (asIso (φ m)) (asIso (φ m)) (hφ m) ≪≫
      (hL.conePointUniqueUpToIso (kernelIsKernel _)).symm
  let g₀ := kernel.lift (homologyMap S.g m) (homologyMap S.f m)
    (by rw [← homologyMap_comp, S.zero, homologyMap_zero])
  have hg : g = g₀ ≫ e₂.hom := by
    rw [← cancel_mono ιL, hgι, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc]
    erw [IsLimit.conePointUniqueUpToIso_inv_comp hL (kernelIsKernel _) WalkingParallelPair.zero]
    simp [g₀, kernel.mapIso, S]
  have z₀ : cokernel.desc _ _ (hS.comp_δ n m hnm) ≫ g₀ = 0 := by
    apply coequalizer.hom_ext; apply equalizer.hom_ext; simp [g₀, hS.δ_comp n m hnm]
  refine ⟨e₁.hom ≫ cokernel.desc _ _ (hS.comp_δ n m hnm), by simp [hg, reassoc_of% z₀], ?_⟩
  refine ShortComplex.shortExact_of_iso ?_ key
  exact ShortComplex.isoMk e₁.symm (Iso.refl _) e₂ (by simp) (by simp [hg, g₀])

end MMP.Analytic
