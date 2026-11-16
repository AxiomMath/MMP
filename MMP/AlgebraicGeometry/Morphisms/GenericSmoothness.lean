module

public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical

/-!
# Generic smoothness and the tangent criterion for smoothness

This file proves two foundational facts about smooth morphisms of varieties.

*Generic smoothness.* Let `K` be a field of characteristic zero and `p : V ⟶ T` a morphism of
integral `K`-schemes of finite type, with `V` smooth over `K`. Then there is a dense open
`T° ⊆ T`, contained in the smooth locus of `T` over `K`, such that the restriction
`p⁻¹(T°) ⟶ T°` is smooth. The preimage may be empty when `p` is not dominant. If `p` is dominant,
every fibre `p⁻¹(t)` with `t ∈ T°` is smooth over the residue field `κ(t)`, and each of its
irreducible components has dimension `dim V - dim T`.

The proof has three steps. Every local ring of `V` is regular, so at a point over the generic
point of `T`, where the local ring of `T` is the function field, of characteristic zero, `p` is
smooth; the closure of the image of the non-smooth locus of `p` then misses the generic point of
`T`. The fibres over `T°` are smooth by base change of `p ∣_ T°` along `Spec κ(t) ⟶ T°`, and their
components have the expected dimension by flatness of `p ∣_ T°`.

*The tangent criterion.* Let `p : V ⟶ T` be a morphism of non-singular varieties over an
algebraically closed field `k`, and let `v` be a closed point of `V`. Then `p` is smooth at `v`
if and only if the differential `dp_v : T_v V → T_{p v} T` is surjective. Dually, `dp_v` is
surjective exactly when the induced map on Zariski cotangent spaces
`𝔪_{p v}/𝔪_{p v}² → 𝔪_v/𝔪_v²`, coming from the stalk map `p.stalkMap v`, is injective; this is
the form stated here.

The proof is local. Write `A → B` for the stalk map and `K = κ(v) = k`. Since `k → K` is an
isomorphism, the conormal maps `𝔪_A/𝔪_A² → K ⊗_A Ω_{A/k}` and `𝔪_B/𝔪_B² → K ⊗_B Ω_{B/k}` are
isomorphisms, so injectivity of the cotangent map is injectivity of
`K ⊗_B (B ⊗_A Ω_{A/k}) → K ⊗_B Ω_{B/k}`. By the Jacobi–Zariski sequence
`H₁(L_{B/k}) → H₁(L_{B/A}) → B ⊗_A Ω_{A/k} → Ω_{B/k} → Ω_{B/A} → 0`, and since `Ω_{B/k}` is
finite free over the local ring `B`, the latter injectivity is equivalent to
`B ⊗_A Ω_{A/k} → Ω_{B/k}` being split injective. That holds exactly when `H₁(L_{B/A}) = 0` and
`Ω_{B/A}` is projective, i.e. when `B` is formally smooth over `A`.

## Main results

* `MMP.exists_dense_smooth_restrict_of_smooth`: generic smoothness.
* `MMP.mem_smoothLocus_iff_injective_mapCotangent`: `v ∈ Mori.smoothLocus p` if and only if
  the cotangent map of `p` at `v` is injective.

## Implementation notes

For generic smoothness, a variety is an integral scheme of finite type over `K`
(`AlgebraicGeometry.IsIntegral`, `LocallyOfFiniteType` and `QuasiCompact` structure morphism);
separatedness is not needed. The source works over `ℂ`; the statement is made over any field of
characteristic zero. Over such a field, non-singular means smooth over `K`, so the non-singular
locus of `T` is `Scheme.Hom.smoothLocus` of its structure morphism, and a non-singular fibre is
one smooth over `κ(t)`. The purity of the fibre dimension is stated additively,
`dim Z + dim T = dim V` for every irreducible component `Z` of `p⁻¹(t)`, which avoids truncated
subtraction.

For the tangent criterion, the tangent space `T_v V` is the `k`-linear dual of the cotangent
space `𝔪_v/𝔪_v²`, and `dp_v` is the transpose of the cotangent map induced by the local
homomorphism of stalks. At a closed point of a variety over an algebraically closed field both
residue fields are `k`, and the cotangent spaces are finite dimensional, so surjectivity of
`dp_v` is injectivity of the cotangent map. The cotangent map is `Ideal.mapCotangent` of the
stalk map, viewed as a `ℤ`-linear map; injectivity does not depend on the scalars. The source
deduces the converse from étale coordinate charts on `V` and on `T` compatible with `p`; here it
is proved in the local rings, from the Jacobi–Zariski sequence of `k → 𝒪_{T,p v} → 𝒪_{V,v}` and
Nakayama's lemma for maps between finite free modules. Smoothness at `v` is formal smoothness of
the stalk map, because `p` is locally of finite presentation.

## References

* [R. Lazarsfeld, *Positivity in algebraic geometry I*][lazarsfeld2004]
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Topology IsLocalRing TensorProduct

universe u

namespace MMP

/-! ### Generic smoothness -/

/-- A morphism over `S` from a scheme locally of finite type over `S` is locally of finite
type. -/
private theorem locallyOfFiniteType_of_isOver (S : Scheme.{u}) {X Y : Scheme.{u}} [X.Over S]
    [Y.Over S] [LocallyOfFiniteType (X ↘ S)] (p : X ⟶ Y) [p.IsOver S] : LocallyOfFiniteType p :=
  have : LocallyOfFiniteType (p ≫ (Y ↘ S)) := by rw [comp_over]; infer_instance
  locallyOfFiniteType_of_comp p (Y ↘ S)

/-- A scheme quasi-compact and locally of finite type over a field is Noetherian. -/
private theorem isNoetherian_of_quasiCompact {K : Type u} [Field K] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of K)) [LocallyOfFiniteType q] [QuasiCompact q] : IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian q
  have := (quasiCompact_iff_compactSpace q).mp ‹_›
  ⟨⟩

/-- A regular local algebra essentially of finite type over a field of characteristic zero is
formally smooth over that field. -/
private theorem formallySmooth_of_isRegularLocalRing {F A : Type*} [CommRing F] (hF : IsField F)
    [CharZero F] [CommRing A] [IsLocalRing A] [Algebra F A] [Algebra.EssFiniteType F A]
    [IsRegularLocalRing A] : Algebra.FormallySmooth F A := by
  letI := hF.toField
  obtain ⟨s, hs⟩ := Algebra.EssFiniteType.cond (R := F) (S := A)
  let q : Ideal (Algebra.adjoin F (s : Set A)) :=
    (IsLocalRing.maximalIdeal A).comap (algebraMap (Algebra.adjoin F (s : Set A)) A)
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have hM : (IsUnit.submonoid A).comap (algebraMap (Algebra.adjoin F (s : Set A)) A) =
      q.primeCompl := by
    ext x
    simp [q, IsUnit.mem_submonoid_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have : IsLocalization.AtPrime A q := by rwa [IsLocalization.AtPrime, ← hM]
  have : Algebra.FiniteType F (Algebra.adjoin F (s : Set A)) :=
    ⟨(Subalgebra.fg_top _).mpr (Subalgebra.fg_adjoin_finset s)⟩
  have := Algebra.isSeparableExtension_of_perfectField F q.ResidueField
  have : Algebra.IsSmoothAt F q := (Algebra.isSmoothAt_iff_isRegularLocalRing q A).mpr ‹_›
  exact Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) A).restrictScalars F)

/-- A morphism locally of finite type is smooth at a point with regular local ring lying over a
point whose local ring is a field of characteristic zero. -/
private theorem mem_smoothLocus_of_isField_stalk {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (x : X)
    (hF : IsField (Y.presheaf.stalk (f x))) (hc : CharZero (Y.presheaf.stalk (f x)))
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) : x ∈ f.smoothLocus := by
  rw [Scheme.Hom.mem_smoothLocus]
  have hess := LocallyOfFiniteType.stalkMap f x
  exact @formallySmooth_of_isRegularLocalRing _ _ _ hF hc _ _ (f.stalkMap x).hom.toAlgebra hess
    hreg

/-- In a Noetherian quasi-sober space, if no point of a closed set `Z` maps to a point `η` that
specializes to every point, then `η` is not in the closure of the image of `Z`. -/
private theorem notMem_closure_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NoetherianSpace X] [QuasiSober X] [T0Space Y] {f : X → Y} (hf : Continuous f) {Z : Set X}
    (hZ : IsClosed Z) {η : Y} (hη : ∀ y, η ⤳ y) (hZη : ∀ x ∈ Z, f x ≠ η) :
    η ∉ closure (f '' Z) := by
  obtain ⟨S, hS, hSZ⟩ := NoetherianSpace.exists_finset_irreducible (⟨Z, hZ⟩ : Closeds X)
  have hZeq : Z = ⋃ C ∈ S, (C : Set X) := by
    simpa [Closeds.coe_finset_sup] using congrArg (fun C : Closeds X => (C : Set X)) hSZ
  intro hmem
  have hcl : closure (f '' Z) ⊆ ⋃ C ∈ S, closure (f '' (C : Set X)) := by
    rw [hZeq, Set.image_iUnion₂]
    exact closure_minimal (Set.iUnion₂_mono fun _ _ => subset_closure)
      (S.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure)
  obtain ⟨C, hCS, hηC⟩ := Set.mem_iUnion₂.mp (hcl hmem)
  obtain ⟨g, hg⟩ : ∃ g, IsGenericPoint g (C : Set X) :=
    ⟨_, (hS ⟨C, hCS⟩).isGenericPoint_genericPoint C.isClosed⟩
  have h1 : f '' (C : Set X) ⊆ closure {f g} := by
    rw [← isGenericPoint_def.mp hg, ← Set.image_singleton]
    exact image_closure_subset_closure_image hf
  have hsp : f g ⤳ η :=
    specializes_iff_mem_closure.mpr (closure_minimal h1 isClosed_closure hηC)
  exact hZη _ (hZeq ▸ Set.mem_iUnion₂.mpr ⟨C, hCS, hg.mem⟩) (hsp.antisymm (hη _)).eq

/-- Generic smoothness: `p` is smooth over a dense open of the smooth locus of `T`. -/
private theorem exists_dense_smooth_restrict {K : Type u} [Field K] [CharZero K]
    {V T : Scheme.{u}} [V.Over (Spec (.of K))] [T.Over (Spec (.of K))]
    [IsIntegral V] [IsIntegral T]
    [LocallyOfFiniteType (V ↘ Spec (.of K))] [QuasiCompact (V ↘ Spec (.of K))]
    [LocallyOfFiniteType (T ↘ Spec (.of K))] [QuasiCompact (T ↘ Spec (.of K))]
    [Smooth (V ↘ Spec (.of K))]
    (p : V ⟶ T) [p.IsOver (Spec (.of K))] :
    ∃ U : T.Opens, Dense (U : Set T) ∧ U ≤ (T ↘ Spec (.of K)).smoothLocus ∧
      Smooth (p ∣_ U) := by
  have := locallyOfFiniteType_of_isOver (Spec (.of K)) p
  have := isNoetherian_of_quasiCompact (V ↘ Spec (.of K))
  have := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of K))
  -- every point of `V` over the generic point of `T` is a smooth point of `p`
  have hreg := (Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk
    (V ↘ Spec (.of K))).mp inferInstance
  have hgen : ∀ x : V, p x = genericPoint T → x ∈ p.smoothLocus := by
    intro x hx
    refine mem_smoothLocus_of_isField_stalk p x ?_ ?_ (hreg x)
    · rw [hx]
      exact Field.toIsField T.functionField
    · let φ : K →+* T.presheaf.stalk (p x) := ((Scheme.ΓSpecIso (.of K)).inv ≫
        (T ↘ Spec (.of K)).appTop ≫ T.presheaf.germ ⊤ (p x) trivial).hom
      exact charZero_of_injective_ringHom φ.injective
  set Z : Set V := ((p.smoothLocus : Set V))ᶜ
  have hZ : IsClosed Z := p.smoothLocus.isOpen.isClosed_compl
  have hη : genericPoint T ∉ closure (p '' Z) :=
    notMem_closure_image p.continuous hZ genericPoint_specializes
      (fun x hx hpx => hx (hgen x hpx))
  let U₀ : T.Opens := ⟨(closure (p '' Z))ᶜ, isClosed_closure.isOpen_compl⟩
  refine ⟨U₀ ⊓ (T ↘ Spec (.of K)).smoothLocus, ?_, inf_le_right, ?_⟩
  · exact (U₀ ⊓ (T ↘ Spec (.of K)).smoothLocus).isOpen.dense
      ⟨genericPoint T, hη, (T ↘ Spec (.of K)).genericPoint_mem_smoothLocus_of_perfectField⟩
  · refine Scheme.Hom.smoothLocus_eq_top_iff.mp (top_unique fun x _ => ?_)
    rw [Scheme.Hom.mem_smoothLocus]
    refine (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap p _ x)).mpr ?_
    rw [← Scheme.Hom.mem_smoothLocus]
    by_contra hx
    exact x.2.1 (subset_closure ⟨x.1, hx, rfl⟩)

/-- The fibre of `p` over a point of an open over which `p` is smooth is smooth over the
residue field. -/
theorem smooth_fiberToSpecResidueField_of_smooth_restrict {V T : Scheme.{u}}
    (p : V ⟶ T) (U : T.Opens) [Smooth (p ∣_ U)] (t : T) (ht : t ∈ U) :
    Smooth (p.fiberToSpecResidueField t) := by
  have hr : Set.range (T.fromSpecResidueField t) ⊆ Set.range U.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    simpa using ht
  let g' := IsOpenImmersion.lift U.ι (T.fromSpecResidueField t) hr
  have hg : g' ≫ U.ι = T.fromSpecResidueField t := IsOpenImmersion.lift_fac _ _ _
  have hR := (isPullback_morphismRestrict p U).flip
  have hF : IsPullback (p.fiberι t) (p.fiberToSpecResidueField t) p (T.fromSpecResidueField t) :=
    IsPullback.of_hasPullback _ _
  let a := hR.lift (p.fiberι t) (p.fiberToSpecResidueField t ≫ g')
    (by simpa only [Category.assoc, hg] using hF.w)
  have h1 : a ≫ (p ⁻¹ᵁ U).ι = p.fiberι t := hR.lift_fst _ _ _
  have h2 : a ≫ p ∣_ U = p.fiberToSpecResidueField t ≫ g' := hR.lift_snd _ _ _
  have hsq : IsPullback a (p.fiberToSpecResidueField t) (p ∣_ U) g' := by
    refine IsPullback.of_right (h₁₂ := (p ⁻¹ᵁ U).ι) (h₂₂ := U.ι) ?_ h2 hR
    rwa [h1, hg]
  exact MorphismProperty.of_isPullback (P := @Smooth) hsq inferInstance

/-- On a Noetherian scheme locally of finite type over a field, a property of the local dimension
holding on a dense open subset holds for the dimension of every irreducible component. -/
private theorem forall_irreducibleComponents_of_dense (k : Type u) [Field k] (X : Scheme.{u})
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
  exact hlocal ▸ hP _ hηO

/-- The local dimension of an irreducible scheme locally of finite type over a field is its
dimension at every point. -/
private theorem topologicalKrullDimAt_eq_topologicalKrullDim (k : Type u) [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] [IrreducibleSpace X]
    (x : X) : topologicalKrullDimAt X x = topologicalKrullDim X := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X q x,
    irreducibleComponents_eq_singleton]
  have : {Z : Set X | Z ∈ ({Set.univ} : Set (Set X)) ∧ x ∈ Z} = {Set.univ} := by
    ext Z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨And.left, fun h ↦ ⟨h, h ▸ Set.mem_univ x⟩⟩
  rw [this, iSup_singleton]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph

/-- Irreducible components correspond along a homeomorphism, with the same dimensions. -/
private theorem preimage_mem_irreducibleComponents_of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {C : Set Y}
    (hC : C ∈ irreducibleComponents Y) :
    e ⁻¹' C ∈ irreducibleComponents X ∧ topologicalKrullDim (e ⁻¹' C) = topologicalKrullDim C := by
  refine ⟨preimage_mem_irreducibleComponents hC e.isOpenEmbedding ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hC.1.nonempty
    exact ⟨c, hc, e.surjective c⟩
  · rw [← e.image_symm]
    exact (IsHomeomorph.topologicalKrullDim_eq _ (e.symm.image C).isHomeomorph).symm

/-- On an open piece `Y` of an irreducible `W` mapping flatly with pure relative dimension `d` to
an irreducible `Z`, both locally of finite type over a field, `d + dim Z = dim W`. -/
private theorem natCast_add_topologicalKrullDim_eq_of_relativeDimension (k : Type u) [Field k]
    {Y W Z : Scheme.{u}} (sW : W ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType sW] [LocallyOfFiniteType sZ] [IrreducibleSpace W] [IrreducibleSpace Z]
    (j : Y ⟶ W) [IsOpenImmersion j] (h : Y ⟶ Z) [Flat h] [LocallyOfFiniteType h]
    [IsLocallyNoetherian Y] {d : ℕ} (hd : RelativeDimension h d) (y : Y) :
    (d : WithBot ℕ∞) + topologicalKrullDim Z = topologicalKrullDim W := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  rw [← topologicalKrullDimAt_eq_topologicalKrullDim k W sW (j y),
    j.isOpenEmbedding.topologicalKrullDimAt_eq y,
    topologicalKrullDimAt_eq_add_of_relativeDimension h hd y,
    topologicalKrullDimAt_eq_topologicalKrullDim k Z sZ, add_comm]

/-- For `z ∈ V`, the fibre over `z` of `(f ⁻¹ᵁ V).ι ≫ f` is homeomorphic to the preimage
`f ⁻¹' {z}`. -/
private noncomputable def fiberHomeoRestrict {W Z : Scheme.{u}} (f : W ⟶ Z) (V : Z.Opens)
    {z : Z} (hz : z ∈ V) : ((f ⁻¹ᵁ V).ι ≫ f).fiber z ≃ₜ (f ⁻¹' {z} : Set W) :=
  (Scheme.Hom.fiberHomeo _ z).trans <|
    ((isHomeomorph_iff_isEmbedding_surjective
      (f := fun p : (((f ⁻¹ᵁ V).ι ≫ f) ⁻¹' {z} : Set (f ⁻¹ᵁ V)) ↦
        (⟨p.1.1, p.2⟩ : (f ⁻¹' {z} : Set W)))).mpr
      ⟨(IsEmbedding.of_comp_iff (g := ((↑) : (f ⁻¹' {z} : Set W) → W))
          IsEmbedding.subtypeVal).mp (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal :
            IsEmbedding fun p : (((f ⁻¹ᵁ V).ι ≫ f) ⁻¹' {z} : Set (f ⁻¹ᵁ V)) ↦ p.1.1),
        fun ⟨w, hw⟩ ↦ ⟨⟨⟨w, show f w ∈ V by rwa [show f w = z from hw]⟩, hw⟩,
          rfl⟩⟩).homeomorph

/-- Every irreducible component `Z` of the fibre of `p` over a point of an open `U` over which `p`
is smooth satisfies `dim Z + dim T = dim V`. -/
theorem topologicalKrullDim_add_of_smooth_restrict {K : Type u} [Field K]
    {V T : Scheme.{u}} [V.Over (Spec (.of K))] [T.Over (Spec (.of K))]
    [IsIntegral V] [IsIntegral T]
    [LocallyOfFiniteType (V ↘ Spec (.of K))] [QuasiCompact (V ↘ Spec (.of K))]
    [LocallyOfFiniteType (T ↘ Spec (.of K))]
    (p : V ⟶ T) [p.IsOver (Spec (.of K))]
    (U : T.Opens) [Smooth (p ∣_ U)] (t : T) (ht : t ∈ U) :
    ∀ Z ∈ irreducibleComponents (p.fiber t),
      topologicalKrullDim Z + topologicalKrullDim T = topologicalKrullDim V := by
  intro C hC
  have := locallyOfFiniteType_of_isOver (Spec (.of K)) p
  have := isNoetherian_of_quasiCompact (V ↘ Spec (.of K))
  have := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of K))
  set g : (p ⁻¹ᵁ U).toScheme ⟶ T := (p ⁻¹ᵁ U).ι ≫ p
  have hg : g = (p ∣_ U) ≫ U.ι := (morphismRestrict_ι p U).symm
  have : Flat g := by rw [hg]; infer_instance
  have : LocallyOfFinitePresentation g := by rw [hg]; infer_instance
  obtain ⟨W, hWdense, hrel⟩ := exists_open_relativeDimension_fiberwise_dense g
  let Φ₀ : g.fiber t ≃ₜ (p ⁻¹' {t} : Set V) := fiberHomeoRestrict p U ht
  have : NoetherianSpace (g.fiber t) :=
    noetherianSpace_of_surjective Φ₀.symm Φ₀.symm.continuous Φ₀.symm.surjective
  have := g.locallyOfFiniteType_fiberToSpecResidueField t
  let Φ : g.fiber t ≃ₜ p.fiber t := Φ₀.trans (p.fiberHomeo t).symm
  obtain ⟨hC', hdimC'⟩ := preimage_mem_irreducibleComponents_of_homeomorph Φ hC
  rw [← hdimC']
  refine forall_irreducibleComponents_of_dense (T.residueField t) (g.fiber t)
    (g.fiberToSpecResidueField t) (· + topologicalKrullDim T = topologicalKrullDim V)
    (((iSup W : (p ⁻¹ᵁ U).toScheme.Opens).isOpen).preimage (g.fiberι _).continuous)
    (hWdense _) (fun w hw ↦ ?_) _ hC'
  obtain ⟨d, hd⟩ := Opens.mem_iSup.mp hw
  rw [← Scheme.Hom.topologicalKrullDimAt_fiber_fiberι,
    topologicalKrullDimAt_fiber_eq_of_relativeDimension g (W d) d (hrel d) _ hd]
  exact natCast_add_topologicalKrullDim_eq_of_relativeDimension K (V ↘ Spec (.of K))
    (T ↘ Spec (.of K)) ((W d).ι ≫ (p ⁻¹ᵁ U).ι) ((W d).ι ≫ g) (hrel d) ⟨_, hd⟩

/-- **Generic smoothness.** A morphism `p : V ⟶ T` of integral schemes of finite type over a field
of characteristic zero, with `V` smooth, is smooth over a dense open `T°` of the smooth locus of
`T`; if `p` is dominant, its fibres over `T°` are smooth over the residue fields and every
irreducible component `Z` of such a fibre satisfies `dim Z + dim T = dim V`. -/
@[mmp "lem_mmp_foundation_laz_generic_smoothness"]
public theorem exists_dense_smooth_restrict_of_smooth {K : Type u} [Field K] [CharZero K]
    {V T : Scheme.{u}} [V.Over (Spec (.of K))] [T.Over (Spec (.of K))]
    [IsIntegral V] [IsIntegral T]
    [LocallyOfFiniteType (V ↘ Spec (.of K))] [QuasiCompact (V ↘ Spec (.of K))]
    [LocallyOfFiniteType (T ↘ Spec (.of K))] [QuasiCompact (T ↘ Spec (.of K))]
    [Smooth (V ↘ Spec (.of K))]
    (p : V ⟶ T) [p.IsOver (Spec (.of K))] :
    ∃ U : T.Opens, Dense (U : Set T) ∧ U ≤ (T ↘ Spec (.of K)).smoothLocus ∧
      Smooth (p ∣_ U) ∧
      (IsDominant p → ∀ t ∈ U, Smooth (p.fiberToSpecResidueField t) ∧
        ∀ Z ∈ irreducibleComponents (p.fiber t),
          topologicalKrullDim Z + topologicalKrullDim T = topologicalKrullDim V) := by
  obtain ⟨U, hU, hUs, hp⟩ := exists_dense_smooth_restrict (K := K) p
  exact ⟨U, hU, hUs, hp, fun _ t ht => ⟨smooth_fiberToSpecResidueField_of_smooth_restrict p U t ht,
    topologicalKrullDim_add_of_smooth_restrict (K := K) p U t ht⟩⟩

/-! ### The tangent criterion for smoothness -/

section Algebraic

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- If `A` is formally smooth over `k` and `A → K` is surjective onto a field `K` that `k` maps
onto isomorphically, then the conormal map `I/I² → K ⊗_A Ω_{A/k}` of `I = ker (A → K)` is
bijective. -/
private lemma bijective_kerCotangentToTensor {K : Type u} [Field K] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] [Algebra.FormallySmooth k A]
    (hk : Function.Bijective (algebraMap k K)) (hA : Function.Surjective (algebraMap A K)) :
    Function.Bijective (KaehlerDifferential.kerCotangentToTensor k A K) := by
  let eK : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K) hk
  have : Algebra.FormallySmooth k K := .of_equiv eK
  have : Algebra.FormallyUnramified k K := .of_equiv eK
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) hA).mp inferInstance
  exact ⟨Function.LeftInverse.injective (g := l) (LinearMap.congr_fun hl),
    fun y => ((KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k A K hA) y).mp
      (Subsingleton.elim _ _)⟩

/-- **Jacobi–Zariski criterion for formal smoothness.** Let `k → A → B` with `B` local and
formally smooth over `k`, and `Ω_{A/k}`, `Ω_{B/k}` finite. Then `B` is formally smooth over `A`
if and only if `K ⊗_B (B ⊗_A Ω_{A/k}) → K ⊗_B Ω_{B/k}` is injective,
`K` the residue field of `B`. -/
private theorem formallySmooth_iff_injective_lTensor_mapBaseChange [IsLocalRing B]
    [Algebra.FormallySmooth k B] [Module.Finite A Ω[A⁄k]] [Module.Finite B Ω[B⁄k]] :
    Algebra.FormallySmooth A B ↔
      Function.Injective ((KaehlerDifferential.mapBaseChange k A B).lTensor (ResidueField B)) := by
  have hex := KaehlerDifferential.exact_mapBaseChange_map k A B
  have hsurj := KaehlerDifferential.map_surjective k A B
  rw [Algebra.formallySmooth_iff A B]
  constructor
  · rintro ⟨_, _⟩
    have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k A B) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := ((Algebra.H1Cotangent.exact_δ_mapBaseChange k A B) x).mp hx
      rw [Subsingleton.elim y 0, map_zero]
    obtain ⟨s, hs⟩ := Module.projective_lifting_property
      (KaehlerDifferential.map k A B B) LinearMap.id hsurj
    have h12 := hex.split_tfae'.out 1 2
    obtain ⟨-, l, hl⟩ := h12.mp ⟨hinj, s, hs⟩
    refine Function.LeftInverse.injective (g := l.lTensor _) fun x => ?_
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hl, LinearMap.lTensor_id,
      LinearMap.id_apply]
  · intro hF
    have : Module.Projective B Ω[B⁄k] := ((Algebra.formallySmooth_iff k B).mp inferInstance).1
    have : Module.Free B Ω[B⁄k] := Module.free_of_flat_of_isLocalRing
    obtain ⟨l, hl⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective _).mpr hF
    have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k A B) :=
      Function.LeftInverse.injective (g := l) (LinearMap.congr_fun hl)
    have h21 := hex.split_tfae'.out 2 1
    obtain ⟨-, s, hs⟩ := h21.mp ⟨hsurj, l, hl⟩
    refine ⟨.of_split s _ hs, ⟨fun x y => ?_⟩⟩
    have hδ : ∀ x, Algebra.H1Cotangent.δ k A B x = 0 := fun x => hinj (by
      rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange k A B).apply_apply_eq_zero, map_zero])
    have hδi : Function.Injective (Algebra.H1Cotangent.δ k A B) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨z, rfl⟩ := ((Algebra.H1Cotangent.exact_map_δ k A B) x).mp hx
      rw [Subsingleton.elim z 0, map_zero]
    exact hδi (by rw [hδ x, hδ y])

/-- **Algebraic tangent criterion.** Let `A → B` be a homomorphism of `k`-algebras with `B`
local, both formally smooth over `k` with finite modules of differentials, such that `k` maps
onto the residue field `K` of `B`. Then `B` is formally smooth over `A` if and only if the
induced map `ker (A → K)/ker (A → K)² → ker (B → K)/ker (B → K)²`
on cotangent spaces is injective. -/
private theorem formallySmooth_iff_injective_mapCotangent_ker [IsLocalRing B]
    [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k B]
    [Module.Finite A Ω[A⁄k]] [Module.Finite B Ω[B⁄k]]
    (hres : Function.Surjective (algebraMap k (ResidueField B)))
    (h : RingHom.ker (algebraMap A (ResidueField B)) ≤
      (RingHom.ker (algebraMap B (ResidueField B))).comap (algebraMap A B).toIntAlgHom) :
    Algebra.FormallySmooth A B ↔ Function.Injective
      (Ideal.mapCotangent (RingHom.ker (algebraMap A (ResidueField B)))
        (RingHom.ker (algebraMap B (ResidueField B))) (algebraMap A B).toIntAlgHom h) := by
  set K := ResidueField B
  have hk : Function.Bijective (algebraMap k K) := ⟨(algebraMap k K).injective, hres⟩
  have hA := bijective_kerCotangentToTensor (A := A) hk
    (by rw [IsScalarTower.algebraMap_eq k A K, RingHom.coe_comp] at hres; exact hres.of_comp)
  have hB := bijective_kerCotangentToTensor (A := B) hk residue_surjective
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange A B K K Ω[A⁄k]
  set F := (KaehlerDifferential.mapBaseChange k A B).lTensor K
  -- the square `F ∘ (c⁻¹ ∘ conormal_A) = conormal_B ∘ mapCotangent`
  have hsq : ∀ x, F (c.symm (KaehlerDifferential.kerCotangentToTensor k A K x)) =
      KaehlerDifferential.kerCotangentToTensor k B K
        (Ideal.mapCotangent _ _ (algebraMap A B).toIntAlgHom h x) := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
    have hc : c.symm (1 ⊗ₜ KaehlerDifferential.D k A x) =
        1 ⊗ₜ (1 ⊗ₜ KaehlerDifferential.D k A x) := by
      rw [LinearEquiv.symm_apply_eq]
      simp [c]
    simp only [Ideal.mapCotangent_toCotangent, KaehlerDifferential.kerCotangentToTensor_toCotangent,
      hc, F, LinearMap.lTensor_tmul, KaehlerDifferential.mapBaseChange_tmul, one_smul,
      KaehlerDifferential.map_D]
    rfl
  have he := c.symm.bijective.comp hA
  rw [formallySmooth_iff_injective_lTensor_mapBaseChange (k := k)]
  refine ⟨fun hF y z hyz => he.1 (hF ((hsq y).trans ((congrArg _ hyz).trans (hsq z).symm))),
    fun hinj y z hyz => ?_⟩
  obtain ⟨y, rfl⟩ := he.2 y
  obtain ⟨z, rfl⟩ := he.2 z
  exact congrArg _ (hinj (hB.1 ((hsq y).symm.trans (hyz.trans (hsq z)))))

end Algebraic

/-- Injectivity of a cotangent map only depends on the ideals, not on how they are written. -/
private lemma injective_mapCotangent_congr {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) {I I' : Ideal A} {J J' : Ideal B} (hI : I = I')
    (hJ : J = J') (h : I ≤ J.comap f) (h' : I' ≤ J'.comap f) :
    Function.Injective (I.mapCotangent J f h) ↔ Function.Injective (I'.mapCotangent J' f h') := by
  subst hI hJ
  rfl

/-- **Tangent criterion for smoothness.** Let `p : V ⟶ T` be a morphism of non-singular
varieties over an algebraically closed field `k` and `v` a closed point of `V`. Then `p` is
smooth at `v` if and only if the cotangent map `𝔪_{p v}/𝔪_{p v}² → 𝔪_v/𝔪_v²` induced by
`p.stalkMap v` is injective, i.e. the differential `dp_v : T_v V → T_{p v} T` is surjective. -/
@[mmp "lem_mmp_foundation_laz_smoothness_tangent_surjection"]
public theorem mem_smoothLocus_iff_injective_mapCotangent {k : Type u} [Field k] [IsAlgClosed k]
    {V T : Scheme.{u}} (fV : V ⟶ Spec (.of k)) (fT : T ⟶ Spec (.of k))
    (hVvar : Mori.IsVariety k fV) (hTvar : Mori.IsVariety k fT)
    (hV : Mori.IsSmoothScheme fV) (hT : Mori.IsSmoothScheme fT)
    (p : V ⟶ T) (hp : p ≫ fT = fV) {v : V} (hv : IsClosed ({v} : Set V)) :
    v ∈ Mori.smoothLocus p ↔
      Function.Injective
        (Ideal.mapCotangent (maximalIdeal (T.presheaf.stalk (p v)))
          (maximalIdeal (V.presheaf.stalk v)) (p.stalkMap v).hom.toIntAlgHom
          (fun x hx => map_nonunit (p.stalkMap v).hom x hx)) := by
  subst hp
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian fT
  have : LocallyOfFiniteType p := locallyOfFiniteType_of_comp p fT
  have : LocallyOfFinitePresentation p :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : LocallyOfFinitePresentation fT :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : Smooth fT := Scheme.Hom.smoothLocus_eq_top_iff.mp
    (by rwa [← Mori.smoothLocus_eq_smoothLocus])
  have : Smooth (p ≫ fT) := Scheme.Hom.smoothLocus_eq_top_iff.mp
    (by rwa [← Mori.smoothLocus_eq_smoothLocus])
  rw [Mori.smoothLocus_eq_smoothLocus, Scheme.Hom.mem_smoothLocus]
  letI := Mori.stalkAlgebra fT (p v)
  letI := Mori.stalkAlgebra (p ≫ fT) v
  letI : Algebra (T.presheaf.stalk (p v)) (V.presheaf.stalk v) := (p.stalkMap v).hom.toAlgebra
  haveI := Threefold.Resolution.isScalarTower_stalkMap fT p v
  obtain ⟨hsA, -, hfA⟩ := Flips.ResolutionInputs.stalk_facts (sX := fT) (p v)
  obtain ⟨hsB, -, hfB⟩ := Flips.ResolutionInputs.stalk_facts (sX := p ≫ fT) v
  have hres : Function.Surjective (algebraMap k (ResidueField (V.presheaf.stalk v))) := by
    have := Flips.ResolutionInputs.finite_residueField_of_isClosed (sX := p ≫ fT) v hv
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  have hsurjA : Function.Surjective
      (algebraMap (T.presheaf.stalk (p v)) (ResidueField (V.presheaf.stalk v))) := by
    rw [IsScalarTower.algebraMap_eq k (T.presheaf.stalk (p v)), RingHom.coe_comp] at hres
    exact hres.of_comp
  have hkA := eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurjA)
  have hkB := eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective
    (algebraMap (V.presheaf.stalk v) (ResidueField (V.presheaf.stalk v))) residue_surjective)
  have hle : RingHom.ker (algebraMap (T.presheaf.stalk (p v)) (ResidueField (V.presheaf.stalk v)))
      ≤ (RingHom.ker (algebraMap (V.presheaf.stalk v) (ResidueField (V.presheaf.stalk v)))).comap
        (algebraMap (T.presheaf.stalk (p v)) (V.presheaf.stalk v)).toIntAlgHom := by
    rw [hkA, hkB]
    exact fun x hx => map_nonunit (p.stalkMap v).hom x hx
  exact (formallySmooth_iff_injective_mapCotangent_ker hres hle).trans
    (injective_mapCotangent_congr _ hkA hkB _ _)

end MMP
