module
public import MMP.AlgebraicGeometry.Resolution.Principalization.ComponentSmoothSingularLoci
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic

/-!
# Strong resolution of embeddable varieties (Kollár, Remark 3.28)

Let `X` be a variety over a field `k` of characteristic `0` which admits a locally closed
embedding into a smooth variety `P` over `k`. Then `X` has a strong resolution:
a projective birational morphism `Π : R(X) → X` from a smooth variety `R(X)` which is an
isomorphism over the smooth locus `X^ns` and such that `Π⁻¹(Sing X)` is a divisor with simple
normal crossings on `R(X)`. The morphism is obtained by restricting the canonical principalization
of the ideal of `X × {0}` in `P° × 𝔸²` to `X`, up to the step at which the generic point of `X`
is blown up.

## Main results

* `MMP.Resolution.exists_strongResolution_of_isImmersion`: existence of the strong resolution.

## Implementation notes

The locally closed embedding is an immersion `ι : X ⟶ P` of `k`-schemes, `ι ≫ s_P = s_X`.
Projectivity of `Π` is meant in the sense of EGA II 5.5 / Stacks 01W8,
`AlgebraicGeometry.IsProjective` (a closed immersion over `X` into the projective bundle of a
quasi-coherent module of finite type): in this sense every blow-up of a Noetherian scheme in a
coherent ideal is projective, and so is the composite of a blow-up sequence, over any Noetherian
base, so no quasi-projectivity of `P` is needed. "Resolution" is spelled out field by field;
these are the fields of `MMP.Resolution.IsResolutionOfVariety`, whose projectivity
is this EGA notion as well: `R(X)` is a smooth variety over `k` via
`Π ≫ s_X`, and `Π` is projective and birational. "Isomorphism over `X^ns`" is the restriction of
`Π` to the preimage of `MMP.Mori.smoothLocus s_X` being an isomorphism; `Sing X` is
`MMP.Mori.singularLocus s_X`, and "divisor with simple normal crossings" is
`MMP.Resolution.IsSNCClosedSubset` over `k`.

The codimension of `X × {0}` in `𝔸²_{P°}` is bounded below one coordinate at a time: an
irreducible closed subset `W` of the zero section of `𝔸¹_S` is strictly contained in the
irreducible closed set `p⁻¹(p(W))`, and `p⁻¹` preserves strict chains, so the codimension goes up
by at least one. The restricted blow-up sequence is projective in the sense of
`AlgebraicGeometry.IsProjective` over any Noetherian base. The resolution of the reduced closed
subscheme `X × {0}` is transported to `X` along the isomorphism `X ≅ X × {0}`; projectivity
survives because an isomorphism is finite, hence projective, and birationality follows from the
isomorphism over the smooth locus, which contains the generic point. The auxiliary lemmas live in
the namespace `Proof_thm_kr3f_strong_resolution_embeddable`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Thm. 3.27 and Remark 3.28]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_thm_kr3f_strong_resolution_embeddable

/-- A morphism which is an isomorphism over a neighbourhood of every point of an open `S` is an
isomorphism over `S`. -/
private theorem isIso_morphismRestrict_of_forall_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : Y.Opens) (h : ∀ y ∈ S, ∃ V : Y.Opens, y ∈ V ∧ IsIso (f ∣_ V)) : IsIso (f ∣_ S) := by
  choose V hyV hV using h
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun y : S => S.ι ⁻¹ᵁ (V y.1 y.2)) ?_ fun y => ?_
  · exact eq_top_iff.mpr fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hyV _ _⟩
  · have : IsIso (f ∣_ (S.ι ''ᵁ (S.ι ⁻¹ᵁ V y.1 y.2))) := by
      haveI := hV y.1 y.2
      refine MMP.Resolution.Kollar.isIso_morphismRestrict_of_le f (W := V y.1 y.2) ?_
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_le_right
    exact (MorphismProperty.arrow_mk_iso_iff _ (morphismRestrictRestrict f S _)).mpr this

/-- The components of an irreducible closed set `closure {η}` are `closure {η}` alone. -/
private theorem componentsOf_closure_singleton {T : Type*} [TopologicalSpace T] (η : T) :
    componentsOf (closure {η} : Set T) = {closure {η}} := by
  ext W
  simp only [componentsOf, Set.mem_setOf_eq, Set.mem_singleton_iff]
  refine ⟨fun h => le_antisymm h.1.2 (h.2 ⟨isIrreducible_singleton.closure, le_rfl⟩ h.1.2), ?_⟩
  rintro rfl
  exact ⟨⟨isIrreducible_singleton.closure, le_rfl⟩, fun _ h _ => h.2⟩

/-- The empty set has no irreducible components. -/
private theorem componentsOf_empty {T : Type*} [TopologicalSpace T] :
    componentsOf (∅ : Set T) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hW =>
    hW.1.1.nonempty.ne_empty (Set.subset_empty_iff.mp hW.1.2)

/-- The generic point of an integral scheme locally of finite type over a perfect field is a
smooth point. -/
private theorem genericPoint_mem_smoothLocus {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType s] :
    genericPoint X ∈ smoothLocus s := by
  have : LocallyOfFinitePresentation s :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := s)).mpr inferInstance
  rw [smoothLocus_eq_smoothLocus]
  exact Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField _

/-- A monomial ideal sheaf on a locally Noetherian scheme is locally principal. -/
private theorem isLocallyPrincipal_of_isMonomialIdeal {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {I : Y.IdealSheafData} (h : IsMonomialIdeal I) : Stacks.Divisors.IsLocallyPrincipal I :=
  Stacks.Divisors.isLocallyPrincipal_of_stalk_isPrincipal _ fun x _ => by
    obtain ⟨n, z, c, -, hx⟩ := h x
    exact ⟨_, hx⟩

/-- An irreducible closed set of codimension `≥ 2` is the start of a strict chain of length two of
irreducible closed sets. -/
private theorem exists_ssubset_ssubset_of_two_le_codimension {T : Type*} [TopologicalSpace T]
    (W : IrreducibleCloseds T) (h : 2 ≤ codimension W) :
    ∃ Y₁ Y₂ : IrreducibleCloseds T, (W : Set T) ⊂ Y₁ ∧ (Y₁ : Set T) ⊂ Y₂ := by
  rw [codimension_eq_coheight] at h
  obtain ⟨p, hp, hlen⟩ := Order.exists_series_of_le_coheight W (n := 2) (by exact_mod_cast h)
  have h01 : p ⟨0, by omega⟩ < p ⟨1, by omega⟩ := p.strictMono (by simp [Fin.lt_def])
  refine ⟨_, _, ?_, SetLike.coe_ssubset_coe.mpr (p.strictMono (by simp [Fin.lt_def]) :
    p ⟨1, by omega⟩ < p ⟨2, by omega⟩)⟩
  rw [← hp]
  exact SetLike.coe_ssubset_coe.mpr h01

/-- The source of a blow-up sequence of a scheme locally of finite type over `S` is locally of
finite type over `S`. -/
private theorem locallyOfFiniteType_toBase_comp {X S : Scheme.{u}} (s : X ⟶ S)
    [LocallyOfFiniteType s] [IsLocallyNoetherian S] (B : ClosedBlowupSequence X) :
    LocallyOfFiniteType (B.toBase ≫ s) := by
  induction B with
  | nil X =>
    change LocallyOfFiniteType (𝟙 X ≫ s)
    rw [Category.id_comp]
    infer_instance
  | cons Z B ih =>
    have : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian s
    have : IsProper (blowUpToBase Z) := AlgebraicGeometry.isProper_blowUpToBase (I := Z)
    have := ih (blowUpToBase Z ≫ s)
    change LocallyOfFiniteType ((B.toBase ≫ blowUpToBase Z) ≫ s)
    rwa [Category.assoc]

/-! ### The zero section of the affine line and codimension -/

/-- The zero section `S ⟶ 𝔸¹_S`. -/
private noncomputable abbrev zeroSection (S : Scheme.{u}) : S ⟶ 𝔸(PUnit.{u+1}; S) :=
  AffineSpace.homOfVector (𝟙 S) 0

private theorem zeroSection_over (S : Scheme.{u}) :
    zeroSection S ≫ (𝔸(PUnit.{u+1}; S) ↘ S) = 𝟙 S :=
  AffineSpace.homOfVector_over _ _

private theorem over_zeroSection_apply (S : Scheme.{u}) (s : S) :
    (𝔸(PUnit.{u+1}; S) ↘ S).base ((zeroSection S).base s) = s := by
  rw [← Scheme.Hom.comp_apply, zeroSection_over]
  rfl

private theorem isClosedImmersion_zeroSection (S : Scheme.{u}) :
    IsClosedImmersion (zeroSection S) := by
  have : IsClosedImmersion (zeroSection S ≫ (𝔸(PUnit.{u+1}; S) ↘ S)) := by
    rw [zeroSection_over]
    infer_instance
  exact IsClosedImmersion.of_comp _ (𝔸(PUnit.{u+1}; S) ↘ S)

/-- The section of `𝔸¹_S` given by `v` meets the locus `coord ≠ 0` exactly over the locus
`v ≠ 0`. -/
private theorem homOfVector_mem_basicOpen_coord_iff (S : Scheme.{u})
    (v : PUnit.{u+1} → Γ(S, ⊤)) (s : S) :
    (AffineSpace.homOfVector (𝟙 S) v).base s ∈
        𝔸(PUnit.{u+1}; S).basicOpen (AffineSpace.coord S PUnit.unit) ↔
      s ∈ S.basicOpen (v PUnit.unit) := by
  change s ∈ AffineSpace.homOfVector (𝟙 S) v ⁻¹ᵁ
    𝔸(PUnit.{u+1}; S).basicOpen (AffineSpace.coord S PUnit.unit) ↔ _
  rw [Scheme.preimage_basicOpen]
  change s ∈ S.basicOpen ((AffineSpace.homOfVector (𝟙 S) v).appTop.hom _) ↔ _
  rw [AffineSpace.homOfVector_appTop_coord]

/-- The preimage of irreducible closed sets under a surjective open morphism is strictly
monotone. -/
private theorem strictMono_preimage_irreducibleCloseds {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [GeometricallyIrreducible f] (hf : IsOpenMap f.base) :
    StrictMono fun V : IrreducibleCloseds Y => (⟨f.base ⁻¹' V,
      f.isIrreducible_preimage hf V.isIrreducible, V.isClosed.preimage f.continuous⟩ :
        IrreducibleCloseds X) := by
  intro V₁ V₂ h
  rw [← SetLike.coe_ssubset_coe] at h ⊢
  change f.base ⁻¹' (V₁ : Set Y) ⊂ f.base ⁻¹' (V₂ : Set Y)
  refine ⟨Set.preimage_mono h.1, fun h' => h.2 fun s hs => ?_⟩
  obtain ⟨x, rfl⟩ := f.surjective s
  exact h' hs

/-- An irreducible closed subset `W` of the zero section of `𝔸¹_S` has codimension at least one
more than its image `V = σ⁻¹(W)` in `S`: `W ⊊ p⁻¹(V)`, and `p⁻¹` preserves strict chains. -/
private theorem codimension_add_one_le (S : Scheme.{u}) (W : IrreducibleCloseds 𝔸(PUnit.{u+1}; S))
    (hW : (W : Set 𝔸(PUnit.{u+1}; S)) ⊆ Set.range (zeroSection S).base) :
    ∃ V : IrreducibleCloseds S, (V : Set S) = (zeroSection S).base ⁻¹' W ∧
      codimension V + 1 ≤ codimension W := by
  set p := 𝔸(PUnit.{u+1}; S) ↘ S
  set σ := zeroSection S
  let τ : S ⟶ 𝔸(PUnit.{u+1}; S) := AffineSpace.homOfVector (𝟙 S) 1
  have hσp : ∀ s, p.base (σ.base s) = s := over_zeroSection_apply S
  have hτp : ∀ s, p.base (τ.base s) = s := fun s => by
    rw [← Scheme.Hom.comp_apply]
    simp [τ, p, AffineSpace.homOfVector_over]
  have hσc : ∀ s, σ.base s ∉ 𝔸(PUnit.{u+1}; S).basicOpen (AffineSpace.coord S PUnit.unit) :=
    fun s hs => by
      have := (homOfVector_mem_basicOpen_coord_iff S 0 s).mp hs
      rw [Pi.zero_apply, Scheme.basicOpen_zero] at this
      exact this
  have hτc : ∀ s, τ.base s ∈ 𝔸(PUnit.{u+1}; S).basicOpen (AffineSpace.coord S PUnit.unit) :=
    fun s => (homOfVector_mem_basicOpen_coord_iff S 1 s).mpr (by
      rw [Pi.one_apply, Scheme.basicOpen_one]
      trivial)
  have himg : σ.base ⁻¹' W = p.base '' W := by
    ext s
    refine ⟨fun hs => ⟨_, hs, hσp s⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    obtain ⟨t, rfl⟩ := hW hx
    simpa [Set.mem_preimage, hσp] using hx
  let V : IrreducibleCloseds S :=
    ⟨σ.base ⁻¹' W, himg ▸ W.isIrreducible.image _ p.continuous.continuousOn,
      W.isClosed.preimage σ.continuous⟩
  have hφ := strictMono_preimage_irreducibleCloseds p (AffineSpace.isOpenMap_over S)
  set φ := fun V : IrreducibleCloseds S => (⟨p.base ⁻¹' V,
    p.isIrreducible_preimage (AffineSpace.isOpenMap_over S) V.isIrreducible,
    V.isClosed.preimage p.continuous⟩ : IrreducibleCloseds 𝔸(PUnit.{u+1}; S))
  have hWT : W < φ V := by
    rw [← SetLike.coe_ssubset_coe]
    refine ⟨fun x hx => ?_, fun h => ?_⟩
    · obtain ⟨t, rfl⟩ := hW hx
      show p.base (σ.base t) ∈ σ.base ⁻¹' W
      rwa [hσp]
    · obtain ⟨s, hs⟩ := V.isIrreducible.nonempty
      have : τ.base s ∈ (W : Set _) :=
        h (show p.base (τ.base s) ∈ (V : Set S) by rwa [hτp])
      obtain ⟨t, ht⟩ := hW this
      exact hσc t (ht ▸ hτc s)
  refine ⟨V, rfl, ?_⟩
  rw [codimension_eq_coheight, codimension_eq_coheight]
  calc Order.coheight V + 1 ≤ Order.coheight (φ V) + 1 := by
        gcongr
        exact Order.coheight_le_coheight_apply_of_strictMono φ hφ V
    _ ≤ Order.coheight W := Order.coheight_add_one_le hWT

/-- An irreducible closed subset of `X × {0}` in `𝔸²_S = 𝔸¹_{𝔸¹_S}`, for any morphism
`i : X ⟶ S`, has codimension at least `2`. -/
private theorem two_le_codimension_of_subset_range {X S : Scheme.{u}} (i : X ⟶ S)
    (W : IrreducibleCloseds 𝔸(PUnit.{u+1}; 𝔸(PUnit.{u+1}; S)))
    (hW : (W : Set _) ⊆ Set.range (i ≫ zeroSection S ≫ zeroSection _).base) :
    2 ≤ codimension W := by
  obtain ⟨V, hV, hVW⟩ := codimension_add_one_le _ W fun x hx => by
    obtain ⟨y, rfl⟩ := hW hx
    exact ⟨(zeroSection S).base (i.base y), by simp only [Scheme.Hom.comp_apply]⟩
  obtain ⟨V', -, hV'⟩ := codimension_add_one_le S V fun s hs => by
    rw [hV] at hs
    obtain ⟨y, hy⟩ := hW hs
    refine ⟨i.base y, ?_⟩
    simpa only [Scheme.Hom.comp_apply, over_zeroSection_apply] using
      congrArg (𝔸(PUnit.{u+1}; 𝔸(PUnit.{u+1}; S)) ↘ 𝔸(PUnit.{u+1}; S)).base hy
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ codimension V' + 1 + 1 := by
      gcongr
      exact zero_le
    _ ≤ codimension V + 1 := by gcongr
    _ ≤ codimension W := hVW

/-- If the concatenation `D.append C` of blow-up sequences is smooth over `k`, so is `C`, over
the composite `D.toBase ≫ s`. -/
private theorem isSmooth_of_isSmooth_append {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (D : ClosedBlowupSequence X) (C : ClosedBlowupSequence D.target)
    (h : (D.append C).IsSmooth s) : C.IsSmooth (D.toBase ≫ s) := by
  induction D with
  | nil X =>
    change C.IsSmooth (𝟙 X ≫ s)
    rwa [Category.id_comp]
  | cons Z D ih =>
    change C.IsSmooth ((D.toBase ≫ blowUpToBase Z) ≫ s)
    rw [Category.assoc]
    exact ih _ C h.2.2

/-- A closed subscheme `W` whose ideal agrees, on an open `U` containing its support, with the
ideal of a closed subscheme `Z` smooth over `T`, is itself smooth over `T`. -/
private theorem smooth_subschemeι_of_comap_eq {Y T : Scheme.{u}} (t : Y ⟶ T)
    (W Z : Y.IdealSheafData) (U : Y.Opens) (hWU : (W.support : Set Y) ⊆ U)
    (h : W.comap U.ι = Z.comap U.ι) (hZ : Smooth (Z.subschemeι ≫ t)) :
    Smooth (W.subschemeι ≫ t) := by
  have key : ∀ V : U.toScheme.IdealSheafData, V = Z.comap U.ι →
      Smooth (V.subschemeι ≫ U.ι ≫ t) := by
    rintro _ rfl
    have e : (Z.comap U.ι).subschemeι ≫ U.ι ≫ t =
        ((Z.comapIso U.ι).hom ≫ Limits.pullback.snd U.ι Z.subschemeι) ≫ Z.subschemeι ≫ t := by
      rw [← Z.comapIso_hom_fst U.ι, Category.assoc, Category.assoc, ← Category.assoc _ U.ι,
        Limits.pullback.condition, Category.assoc]
    rw [e]
    infer_instance
  have hW := key _ h
  have hsnd : IsIso (Limits.pullback.snd U.ι W.subschemeι) := by
    refine (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨fun x => ?_⟩⟩
    have hx : W.subschemeι x ∈ U := hWU (by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩)
    change x ∈ Set.range (Limits.pullback.snd U.ι W.subschemeι)
    rw [IsOpenImmersion.range_pullbackSnd]
    simpa using hx
  have e : W.subschemeι ≫ t = inv (Limits.pullback.snd U.ι W.subschemeι) ≫
      ((W.comapIso U.ι).inv ≫ (W.comap U.ι).subschemeι ≫ U.ι ≫ t) := by
    rw [← W.comapIso_hom_fst U.ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Limits.pullback.condition_assoc, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- Restricting a blow-up sequence `T` to a closed subscheme `C`, if the restricted top space
sits (via the closed immersion `T.restrictHom C`) as a closed subscheme of `T.target` whose ideal
agrees, on an open `U` containing it, with that of a center `Z` smooth over `T.toBase ≫ t`, then
the restricted composite is smooth over `t`. -/
private theorem smooth_restrict_toBase_comp {X S : Scheme.{u}} (t : X ⟶ S)
    (T : ClosedBlowupSequence X) (C : X.IdealSheafData) [IsClosedImmersion (T.restrictHom C)]
    (Z : T.target.IdealSheafData) (U : T.target.Opens)
    (hιU : Set.range (T.restrictHom C) ⊆ U)
    (hker : (T.restrictHom C).ker.comap U.ι = Z.comap U.ι)
    (hZ : Smooth (Z.subschemeι ≫ T.toBase ≫ t)) :
    Smooth ((T.restrict C).toBase ≫ C.subschemeι ≫ t) := by
  have hW := smooth_subschemeι_of_comap_eq _ _ Z U (by
    rwa [Scheme.Hom.support_ker, (T.restrictHom C).isClosedEmbedding.isClosed_range.closure_eq])
    hker hZ
  have hc : (T.restrict C).toBase ≫ C.subschemeι = T.restrictHom C ≫ T.toBase :=
    (MMP.Resolution.Kollar.pullbackHom_toBase_comm _ _).symm
  rw [← Category.assoc, hc, ← Scheme.Hom.toImage_imageι (T.restrictHom C)]
  simp only [Category.assoc]
  infer_instance

/-- The smooth locus of a scheme of finite type over `k` is carried along isomorphisms over
`k`. -/
private theorem smoothLocus_iso_hom_comp {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (e : Y ≅ X) :
    smoothLocus (e.hom ≫ sX) = e.hom ⁻¹ᵁ smoothLocus sX := by
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  rw [smoothLocus_eq_smoothLocus, smoothLocus_eq_smoothLocus,
    Scheme.Hom.preimage_smoothLocus_eq]

/-- **Strong resolutions are carried along isomorphisms over `k`.** Let `Y ≅ X` over `k`, and
`g : R ⟶ Y` projective, from a smooth variety, an isomorphism over the smooth locus of `Y`, with
the preimage of the singular locus a divisor with simple normal crossings. Then `g` followed by
the isomorphism is a strong resolution of `X`. -/
private theorem exists_strongResolution_of_iso {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX)
    (sY : Y ⟶ Spec (.of k)) (e : Y ≅ X) (he : e.hom ≫ sX = sY)
    (h : ∃ (R : Scheme.{u}) (g : R ⟶ Y), AlgebraicGeometry.IsVariety k (g ≫ sY) ∧
      IsSmoothScheme (g ≫ sY) ∧ IsProjective g ∧
      IsIso (g ∣_ smoothLocus sY) ∧
      IsSNCClosedSubset (g ≫ sY) (g.base ⁻¹' (singularLocus sY : Set Y))) :
    ∃ (R : Scheme.{u}) (f : R ⟶ X), AlgebraicGeometry.IsVariety k (f ≫ sX) ∧
      IsSmoothScheme (f ≫ sX) ∧ IsProjective f ∧ IsBirationalMorphism f ∧
      IsIso (f ∣_ smoothLocus sX) ∧
      IsSNCClosedSubset (f ≫ sX) (f.base ⁻¹' (singularLocus sX : Set X)) := by
  subst he
  obtain ⟨R, g, hvar, hsmR, hproj, hiso, hsnc⟩ := h
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsIntegral X := hX.toIsIntegral
  have hvar' : AlgebraicGeometry.IsVariety k ((g ≫ e.hom) ≫ sX) := by
    simpa only [Category.assoc] using hvar
  have hsm := smoothLocus_iso_hom_comp sX e
  have hfiso : IsIso ((g ≫ e.hom) ∣_ smoothLocus sX) := by
    rw [morphismRestrict_comp]
    have h1 : IsIso (g ∣_ e.hom ⁻¹ᵁ smoothLocus sX) := hsm ▸ hiso
    have h2 : IsIso (e.hom ∣_ smoothLocus sX) :=
      IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
        (MorphismProperty.isomorphisms.infer_property _) _
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  refine ⟨R, g ≫ e.hom, hvar', ?_, ?_, ?_, hfiso, ?_⟩
  · simpa only [Category.assoc] using hsmR
  · have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated sX
    exact IsProjective.comp hproj (Stacks.FiniteMorphismProjective.isProjective_of_isFinite e.hom)
  · have : IsIntegral R := hvar'.toIsIntegral
    have hx := genericPoint_mem_smoothLocus sX
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE _ _ (smoothLocus sX)
      ⟨(inv ((g ≫ e.hom) ∣_ smoothLocus sX) ⟨_, hx⟩).1, (inv ((g ≫ e.hom) ∣_ smoothLocus sX)
        ⟨_, hx⟩).2⟩ ⟨_, hx⟩ le_rfl ?_
    simp only [Scheme.Hom.resLE, Scheme.homOfLE_rfl, Category.id_comp]
    infer_instance
  · have hsing : (g ≫ e.hom).base ⁻¹' (singularLocus sX : Set X) =
        g.base ⁻¹' (singularLocus (e.hom ≫ sX) : Set Y) := by
      ext r
      simp only [Set.mem_preimage, SetLike.mem_coe, mem_singularLocus_iff, hsm,
        Scheme.Hom.comp_base, TopCat.comp_app, Scheme.Hom.mem_preimage]
    rw [hsing]
    simpa only [Category.assoc] using hsnc

/-- **The strong resolution of an irreducible reduced closed subscheme of codimension `≥ 2`.**
Let `P` be smooth, separated, of finite type and equidimensional over a field of
characteristic `0`, and `C ⊆ P` the reduced closed subscheme `closure {η}`, of codimension
`≥ 2`. The canonical principalization of `I_C`, truncated at the step where `η` is blown up and
restricted to `C`, is projective from a smooth variety, an isomorphism over the smooth locus of
`C`, and pulls the singular locus of `C` back to a divisor with simple normal crossings. -/
private theorem exists_strongResolution_vanishingIdeal {k : Type u} [Field k] [CharZero k]
    {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) (hsm : IsSmoothScheme sP) [IsSeparated sP]
    [LocallyOfFiniteType sP] [QuasiCompact sP] (heq : Equidimensional P) (η : P)
    (hcodim : 2 ≤ closedsCodimension
      (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩).support) :
    let C : P.IdealSheafData :=
      Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩
    ∃ (R : Scheme.{u}) (g : R ⟶ C.subscheme),
      AlgebraicGeometry.IsVariety k (g ≫ C.subschemeι ≫ sP) ∧
      IsSmoothScheme (g ≫ C.subschemeι ≫ sP) ∧ IsProjective g ∧
      IsIso (g ∣_ smoothLocus (C.subschemeι ≫ sP)) ∧
      IsSNCClosedSubset (g ≫ C.subschemeι ≫ sP)
        (g.base ⁻¹' (singularLocus (C.subschemeι ≫ sP) : Set C.subscheme)) := by
  intro C
  have hsupp : (C.support : Set P) = closure {η} := by simp [C]
  have hη : closure {η} ∈ componentsOf (C.support : Set P) := by
    simp [hsupp, componentsOf_closure_singleton]
  have hconn : ∀ Z ∈ componentsOf (C.support : Set P), Z ≠ closure {η} →
      Disjoint Z (closure {η}) := by
    intro Z hZ hne
    exact absurd (by rwa [hsupp, componentsOf_closure_singleton] at hZ) hne
  have : IsIntegral C.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure η
  have hred : IsReduced C.subscheme := inferInstance
  have hmem : ∀ y, C.subschemeι.base y ∈ closure {η} := fun y => by
    rw [← hsupp, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨_, rfl⟩
  obtain ⟨ht, hsing⟩ := preimage_singularLocus_toBase_restrict_canonicalPrincipalization sP hsm
    heq C hred hcodim η hη hconn
  obtain ⟨_, hsnc⟩ :=
    isSNCClosedSubset_restrictHom_preimage_totalExceptionalSet_canonicalPrincipalization
      sP hsm heq C hcodim η hη _ (genericPoint_mem_smoothLocus _) (hmem _)
  obtain ⟨hprop1, hprop2, hprop3, -⟩ := canonicalPrincipalization_properties.{u, u, u}
  set B := canonicalPrincipalization _ (triples_subset_sncTriples ht)
  set g := ((B.truncate (B.entryIndex η)).restrict C).toBase
  have hcod' : ∃ Y₁ Y₂ : IrreducibleCloseds P, closure {η} ⊂ (Y₁ : Set P) ∧ (Y₁ : Set P) ⊂ Y₂ :=
    exists_ssubset_ssubset_of_two_le_codimension (IrreducibleCloseds.closureSingleton η)
      (MMP.Mori.le_closedsCodimension_iff.mp hcodim _ hsupp.ge)
  have : LocallyOfFiniteType (B.toBase ≫ sP) := locallyOfFiniteType_toBase_comp sP B
  have : IsLocallyNoetherian B.target := LocallyOfFiniteType.isLocallyNoetherian (B.toBase ≫ sP)
  have hcomp : (componentsOf (OrderedDivisor.empty P).support).Pairwise Disjoint := by
    simp [OrderedDivisor.support, OrderedDivisor.empty, componentsOf_empty]
  have hB : B.IsSmooth sP := (hprop1 _ ht).1
  have hcent : B.CentersLieOver (𝟙 P) (C.support : Set P) := (hprop3 _ ht hcomp).1
  have hCvar : AlgebraicGeometry.IsVariety k (C.subschemeι ≫ sP) := by
    constructor <;> infer_instance
  have hηC : IsGenericPoint η (C.support : Set P) := by simp [C, IsGenericPoint]
  obtain ⟨hvar, -, hproj, -⟩ :=
    ClosedBlowupSequence.isVariety_restrict_truncate_of_le_entryIndex sP B C hCvar hηC le_rfl
  obtain ⟨-, Z, B', hBeq, -, U, hιU, hker⟩ :=
    ClosedBlowupSequence.restrict_truncate_entryIndex_isConnectedComponent sP hsm C hη hcod'
      B hB (isLocallyPrincipal_of_isMonomialIdeal (hprop2 _ ht)) hcent
  have hB' : ((B.truncate (B.entryIndex η)).append (ClosedBlowupSequence.cons Z B')).IsSmooth sP :=
    hBeq ▸ hB
  have := MMP.Resolution.Kollar.isClosedImmersion_restrictHom_truncate B C (B.entryIndex η)
  refine ⟨_, g, hvar, ?_, hproj, ?_, ?_⟩
  · exact MMP.Mori.isSmoothScheme_of_smooth (smooth_restrict_toBase_comp sP _ C Z U hιU hker
      (MMP.Mori.IsSmoothScheme.smooth (isSmooth_of_isSmooth_append sP _ _ hB').2.1))
  · refine isIso_morphismRestrict_of_forall_exists g _ fun x hx => ?_
    obtain ⟨_, V, y, hyx, hyV, hV⟩ :=
      exists_isIso_morphismRestrict_toBase_restrict_canonicalPrincipalization sP hsm heq C
        hcodim η hη x hx (hmem _)
    exact ⟨V, C.subschemeι.isClosedEmbedding.injective hyx ▸ hyV, hV⟩
  · convert hsnc using 1

/-- The image of a closed immersion out of an irreducible scheme is the closure of the image of
its generic point. -/
private theorem range_eq_closure_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X]
    (j : X ⟶ Y) [IsClosedImmersion j] :
    Set.range j.base = closure {j.base (genericPoint X)} := by
  rw [((genericPoint_spec X).image j.continuous).def, Set.image_univ,
    j.isClosedEmbedding.isClosed_range.closure_eq]

/-- The affine plane `𝔸²_U` over an open `U` of a smooth, separated, quasi-compact `k`-scheme `P`
of finite type is again smooth, separated, quasi-compact and of finite type over `k`. -/
private theorem isSmoothScheme_affinePlane {k : Type u} [Field k] {P : Scheme.{u}}
    (sP : P ⟶ Spec (.of k)) (hPs : IsSmoothScheme sP) [IsSeparated sP] [LocallyOfFiniteType sP]
    [QuasiCompact sP] (U : P.Opens) :
    IsSmoothScheme ((𝔸(PUnit.{u+1}; 𝔸(PUnit.{u+1}; U)) ↘ 𝔸(PUnit.{u+1}; U)) ≫
        (𝔸(PUnit.{u+1}; U) ↘ U) ≫ U.ι ≫ sP) ∧
      IsSeparated ((𝔸(PUnit.{u+1}; 𝔸(PUnit.{u+1}; U)) ↘ 𝔸(PUnit.{u+1}; U)) ≫
        (𝔸(PUnit.{u+1}; U) ↘ U) ≫ U.ι ≫ sP) ∧
      LocallyOfFiniteType ((𝔸(PUnit.{u+1}; 𝔸(PUnit.{u+1}; U)) ↘ 𝔸(PUnit.{u+1}; U)) ≫
        (𝔸(PUnit.{u+1}; U) ↘ U) ≫ U.ι ≫ sP) ∧
      QuasiCompact ((𝔸(PUnit.{u+1}; 𝔸(PUnit.{u+1}; U)) ↘ 𝔸(PUnit.{u+1}; U)) ≫
        (𝔸(PUnit.{u+1}; U) ↘ U) ≫ U.ι ≫ sP) := by
  have : Smooth (𝔸(PUnit.{u+1}; 𝔸(PUnit.{u+1}; U)) ↘ 𝔸(PUnit.{u+1}; U)) :=
    smooth_affineSpace_over _ _
  have : Smooth (𝔸(PUnit.{u+1}; U) ↘ U) := smooth_affineSpace_over _ _
  have : LocallyOfFinitePresentation sP :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sP)).mpr inferInstance
  have : Smooth sP := (isSmoothScheme_iff sP).mp hPs
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace sP
  have : IsNoetherian P := {}
  refine ⟨?_, inferInstance, inferInstance, inferInstance⟩
  have : LocallyOfFinitePresentation ((𝔸(PUnit.{u+1}; 𝔸(PUnit.{u+1}; U)) ↘ 𝔸(PUnit.{u+1}; U)) ≫
      (𝔸(PUnit.{u+1}; U) ↘ U) ≫ U.ι ≫ sP) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := _)).mpr inferInstance
  rw [isSmoothScheme_iff]
  infer_instance

/-- The reduced closed subscheme on the image `closure {η}` of a closed immersion `j : X ⟶ Y` of
a reduced scheme is isomorphic to `X`, compatibly with the structure morphisms. -/
private theorem exists_iso_subscheme_vanishingIdeal {X Y T : Scheme.{u}} [IsReduced X]
    (j : X ⟶ Y) [IsClosedImmersion j] (s : X ⟶ T) (t : Y ⟶ T) (hj : j ≫ t = s) (η : Y)
    (hrange : Set.range j.base = closure {η}) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩).subscheme ≅ X,
      e.hom ≫ s =
        (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩).subschemeι ≫ t := by
  have hker : j.ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩ := by
    have : IsReduced j.ker.subscheme := isReduced_of_isOpenImmersion (inv j.toImage)
    refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
    ext1
    rw [Scheme.Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq, hrange]
    rfl
  have key : ∀ I : Y.IdealSheafData, j.ker = I →
      ∃ e : I.subscheme ≅ X, e.hom ≫ s = I.subschemeι ≫ t := by
    rintro _ rfl
    refine ⟨(asIso j.toImage).symm, ?_⟩
    have h1 : j.toImage ≫ j.ker.subschemeι = j := Scheme.Hom.toImage_imageι j
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, reassoc_of% h1, hj]
  exact key _ hker

end Proof_thm_kr3f_strong_resolution_embeddable

namespace MMP.Resolution

open Proof_thm_kr3f_strong_resolution_embeddable

/-- **Strong resolution of embeddable varieties** (Kollár, Remark 3.28). Let `X` be a variety over
a field `k` of characteristic `0` admitting a locally closed embedding `ι : X ⟶ P` into a smooth
variety `P` over `k`. Then there is a projective (in the sense of `AlgebraicGeometry.IsProjective`)
birational morphism `f : R ⟶ X` such that
1. `R` is a smooth variety over `k` via `f ≫ sX`;
2. `f` is an isomorphism over the smooth locus `smoothLocus sX`;
3. `f⁻¹(singularLocus sX)` is a divisor with simple normal crossings on `R`. -/
@[mmp "thm_kr3f_strong_resolution_embeddable"]
public theorem exists_strongResolution_of_isImmersion {k : Type u} [Field k] [CharZero k]
    {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX)
    (sP : P ⟶ Spec (.of k)) (hPv : AlgebraicGeometry.IsVariety k sP) (hPs : IsSmoothScheme sP)
    (ι : X ⟶ P) [IsImmersion ι] (hι : ι ≫ sP = sX) :
    ∃ (R : Scheme.{u}) (f : R ⟶ X), AlgebraicGeometry.IsVariety k (f ≫ sX) ∧
      IsSmoothScheme (f ≫ sX) ∧ IsProjective f ∧ IsBirationalMorphism f ∧
      IsIso (f ∣_ smoothLocus sX) ∧
      IsSNCClosedSubset (f ≫ sX) (f.base ⁻¹' (singularLocus sX : Set X)) := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral P := hPv.toIsIntegral
  have : LocallyOfFiniteType sP := hPv.toLocallyOfFiniteType
  have : IsSeparated sP := hPv.toIsSeparated
  set U := ι.coborderRange
  set i : X ⟶ U := ι.liftCoborder
  have : Nonempty U := ⟨i.base (genericPoint X)⟩
  obtain ⟨hsmA, _, _, _⟩ := isSmoothScheme_affinePlane sP hPs U
  set A₁ := 𝔸(PUnit.{u+1}; U)
  set A₂ := 𝔸(PUnit.{u+1}; A₁)
  set sA : A₂ ⟶ Spec (.of k) := (A₂ ↘ A₁) ≫ (A₁ ↘ U) ≫ U.ι ≫ sP
  set j : X ⟶ A₂ := i ≫ zeroSection U ≫ zeroSection A₁
  have hj : j ≫ sA = sX := by
    simp only [j, sA, Category.assoc]
    rw [reassoc_of% zeroSection_over A₁, reassoc_of% zeroSection_over U, ← hι,
      ← Scheme.Hom.liftCoborder_ι ι, Category.assoc]
  have := isClosedImmersion_zeroSection U
  have := isClosedImmersion_zeroSection A₁
  have : IsClosedImmersion j := by
    simp only [j]
    infer_instance
  set η : A₂ := j.base (genericPoint X)
  have hrange : Set.range j.base = closure {η} := range_eq_closure_genericPoint j
  have heqA : Equidimensional A₂ := Equidimensional.of_preirreducibleSpace A₂
  have hcodim : 2 ≤ closedsCodimension
      (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩).support := by
    rw [MMP.Mori.le_closedsCodimension_iff]
    intro W hW
    refine two_le_codimension_of_subset_range i W ?_
    rw [hrange]
    simpa using hW
  obtain ⟨e, he⟩ := exists_iso_subscheme_vanishingIdeal j sX sA hj η hrange
  exact exists_strongResolution_of_iso sX hX _ e he
    (exists_strongResolution_vanishingIdeal sA hsmA heqA η hcodim)

end MMP.Resolution

end
