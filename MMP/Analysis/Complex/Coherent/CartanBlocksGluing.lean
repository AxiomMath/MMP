module

public import MMP.Topology.Sheaves.ExtRightDerived
public import MMP.Topology.Sheaves.GodementOpenEmbedding
public import MMP.Algebra.Category.ModuleCat.Sheaf.FreeSections
public import MMP.Analysis.Complex.HolomorphicCompactConvergence
public import MMP.Analysis.Complex.Coherent.CartanMatrixSplitting
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSiteWeakSerre

/-!
# Cartan's theorems on compact blocks: gluing of resolutions

Results on sheaves of modules over opens of `ℂⁿ` and on compact blocks
`∏ᵢ [aᵢ, bᵢ] × [cᵢ, dᵢ]` of `ℂⁿ`: shrinking of compact sets, truncation and dimension shifting
of resolutions, `Ext` comparisons, restriction of sheaves of modules to opens, Dolbeault sheaves,
finite free resolutions, matrices over sections, Cartan's matrix splitting on blocks, and the
gluing of finite free resolutions given on two blocks with a common face.

## Main definitions

* `HasFFR`: a sheaf of modules has a finite free resolution of length `≤ ℓ`.
* `SplitProp`: Cartan's splitting property for a pair of sets.

## Main results

* `isZero_of_isZero_res`, `epi_of_epi_res`, `mono_of_mono_res`: vanishing, surjectivity and
  injectivity of sheaves of modules are local.
* `exists_glue_tuple`: tuples of sections near `K₁` and near `K₂`, related near `K₁ ∩ K₂` by an
  invertible holomorphic matrix, glue after a holomorphic change of basis.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite MMP.Analytic

namespace MMP.Analytic.CartanCompactBlocks

open scoped Manifold ContDiff

/-! ### Shrinking -/

/-- **Shrinking.** If two compact sets `K₁`, `K₂` of a metric space meet inside an open set `W`,
then for some `η > 0` their open `η`-neighbourhoods already meet inside `W`. -/
theorem exists_thickening_inter_thickening_subset {X : Type*} [MetricSpace X]
    {K₁ K₂ W : Set X} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂) (hW : IsOpen W)
    (hKW : K₁ ∩ K₂ ⊆ W) :
    ∃ η > 0, Metric.thickening η K₁ ∩ Metric.thickening η K₂ ⊆ W := by
  obtain ⟨ε, hε, hεW⟩ := (h₁.inter_right h₂.isClosed).exists_thickening_subset_open hW hKW
  set K₀ := K₁ \ Metric.thickening (ε / 2) (K₁ ∩ K₂)
  have hK₀ : IsCompact K₀ := h₁.diff Metric.isOpen_thickening
  have hdisj : Disjoint K₀ K₂ := by
    rw [Set.disjoint_left]
    intro x hx hx2
    exact hx.2 (Metric.self_subset_thickening (by positivity) _ ⟨hx.1, hx2⟩)
  obtain ⟨δ, hδ, hδd⟩ := hdisj.exists_thickenings hK₀ h₂.isClosed
  refine ⟨min δ (ε / 2), lt_min hδ (by positivity), ?_⟩
  rintro x ⟨hx1, hx2⟩
  obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.1 hx1
  by_cases hy0 : y ∈ Metric.thickening (ε / 2) (K₁ ∩ K₂)
  · apply hεW
    obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.1 hy0
    refine Metric.mem_thickening_iff.2 ⟨z, hz, ?_⟩
    calc dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (lt_of_lt_of_le hxy (min_le_right _ _)) hyz
      _ = ε := by ring
  · exfalso
    refine Set.disjoint_left.1 hδd (Metric.mem_thickening_iff.2 ⟨y, ⟨hy, hy0⟩, ?_⟩)
      (Metric.thickening_mono (min_le_left _ _) _ hx2)
    exact lt_of_lt_of_le hxy (min_le_left _ _)

/-! ### Truncating a resolution -/

section Truncation

variable {C : Type*} [Category C] [Abelian C]

/-- An epimorphism and its kernel form a short exact sequence. -/
theorem shortExact_kernel {A F : C} (ε : A ⟶ F) [Epi ε] :
    (ShortComplex.mk (kernel.ι ε) ε (kernel.condition ε)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel ε)

/-- **Truncation.** If `K → F` is a resolution (exact in positive degrees and at `K₀`), then
`K_{≥ 1}` resolves `ker ε` through the lift of `d₁₀`. -/
theorem truncate_resolution (K : ChainComplex C ℕ) {F : C} (ε : K.X 0 ⟶ F)
    (hexact : ∀ i, 0 < i → K.ExactAt i) (h : K.d 1 0 ≫ ε = 0)
    (hex : (ShortComplex.mk _ _ h).Exact) :
    Epi (kernel.lift ε (K.d 1 0) h) ∧ (∀ i, 0 < i → (ChainComplex.truncate.obj K).ExactAt i) ∧
      ∃ h' : (ChainComplex.truncate.obj K).d 1 0 ≫ kernel.lift ε (K.d 1 0) h = 0,
        (ShortComplex.mk _ _ h').Exact := by
  let K' := (ChainComplex.truncate).obj K
  let ε' : K'.X 0 ⟶ kernel ε := kernel.lift ε (K.d 1 0) h
  have hι : ε' ≫ kernel.ι ε = K.d 1 0 := kernel.lift_ι _ _ _
  have h' : K'.d 1 0 ≫ ε' = 0 := by
    apply (cancel_mono (kernel.ι ε)).1
    rw [Category.assoc, hι, zero_comp]
    exact K.d_comp_d 2 1 0
  refine ⟨hex.epi_kernelLift, fun i hi => ?_, h', ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have := hexact (j + 2) (by omega)
    rw [K.exactAt_iff' (j + 3) (j + 2) (j + 1) (by simp) (by simp)] at this
    rwa [HomologicalComplex.exactAt_iff' _ (j + 2) (j + 1) j (by simp) (by simp)]
  · let φ : ShortComplex.mk _ _ h' ⟶
        ShortComplex.mk (K.d 2 1) (K.d 1 0) (K.d_comp_d 2 1 0) :=
      { τ₁ := 𝟙 (K.X 2), τ₂ := 𝟙 (K.X 1), τ₃ := kernel.ι ε
        comm₁₂ := (Category.id_comp (K.d 2 1)).trans (Category.comp_id (K'.d 1 0)).symm
        comm₂₃ := (Category.id_comp (K.d 1 0)).trans hι.symm }
    haveI : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 (K.X 2)))
    haveI : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (K.X 1)))
    haveI : Mono φ.τ₃ := inferInstanceAs (Mono (kernel.ι ε))
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
    exact (K.exactAt_iff' 2 1 0 (by simp) (by simp)).1 (hexact 1 Nat.zero_lt_one)

end Truncation

/-! ### Dimension shifting -/

section DimensionShifting

open Limits Abelian

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- `Ext` into a zero object vanishes. -/
theorem subsingleton_ext_of_isZero (X : C) {Y : C} (h : IsZero Y) (n : ℕ) :
    Subsingleton (Ext X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.comp_mk₀_id x, h.eq_of_src (𝟙 Y) 0, Ext.mk₀_zero, Ext.comp_zero]

/-- In a short exact sequence `0 → S₁ → S₂ → S₃ → 0`, `Ext^q(X, S₃)` vanishes once
`Ext^q(X, S₂)` and `Ext^{q+1}(X, S₁)` do. -/
theorem subsingleton_ext_X₃_of_shortExact (X : C) {S : ShortComplex C}
    (hS : S.ShortExact) {q : ℕ} (h₂ : Subsingleton (Ext X S.X₂ q))
    (h₁ : Subsingleton (Ext X S.X₁ (q + 1))) :
    Subsingleton (Ext X S.X₃ q) := by
  refine subsingleton_of_forall_eq 0 fun x₃ => ?_
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ X hS x₃ rfl (Subsingleton.elim _ _)
  rw [← hx₂, Subsingleton.elim x₂ 0, Ext.zero_comp]

/-- **Dimension shifting.** Let `0 → K_ℓ → ⋯ → K_0 → F → 0` be a bounded resolution of `F`
whose terms satisfy `Ext^q(X, K_i) = 0` for `q ≥ 1`. Then `Ext^q(X, -)` vanishes for `q ≥ 1` on
`F` and on the kernel of the augmentation. -/
theorem subsingleton_ext_of_resolution (X : C) (ℓ : ℕ) :
    ∀ (K : ChainComplex C ℕ) {F : C} (ε : K.X 0 ⟶ F),
      (∀ i, ∀ q, 1 ≤ q → Subsingleton (Ext X (K.X i) q)) →
      (∀ i, ℓ < i → IsZero (K.X i)) → (∀ i, 0 < i → K.ExactAt i) → Epi ε →
      ∀ (h : K.d 1 0 ≫ ε = 0), (ShortComplex.mk _ _ h).Exact →
      (∀ q, 1 ≤ q → Subsingleton (Ext X (kernel ε) q)) ∧
        ∀ q, 1 ≤ q → Subsingleton (Ext X F q) := by
  suffices key : ∀ (K : ChainComplex C ℕ) {F : C} (ε : K.X 0 ⟶ F),
      (∀ i, ∀ q, 1 ≤ q → Subsingleton (Ext X (K.X i) q)) → Epi ε →
      (∀ q, 1 ≤ q → Subsingleton (Ext X (kernel ε) q)) →
        ∀ q, 1 ≤ q → Subsingleton (Ext X F q) by
    induction ℓ with
    | zero =>
      intro K F ε hK hzero hexact hε h hex
      have hk : ∀ q, 1 ≤ q → Subsingleton (Ext X (kernel ε) q) := by
        intro q _
        apply subsingleton_ext_of_isZero
        have : Epi (kernel.lift ε (K.d 1 0) h) := hex.epi_kernelLift
        exact IsZero.of_epi (kernel.lift ε (K.d 1 0) h) (hzero 1 Nat.zero_lt_one)
      exact ⟨hk, key K ε hK hε hk⟩
    | succ ℓ ih =>
      intro K F ε hK hzero hexact hε h hex
      obtain ⟨hε', hexact', h', hex'⟩ := truncate_resolution K ε hexact h hex
      have hk := (ih _ _ (fun i => hK (i + 1)) (fun i hi => hzero (i + 1) (by omega)) hexact'
        hε' h' hex').2
      exact ⟨hk, key K ε hK hε hk⟩
  intro K F ε hK hε hk q hq
  exact subsingleton_ext_X₃_of_shortExact X (shortExact_kernel ε) (hK 0 q hq)
    (hk (q + 1) (by omega))

end DimensionShifting

/-! ### Sheaf cohomology as `Ext` -/

section ExtComparison

universe w

/-- If `(R^{q+1} Γ(X, -))(F)` vanishes, so does `H'^{q+1}(X, F) = Ext^{q+1}(ℤ_⊤, F)`: a cocycle
`ℤ_⊤ ⟶ I^{q+1}` of an injective resolution is a global section killed by the differential, hence
the image of a global section of `I^q`. -/
theorem subsingleton_H'_of_isZero_rightDerived {X : TopCat.{0}}
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
    [(globalSections X).Additive]
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (q : ℕ)
    (h : Limits.IsZero (((globalSections X).rightDerived (q + 1)).obj F)) :
    Subsingleton (Sheaf.H' F (q + 1) (⊤ : Opens X)) := by
  have : HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{0} X) := ‹_›
  let R : InjectiveResolution F := injectiveResolution F
  have h' := h.of_iso (R.isoRightDerivedObj (globalSections X) (q + 1)).symm
  change Limits.IsZero
    ((((globalSections X).mapHomologicalComplex _).obj R.cocomplex).homology (q + 1)) at h'
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at h'
  let P : TopCat.Sheaf AddCommGrpCat.{0} X := freeYonedaTop X
  let e : ∀ G : TopCat.Sheaf AddCommGrpCat.{0} X, (P ⟶ G) ≃ G.obj.obj (op ⊤) :=
    fun G => freeYonedaTopHomEquiv (X := X) G
  have he : ∀ {G G' : TopCat.Sheaf AddCommGrpCat.{0} X} (f : P ⟶ G) (k : G ⟶ G'),
      e G' (f ≫ k) = k.hom.app (op ⊤) (e G f) := fun f k => freeYonedaTopHomEquiv_comp f k
  have he0 : ∀ G : TopCat.Sheaf AddCommGrpCat.{0} X, e G 0 = 0 := fun G =>
    freeYonedaTopHomEquiv_zero G
  show Subsingleton (Abelian.Ext P F (q + 1))
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective y (q + 2) rfl
  rw [R.extMk_eq_zero_iff f (q + 2) rfl hf q rfl]
  obtain ⟨g', hg'⟩ := h' (e _ f) (by
    have := he f (R.cocomplex.d (q + 1) (q + 2))
    rw [hf, he0] at this
    exact this.symm)
  refine ⟨(e _).symm g', (e _).injective ?_⟩
  rw [he]
  exact (congrArg _ ((e (R.cocomplex.X q)).apply_symm_apply g')).trans hg'

end ExtComparison

/-! ### Exactness and restriction -/

section Exactness

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{0})
  [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- The underlying abelian sheaf of a sheaf of modules commutes with finite colimits: colimits
of sheaves of modules are sheafified colimits of presheaves of modules. -/
theorem preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{0} R) := by
  constructor
  intro K _ _
  constructor
  intro F
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let H := F ⋙ SheafOfModules.forget R
  let e : F ≅ H ⋙ PresheafOfModules.sheafification (𝟙 R.obj) :=
    Functor.isoWhiskerLeft F (asIso adj.counit).symm
  suffices PreservesColimit (H ⋙ PresheafOfModules.sheafification (𝟙 R.obj))
      (SheafOfModules.toSheaf R) from preservesColimit_of_iso_diagram _ e.symm
  have h1 : IsColimit ((PresheafOfModules.sheafification (𝟙 R.obj)).mapCocone
      (colimit.cocone H)) := isColimitOfPreserves _ (colimit.isColimit H)
  have h2 : PreservesColimit H (PresheafOfModules.sheafification (𝟙 R.obj) ⋙
      SheafOfModules.toSheaf R) :=
    preservesColimit_of_natIso _ (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  exact preservesColimit_of_preserves_colimit_cocone h1
    (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 R.obj) ⋙
      SheafOfModules.toSheaf R) (colimit.isColimit H))

end Exactness

section Restriction

variable {X : TopCat.{0}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0})

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
/-- Pushforward of presheaves of modules along a functor preserves finite limits. -/
theorem preservesFiniteLimits_presheafPushforward {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) (S : Dᵒᵖ ⥤ RingCat.{0}) (R' : Cᵒᵖ ⥤ RingCat.{0})
    (φ : R' ⟶ F.op ⋙ S) : PreservesFiniteLimits (PresheafOfModules.pushforward.{0} φ) := by
  have : PreservesFiniteLimits
      (PresheafOfModules.pushforward.{0} φ ⋙ PresheafOfModules.toPresheaf _) :=
    inferInstanceAs (PreservesFiniteLimits
      (PresheafOfModules.toPresheaf _ ⋙ (Functor.whiskeringLeft _ _ _).obj F.op))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf _)

/-- The restriction `M ↦ M|_V` of sheaves of modules on `Over W` to `Over V`, for `V ≤ W`. -/
noncomputable abbrev res {V W : Opens X} (h : V ≤ W) :
    SheafOfModules.{0} (R.over W) ⥤ SheafOfModules.{0} (R.over V) :=
  SheafOfModules.overMap R (homOfLE h)

/-- Restriction of sheaves of modules from `W` to `V ≤ W` preserves finite limits. -/
theorem preservesFiniteLimits_res {V W : Opens X} (h : V ≤ W) :
    PreservesFiniteLimits (res R h) := by
  have := preservesFiniteLimits_presheafPushforward (Over.map (homOfLE h))
    (R.over W).obj (R.over V).obj (Sheaf.pushforwardOverMapIso R (homOfLE h)).inv.hom
  have : PreservesFiniteLimits (res R h ⋙ SheafOfModules.forget _) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward _))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.forget _)

/-- Restriction of sheaves of modules from `W` to `V ≤ W` preserves colimits. -/
theorem preservesColimits_res {V W : Opens X} (h : V ≤ W) :
    PreservesColimitsOfSize.{0, 0} (res R h) :=
  (SheafOfModules.overMapPushforwardAdj R (homOfLE h)).leftAdjoint_preservesColimits

/-- The restriction functor `SheafOfModules.overFunctor R W` to `Over W` preserves finite
limits. -/
theorem preservesFiniteLimits_overFunctor (W : Opens X) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{0} R W) := by
  have : PreservesFiniteLimits (PresheafOfModules.pushforward.{0}
      (𝟙 (R.over W) : R.over W ⟶ R.over W).hom) :=
    preservesFiniteLimits_presheafPushforward (Over.forget W) _ _ _
  have : PreservesFiniteLimits (SheafOfModules.overFunctor.{0} R W ⋙ SheafOfModules.forget _) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward _))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.forget _)

/-- Morphisms in `Over T` are unique. -/
lemma over_hom_ext {T : Opens X} {A B : Over T} (f g : A ⟶ B) : f = g :=
  Over.OverMorphism.ext (Subsingleton.elim _ _)

/-- The terminal object `T ⟶ T` of `Over T`. -/
abbrev topOver (T : Opens X) : Over T := Over.mk (𝟙 T)

/-- The unique morphism from an object of `Over T` to the terminal object `topOver T`. -/
abbrev toTopOver {T : Opens X} (A : Over T) : A ⟶ topOver T := Over.homMk A.hom

variable {R}

/-- The sections over all of `T` of a sheaf of modules on `Over T`. -/
abbrev Γ {T : Opens X} (M : SheafOfModules.{0} (R.over T)) := M.val.obj (op (topOver T))

/-- The section of `M` determined by its value over the terminal object. -/
noncomputable def secOfTop {T : Opens X} (M : SheafOfModules.{0} (R.over T)) (t : Γ M) :
    M.sections :=
  PresheafOfModules.sectionsMk (fun A => M.val.map (toTopOver A.unop).op t) (by
    intro A B f
    rw [← PresheafOfModules.map_comp_apply]
    congr 2)

/-- The value of `secOfTop M t` over `A` is the restriction of `t` to `A`. -/
lemma secOfTop_coe {T : Opens X} (M : SheafOfModules.{0} (R.over T)) (t : Γ M)
    (A : (Over T)ᵒᵖ) : (secOfTop M t).1 A = M.val.map (toTopOver A.unop).op t := rfl

/-- The value of `secOfTop M t` over the terminal object is `t`. -/
lemma secOfTop_top {T : Opens X} (M : SheafOfModules.{0} (R.over T)) (t : Γ M) :
    (secOfTop M t).1 (op (topOver T)) = t := by
  rw [secOfTop_coe, over_hom_ext (toTopOver _) (𝟙 _), op_id, PresheafOfModules.map_id]
  rfl

/-- The morphism `𝒪ᵖ ⟶ M` sending `eᵢ` to `tᵢ`, for sections `tᵢ` of `M` over `T`. -/
noncomputable def ofTop {T : Opens X} {M : SheafOfModules.{0} (R.over T)} {I : Type}
    (t : I → Γ M) : SheafOfModules.free I ⟶ M :=
  M.freeHomEquiv.symm fun i => secOfTop M (t i)

/-- The basis section `eᵢ` of `𝒪ᵖ` over `T`. -/
noncomputable abbrev eb {T : Opens X} {I : Type} (i : I) :
    Γ (SheafOfModules.free (R := R.over T) I) :=
  (SheafOfModules.freeSection i).1 (op (topOver T))

/-- `ofTop t` sends the basis section `eᵢ` to `tᵢ`. -/
lemma ofTop_app_eb {T : Opens X} {M : SheafOfModules.{0} (R.over T)} {I : Type}
    (t : I → Γ M) (i : I) : (ofTop t).val.app (op (topOver T)) (eb i) = t i := by
  have h := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection (M := M)
    (fun i => secOfTop M (t i)) i
  have h' := congrArg (fun s : M.sections => s.1 (op (topOver T))) h
  simp only [PresheafOfModules.sectionsMap_coe] at h'
  rwa [secOfTop_top] at h'

/-- A morphism `f` out of a free sheaf of modules is `ofTop` of the images `f(eᵢ)` of the basis
sections. -/
lemma eq_ofTop {T : Opens X} {M : SheafOfModules.{0} (R.over T)} {I : Type}
    (f : SheafOfModules.free I ⟶ M) :
    f = ofTop fun i => f.val.app (op (topOver T)) (eb i) := by
  apply M.freeHomEquiv.injective
  funext i
  refine Subtype.ext (funext fun A => ?_)
  rw [ofTop, Equiv.apply_symm_apply, secOfTop_coe, SheafOfModules.freeHomEquiv_apply,
    PresheafOfModules.sectionsMap_coe, ← PresheafOfModules.naturality_apply]
  congr 1
  exact ((SheafOfModules.freeSection i).2 (toTopOver A.unop).op).symm

/-- Composing `ofTop t` with `g` gives `ofTop` of the sections `g(tᵢ)`. -/
lemma ofTop_comp {T : Opens X} {M N : SheafOfModules.{0} (R.over T)} {I : Type}
    (t : I → Γ M) (g : M ⟶ N) :
    ofTop t ≫ g = ofTop fun i => g.val.app (op (topOver T)) (t i) := by
  rw [eq_ofTop (ofTop t ≫ g)]
  congr 1
  funext i
  change g.val.app _ ((ofTop t).val.app _ (eb i)) = _
  rw [ofTop_app_eb]

/-- The morphism `𝒪ᵖ ⟶ 𝒪^q` given by a matrix: `eₖ ↦ ∑ⱼ aₖⱼ eⱼ`. -/
noncomputable def ofMatrix {T : Opens X} {I J : Type} [Fintype J]
    (a : Matrix I J ((R.over T).obj.obj (op (topOver T)))) :
    SheafOfModules.free (R := R.over T) I ⟶ SheafOfModules.free J :=
  ofTop fun k => ∑ j, a k j • eb j

/-- `ofMatrix a ≫ ofTop t` is `ofTop` of the sections `∑ⱼ aₖⱼ tⱼ`. -/
lemma ofMatrix_comp_ofTop {T : Opens X} {M : SheafOfModules.{0} (R.over T)} {I J : Type}
    [Fintype J] (a : Matrix I J ((R.over T).obj.obj (op (topOver T)))) (t : J → Γ M) :
    ofMatrix a ≫ ofTop t = ofTop fun k => ∑ j, a k j • t j := by
  rw [ofMatrix, ofTop_comp]
  congr 1
  funext k
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ofTop_app_eb]

/-- `ofMatrix` is multiplicative: `ofMatrix a ≫ ofMatrix b = ofMatrix (a * b)`. -/
lemma ofMatrix_comp_ofMatrix {T : Opens X} {I J K : Type} [Fintype J] [Fintype K]
    (a : Matrix I J ((R.over T).obj.obj (op (topOver T))))
    (b : Matrix J K ((R.over T).obj.obj (op (topOver T)))) :
    ofMatrix a ≫ ofMatrix b = ofMatrix (a * b) := by
  have hb : ofMatrix b = ofTop fun k => ∑ j, b k j • eb j := rfl
  rw [hb, ofMatrix_comp_ofTop, ofMatrix]
  congr 1
  funext k
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- `ofMatrix` sends the identity matrix to the identity morphism. -/
lemma ofMatrix_one {T : Opens X} {I : Type} [Fintype I] [DecidableEq I] :
    ofMatrix (1 : Matrix I I ((R.over T).obj.obj (op (topOver T)))) = 𝟙 _ := by
  rw [eq_ofTop (𝟙 _), ofMatrix]
  congr 1
  funext k
  simp [Matrix.one_apply]

/-- Restriction of sections over `T` to sections over `V ≤ T`. -/
noncomputable def rΓ {V T : Opens X} (h : V ≤ T) (M : SheafOfModules.{0} (R.over T))
    (m : Γ M) : Γ ((res R h).obj M) :=
  M.val.map (toTopOver ((Over.map (homOfLE h)).obj (topOver V))).op m

/-- Restriction of functions over `T` to functions over `V ≤ T`. -/
noncomputable def rR {V T : Opens X} (h : V ≤ T)
    (a : (R.over T).obj.obj (op (topOver T))) : (R.over V).obj.obj (op (topOver V)) :=
  (R.over T).obj.map (toTopOver ((Over.map (homOfLE h)).obj (topOver V))).op a

/-- Restriction of sections is semilinear along the restriction of functions `rR`. -/
lemma rΓ_smul {V T : Opens X} (h : V ≤ T) (M : SheafOfModules.{0} (R.over T))
    (a : (R.over T).obj.obj (op (topOver T))) (m : Γ M) :
    rΓ h M (a • m) = rR h a • rΓ h M m :=
  M.val.map_smul _ a m

/-- Restriction of sections is additive. -/
lemma rΓ_add {V T : Opens X} (h : V ≤ T) (M : SheafOfModules.{0} (R.over T))
    (m m' : Γ M) : rΓ h M (m + m') = rΓ h M m + rΓ h M m' :=
  map_add _ m m'

/-- Restriction of sections commutes with morphisms of sheaves of modules. -/
lemma res_map_app_rΓ {V T : Opens X} (h : V ≤ T) {M N : SheafOfModules.{0} (R.over T)}
    (f : M ⟶ N) (m : Γ M) :
    ((res R h).map f).val.app (op (topOver V)) (rΓ h M m) = rΓ h N (f.val.app _ m) :=
  PresheafOfModules.naturality_apply f.val
    (toTopOver ((Over.map (homOfLE h)).obj (topOver V))).op m

/-- The identification `𝒪ᵖ ≅ (𝒪ᵖ)|_V`. -/
noncomputable def freeRes {V T : Opens X} (h : V ≤ T) (I : Type) :
    SheafOfModules.free (R := R.over V) I ≅ (res R h).obj (SheafOfModules.free I) :=
  haveI := preservesColimits_res R h
  SheafOfModules.mapFreeIso (res R h) I (SheafOfModules.overMapUnitIso (homOfLE h)).symm

/-- The unit section `1` of `𝒪` over `A`. -/
abbrev one1 {T : Opens X} (A : (Over T)ᵒᵖ) : (SheafOfModules.unit (R.over T)).val.obj A :=
  (show (R.over T).obj.obj A from 1)

/-- The basis section `freeSection i` over `A` is the image of `1` under `ιFree i`. -/
lemma freeSection_coe {T : Opens X} {I : Type} (i : I) (A : (Over T)ᵒᵖ) :
    (SheafOfModules.freeSection (R := R.over T) (I := I) i).1 A =
      (SheafOfModules.ιFree i).val.app A (one1 A) := by
  have hfs : (SheafOfModules.freeSection (R := R.over T) (I := I) i) =
      (SheafOfModules.free I).unitHomEquiv (SheafOfModules.ιFree i) := by
    rw [← Category.comp_id (SheafOfModules.ιFree i),
      ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
  rw [hfs]
  rfl

/-- The identification `freeRes h I` sends the basis section `eᵢ` over `V` to the restriction of
the basis section `eᵢ` over `T`. -/
lemma freeRes_hom_app_eb {V T : Opens X} (h : V ≤ T) {I : Type} (i : I) :
    (freeRes (R := R) h I).hom.val.app (op (topOver V)) (eb i) = rΓ h _ (eb i) := by
  have h1 := congrArg (fun g => g.val.app (op (topOver V)) (one1 _))
    (SheafOfModules.ιFree_mapFreeIso_hom (res R h) I
      (SheafOfModules.overMapUnitIso (R := R) (homOfLE h)).symm i)
  dsimp only at h1
  have h2 : rΓ h _ (eb (R := R) (T := T) (I := I) i) =
      (SheafOfModules.freeSection (R := R.over T) (I := I) i).1
        (op ((Over.map (homOfLE h)).obj (topOver V))) :=
    (SheafOfModules.freeSection (R := R.over T) (I := I) i).2 _
  rw [h2, freeSection_coe]
  have h3 : (eb (R := R) (T := V) (I := I) i) = (SheafOfModules.ιFree i).val.app _ (one1 _) :=
    freeSection_coe i _
  rw [h3]
  exact h1

/-- **Restriction of `ofTop`.** Restricting `ofTop t` to `V`, through `freeRes h I`, is `ofTop` of
the restricted sections `rΓ h M (t i)`. -/
lemma freeRes_hom_comp_res_map_ofTop {V T : Opens X} (h : V ≤ T)
    {M : SheafOfModules.{0} (R.over T)} {I : Type} (t : I → Γ M) :
    (freeRes h I).hom ≫ (res R h).map (ofTop t) = ofTop fun i => rΓ h M (t i) := by
  rw [eq_ofTop ((freeRes h I).hom ≫ (res R h).map (ofTop t))]
  congr 1
  funext i
  change ((res R h).map (ofTop t)).val.app _ ((freeRes h I).hom.val.app _ (eb i)) = _
  rw [freeRes_hom_app_eb, res_map_app_rΓ, ofTop_app_eb]

end Restriction

/-! ### Homeomorphism invariance -/

section Homeomorph

variable {T T' : TopCat.{0}} (f : T' ⟶ T)

/-- For a surjective open embedding `f`, the comparison map `godementSectionsPullback f F` is an
isomorphism. -/
lemma isIso_godementSectionsPullback (hf : Topology.IsOpenEmbedding f)
    (hs : Function.Surjective f) (F : TopCat.Sheaf AddCommGrpCat.{0} T) :
    IsIso (godementSectionsPullback f F) := by
  have : IsIso (((globalSections T).mapHomologicalComplex _).map
      (godementResolutionPullback f F)) := by
    have : ∀ k, IsIso ((((globalSections T).mapHomologicalComplex _).map
        (godementResolutionPullback f F)).f k) := fun k =>
      (ConcreteCategory.isIso_iff_bijective _).2
        (godementResolutionPullback_app_bijective (f := f) hf F k ⊤ (fun x _ => hs x))
    exact HomologicalComplex.Hom.isIso_of_components _
  exact ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{0}).mapIso
    (asIso (((globalSections T).mapHomologicalComplex _).map
      (godementResolutionPullback f F)))).isIso_hom

/-- For a surjective open embedding `f`, the pullback map `sheafCohomologyPullback f F n` on
sheaf cohomology is an isomorphism. -/
lemma isIso_sheafCohomologyPullback (hf : Topology.IsOpenEmbedding f)
    (hs : Function.Surjective f) (F : TopCat.Sheaf AddCommGrpCat.{0} T) (n : ℤ) :
    IsIso (sheafCohomologyPullback f F n) := by
  let K :=
    (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{0} T) (ComplexShape.up ℤ) 0).obj F
  have h1 : IsIso (godementSectionsDoubleComplexPullback f K) := by
    have : ∀ q, IsIso ((godementSectionsDoubleComplexPullback f K).f q) := fun q =>
      isIso_godementSectionsPullback f hf hs (K.X q)
    exact HomologicalComplex.Hom.isIso_of_components _
  let e := asIso (godementSectionsDoubleComplexPullback f K)
  have h2 : IsIso (HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f K)
      (ComplexShape.up ℤ)) :=
    ⟨HomologicalComplex₂.total.map e.inv (ComplexShape.up ℤ), by
      rw [← HomologicalComplex₂.total.map_comp]
      simp [e], by
      rw [← HomologicalComplex₂.total.map_comp]
      simp [e]⟩
  have h3 : IsIso (hypercohomologyPullback f K n) := by
    unfold hypercohomologyPullback
    exact (HomologicalComplex.homologyFunctor _ _ n).map_isIso _
  unfold sheafCohomologyPullback
  exact IsIso.comp_isIso' h3 (Functor.map_isIso _ _)

end Homeomorph

/-! ### Dolbeault's sheaf on a product of rectangles -/

section DolbeaultSheaf

variable {n : ℕ}

/-- A map from an open subset `A` of `U ⊆ ℂⁿ` to an open `B ⊆ ℂⁿ` which is the identity on
underlying points of `ℂⁿ` is smooth. -/
lemma contMDiff_val_val {U : Opens (EuclideanSpace ℂ (Fin n))} {A : Opens (TopCat.of U)}
    {B : Opens (EuclideanSpace ℂ (Fin n))} (θ : A → B)
    (h : ∀ x, ((θ x : B) : EuclideanSpace ℂ (Fin n)) = ((x : U) : EuclideanSpace ℂ (Fin n))) :
    ContMDiff 𝓘(ℂ, (EuclideanSpace ℂ (Fin n))) 𝓘(ℂ, (EuclideanSpace ℂ (Fin n))) ∞ θ := by
  rw [← ContMDiff.subtypeVal_comp_iff B]
  have : (Subtype.val ∘ θ : A → (EuclideanSpace ℂ (Fin n))) = Subtype.val ∘ Subtype.val := funext h
  rw [this]
  exact contMDiff_subtype_val.comp contMDiff_subtype_val

/-- A map from an open `A ⊆ ℂⁿ` to an open subset `B` of `U ⊆ ℂⁿ` which is the identity on
underlying points of `ℂⁿ` is smooth. -/
lemma contMDiff_val_val' {U : Opens (EuclideanSpace ℂ (Fin n))}
    {A : Opens (EuclideanSpace ℂ (Fin n))} {B : Opens (TopCat.of U)} (θ : A → B)
    (h : ∀ x, ((θ x : U) : (EuclideanSpace ℂ (Fin n))) = (x : (EuclideanSpace ℂ (Fin n)))) :
    ContMDiff 𝓘(ℂ, (EuclideanSpace ℂ (Fin n))) 𝓘(ℂ, (EuclideanSpace ℂ (Fin n))) ∞ θ := by
  rw [← ContMDiff.subtypeVal_comp_iff B, ← ContMDiff.subtypeVal_comp_iff U]
  have : (Subtype.val ∘ Subtype.val ∘ θ : A → (EuclideanSpace ℂ (Fin n))) = Subtype.val := funext h
  rw [this]
  exact contMDiff_subtype_val

/-- Precomposition with a diffeomorphism of open subsets of complex manifolds, as an
isomorphism of rings of holomorphic functions. -/
noncomputable def precompRingEquiv {M₁ M₂ : Type} [TopologicalSpace M₁]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M₁] [TopologicalSpace M₂]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M₂]
    {A : Opens M₁} {B : Opens M₂} (θ : A → B) (ψ : B → A)
    (hθ : ContMDiff 𝓘(ℂ, (EuclideanSpace ℂ (Fin n))) 𝓘(ℂ, (EuclideanSpace ℂ (Fin n))) ∞ θ)
    (hψ : ContMDiff 𝓘(ℂ, (EuclideanSpace ℂ (Fin n))) 𝓘(ℂ, (EuclideanSpace ℂ (Fin n))) ∞ ψ)
    (h1 : ∀ x, ψ (θ x) = x) (h2 : ∀ y, θ (ψ y) = y) :
    𝒪[n, M₂].presheaf.obj (op B) ≃+* 𝒪[n, M₁].presheaf.obj (op A) where
  toFun g := ⟨fun x => g (θ x),
    (show ContMDiff 𝓘(ℂ, (EuclideanSpace ℂ (Fin n))) 𝓘(ℂ) ∞ (g : B → ℂ) from g.2).comp hθ⟩
  invFun g := ⟨fun y => g (ψ y),
    (show ContMDiff 𝓘(ℂ, (EuclideanSpace ℂ (Fin n))) 𝓘(ℂ) ∞ (g : A → ℂ) from g.2).comp hψ⟩
  left_inv g := by
    apply ContMDiffMap.ext
    intro y
    change g (θ (ψ y)) = g y
    rw [h2]
  right_inv g := by
    apply ContMDiffMap.ext
    intro x
    change g (ψ (θ x)) = g x
    rw [h1]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The homeomorphism `P → D` onto the image `D ⊆ ℂⁿ` of an open subset `P` of `U`. -/
noncomputable def homP (U : Opens (EuclideanSpace ℂ (Fin n))) (P : Opens (TopCat.of U))
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) = Subtype.val '' (P : Set U)) :
    TopCat.of P ⟶ (Opens.toTopCat (TopCat.of (EuclideanSpace ℂ (Fin n)))).obj D :=
  TopCat.ofHom ⟨fun x => ⟨x.1.1, (show x.1.1 ∈ (D : Set _) from hD ▸ ⟨x.1, x.2, rfl⟩)⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

/-- `homP U P D hD` is the identity on underlying points of `ℂⁿ`. -/
lemma homP_apply (U : Opens (EuclideanSpace ℂ (Fin n))) (P : Opens (TopCat.of U))
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) = Subtype.val '' (P : Set U)) (x : P) :
    (homP U P D hD x).1 = ((x : U) : (EuclideanSpace ℂ (Fin n))) := rfl

/-- `homP U P D hD` is an open embedding. -/
lemma isOpenEmbedding_homP (U : Opens (EuclideanSpace ℂ (Fin n))) (P : Opens (TopCat.of U))
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) = Subtype.val '' (P : Set U)) :
    Topology.IsOpenEmbedding (homP U P D hD) :=
  .of_comp _ D.isOpenEmbedding' (U.isOpenEmbedding'.comp P.isOpenEmbedding')

/-- The holomorphic functions on `P`, read on `D`. -/
noncomputable def dolbeaultSheafIso (U : Opens (EuclideanSpace ℂ (Fin n))) (P : Opens (TopCat.of U))
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) = Subtype.val '' (P : Set U)) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (homP U P D hD)).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0}
        (Opens.inclusion' (X := TopCat.of (EuclideanSpace ℂ (Fin n))) D)).obj
        ((SheafOfModules.toSheaf _).obj
          (SheafOfModules.unit (holomorphicRingCatSheaf n (EuclideanSpace ℂ (Fin n)))))) ≅
      ((Opens.sheafEquivOver P).functor).obj ((SheafOfModules.toSheaf _).obj
        (SheafOfModules.unit ((holomorphicRingCatSheaf n U).over P))) := by
  let hh := isOpenEmbedding_homP U P D hD
  let hi := Opens.isOpenEmbedding (X := TopCat.of (EuclideanSpace ℂ (Fin n))) D
  refine ((hh.sheafPullbackIso AddCommGrpCat.{0}).app _) ≪≫
    (hh.sheafPullback AddCommGrpCat.{0}).mapIso
      ((hi.sheafPullbackIso AddCommGrpCat.{0}).app _) ≪≫ ?_
  refine (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents (fun V => ?_) ?_)
  · let Y := ((Opens.overEquivalence P).inverse.obj V.unop).left
    let Y' := hi.functor.obj (hh.functor.obj V.unop)
    have memY : ∀ y : Y, ((y : U) : EuclideanSpace ℂ (Fin n)) ∈ Y' := by
      rintro ⟨y, p, hp, rfl⟩
      exact ⟨homP U P D hD p, ⟨p, hp, rfl⟩, rfl⟩
    have memU : ∀ x : Y', (x : EuclideanSpace ℂ (Fin n)) ∈ U := by
      rintro ⟨x, d, ⟨p, hp, rfl⟩, rfl⟩
      exact p.1.2
    have memY' : ∀ x : Y', (⟨x.1, memU x⟩ : U) ∈ Y := by
      rintro ⟨x, d, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
    exact (precompRingEquiv (M₁ := U) (M₂ := EuclideanSpace ℂ (Fin n)) (A := Y) (B := Y')
      (fun y => ⟨y.1.1, memY y⟩) (fun x => ⟨⟨x.1, memU x⟩, memY' x⟩)
      (contMDiff_val_val _ fun _ => rfl) (contMDiff_val_val' _ fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl)).toAddEquiv.toAddCommGrpIso
  · intro X Y f
    ext g
    apply ContMDiffMap.ext
    intro y
    rfl

end DolbeaultSheaf

/-! ### Cohomology of restrictions to open subsets -/

section Psi

variable {X : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

/-- The underlying abelian sheaf on `P` of the restriction to `P ≤ W` of a sheaf of modules on
`Over W`. -/
noncomputable abbrev Ψ {P W : Opens X} (h : P ≤ W) :
    SheafOfModules.{0} (R.over W) ⥤ Sheaf (Opens.grothendieckTopology P) AddCommGrpCat.{0} :=
  res R h ⋙ SheafOfModules.toSheaf _ ⋙ (Opens.sheafEquivOver P).functor

/-- `Ψ h` preserves finite limits. -/
lemma preservesFiniteLimits_Ψ {P W : Opens X} (h : P ≤ W) :
    PreservesFiniteLimits (Ψ (R := R) h) := by
  have := preservesFiniteLimits_res R h
  exact comp_preservesFiniteLimits _ _

/-- `Ψ h` preserves finite colimits. -/
lemma preservesFiniteColimits_Ψ {P W : Opens X} (h : P ≤ W) :
    PreservesFiniteColimits (Ψ (R := R) h) := by
  have := preservesColimits_res R h
  have := preservesFiniteColimits_toSheaf (R.over P)
  exact comp_preservesFiniteColimits _ _

/-- `Ψ h` is additive. -/
lemma additive_Ψ {P W : Opens X} (h : P ≤ W) : (Ψ (R := R) h).Additive := by
  have := preservesFiniteLimits_Ψ (R := R) h
  have : PreservesBinaryBiproducts (Ψ (R := R) h) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- `Ψ h` preserves exactness of a chain complex in each degree. -/
lemma exactAt_map_Ψ {P W : Opens X} (h : P ≤ W)
    (C : ChainComplex (SheafOfModules.{0} (R.over W)) ℕ) (i : ℕ) (hC : C.ExactAt i) :
    (((Ψ (R := R) h).mapHomologicalComplex _).obj C).ExactAt i := by
  have := preservesFiniteLimits_Ψ (R := R) h
  have := preservesFiniteColimits_Ψ (R := R) h
  have := additive_Ψ (R := R) h
  exact (show (C.sc i).Exact from hC).map (Ψ h)

/-- `Ext` vanishing is invariant under isomorphism of the target. -/
lemma subsingleton_ext_of_iso {C : Type*} [Category C] [Abelian C] [HasExt C]
    {Z Y Y' : C} (e : Y ≅ Y') {q : ℕ} (h : Subsingleton (Abelian.Ext Z Y q)) :
    Subsingleton (Abelian.Ext Z Y' q) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have : x = (x.comp (Abelian.Ext.mk₀ e.inv) (add_zero q)).comp (Abelian.Ext.mk₀ e.hom)
      (add_zero q) := by
    rw [Abelian.Ext.comp_assoc _ _ _ (add_zero q) (add_zero 0) (by simp),
      Abelian.Ext.mk₀_comp_mk₀, e.inv_hom_id, Abelian.Ext.comp_mk₀_id]
  rw [this, Subsingleton.elim (x.comp (Abelian.Ext.mk₀ e.inv) (add_zero q)) 0,
    Abelian.Ext.zero_comp]

/-- A finite free resolution of length `≤ ℓ`. -/
def HasFFR {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [HasSheafify J AddCommGrpCat.{0}]
    (M : SheafOfModules.{0} R) (ℓ : ℕ) : Prop :=
  ∃ (K : ChainComplex (SheafOfModules.{0} R) ℕ) (ε : K.X 0 ⟶ M),
    (∀ i, ∃ r : ℕ, Nonempty (K.X i ≅ SheafOfModules.free (Fin r))) ∧
    (∀ i, ℓ < i → IsZero (K.X i)) ∧ (∀ i, 0 < i → K.ExactAt i) ∧ Epi ε ∧
    ∃ h : K.d 1 0 ≫ ε = 0, (ShortComplex.mk _ _ h).Exact

section ExactFunctor

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasSheafify J AddCommGrpCat.{0}]
  {D : Type*} [Category D] [Abelian D] [HasExt D]
  (G : SheafOfModules.{0} R ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- An additive functor carries `Ext` vanishing on `𝒪` to `Ext` vanishing on `𝒪ʳ`. -/
lemma subsingleton_ext_map_free (Z : D) (r q : ℕ)
    (h : Subsingleton (Abelian.Ext Z (G.obj (SheafOfModules.unit R)) q)) :
    Subsingleton (Abelian.Ext Z (G.obj (SheafOfModules.free (Fin r))) q) := by
  refine subsingleton_ext_of_sum_comp_eq_id Finset.univ
    (fun k => G.map (MMP.freeProj k)) (fun k => G.map (SheafOfModules.ιFree k)) ?_ q h
  have : ∀ k : Fin r, G.map (MMP.freeProj (R := R) k) ≫ G.map (SheafOfModules.ιFree k) =
      G.map (MMP.freeProj k ≫ SheafOfModules.ιFree k) := fun k => (G.map_comp _ _).symm
  rw [Finset.sum_congr rfl (fun k _ => this k), ← G.map_sum, MMP.sum_freeProj_ιFree, G.map_id]

/-- **Dimension shifting along an exact functor.** If `Ext^q(Z, G 𝒪) = 0` for `q ≥ 1`, then for a
finite free resolution `K → M`, `Ext^q(Z, G -)` vanishes for `q ≥ 1` on `M` and on the kernel of
the augmentation. -/
lemma subsingleton_ext_map_of_resolution (Z : D)
    (hunit : ∀ q, 1 ≤ q → Subsingleton (Abelian.Ext Z (G.obj (SheafOfModules.unit R)) q))
    {M : SheafOfModules.{0} R} {ℓ : ℕ} (K : ChainComplex (SheafOfModules.{0} R) ℕ)
    (ε : K.X 0 ⟶ M) (hfree : ∀ i, ∃ r : ℕ, Nonempty (K.X i ≅ SheafOfModules.free (Fin r)))
    (hzero : ∀ i, ℓ < i → IsZero (K.X i)) (hexact : ∀ i, 0 < i → K.ExactAt i) (hε : Epi ε)
    (h0 : K.d 1 0 ≫ ε = 0) (hex : (ShortComplex.mk _ _ h0).Exact) :
    (∀ q, 1 ≤ q → Subsingleton (Abelian.Ext Z (G.obj (kernel ε)) q)) ∧
    ∀ q, 1 ≤ q → Subsingleton (Abelian.Ext Z (G.obj M) q) := by
  have h0' : ((G.mapHomologicalComplex _).obj K).d 1 0 ≫ G.map ε = 0 := by
    change G.map (K.d 1 0) ≫ G.map ε = 0
    rw [← G.map_comp, h0, G.map_zero]
  obtain ⟨hk, hM⟩ := subsingleton_ext_of_resolution Z ℓ
    ((G.mapHomologicalComplex _).obj K) (G.map ε)
    (fun i q hq => by
      obtain ⟨r, ⟨e⟩⟩ := hfree i
      exact subsingleton_ext_of_iso (G.mapIso e).symm
        (subsingleton_ext_map_free G Z r q (hunit q hq)))
    (fun i hi => G.map_isZero (hzero i hi))
    (fun i hi => (show (K.sc i).Exact from hexact i hi).map G)
    inferInstance h0' (hex.map G)
  exact ⟨fun q hq => subsingleton_ext_of_iso (PreservesKernel.iso G ε).symm (hk q hq), hM⟩

end ExactFunctor

section Lifting

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasSheafify J AddCommGrpCat.{0}]

/-- **Lifting global sections.** If `Ext¹(ℤ, G(ker ε)) = 0`, every global section of `G M` lifts
through `G ε`. -/
lemma exists_lift_of_subsingleton_ext {X' : TopCat.{0}}
    (G : SheafOfModules.{0} R ⥤ Sheaf (Opens.grothendieckTopology X') AddCommGrpCat.{0})
    [HasExt (Sheaf (Opens.grothendieckTopology X') AddCommGrpCat.{0})] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {A M : SheafOfModules.{0} R} (ε : A ⟶ M) [Epi ε]
    (hk : Subsingleton (Abelian.Ext (freeYonedaTop X') (G.obj (kernel ε)) 1)) :
    ∀ m : (G.obj M).obj.obj (op ⊤), ∃ y : (G.obj A).obj.obj (op ⊤),
      (G.map ε).hom.app (op ⊤) y = m := by
  intro m
  have hS := (shortExact_kernel ε).map_of_exact G
  let e := fun Y => freeYonedaTopHomEquiv (X := X') Y
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ (freeYonedaTop X') hS
    (Abelian.Ext.mk₀ ((e _).symm m)) (n₁ := 1) rfl (by
      have : Subsingleton (Abelian.Ext (freeYonedaTop X')
          ((ShortComplex.mk (kernel.ι ε) ε (kernel.condition ε)).map G).X₁ 1) := hk
      exact Subsingleton.elim _ _)
  obtain ⟨f₂, rfl⟩ := (Abelian.Ext.mk₀_bijective (freeYonedaTop X') (G.obj A)).2 x₂
  rw [Abelian.Ext.mk₀_comp_mk₀] at hx₂
  have hf := (Abelian.Ext.mk₀_bijective _ _).1 hx₂
  refine ⟨e _ f₂, ?_⟩
  have := freeYonedaTopHomEquiv_comp f₂ (G.map ε)
  change _ = m
  rw [← this]
  have hf' : f₂ ≫ G.map ε = (e _).symm m := hf
  change e _ (f₂ ≫ G.map ε) = m
  rw [hf', Equiv.apply_symm_apply]

end Lifting

end Psi

/-! ### Finite free resolutions -/

section FFR

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasSheafify J AddCommGrpCat.{0}]

/-- A finite free resolution of length `≤ ℓ` has length `≤ ℓ'` for every `ℓ' ≥ ℓ`. -/
lemma HasFFR.mono {M : SheafOfModules.{0} R} {ℓ ℓ' : ℕ} (h : HasFFR M ℓ) (hℓ : ℓ ≤ ℓ') :
    HasFFR M ℓ' := by
  obtain ⟨K, ε, h1, h2, h3, h4, h5⟩ := h
  exact ⟨K, ε, h1, fun i hi => h2 i (by omega), h3, h4, h5⟩

/-- Having a finite free resolution of length `≤ ℓ` is invariant under isomorphism. -/
lemma HasFFR.of_iso {M M' : SheafOfModules.{0} R} {ℓ : ℕ} (h : HasFFR M ℓ) (e : M ≅ M') :
    HasFFR M' ℓ := by
  obtain ⟨K, ε, h1, h2, h3, h4, h0, hex⟩ := h
  refine ⟨K, ε ≫ e.hom, h1, h2, h3, epi_comp _ _, by rw [reassoc_of% h0, zero_comp], ?_⟩
  refine ShortComplex.exact_of_iso ?_ hex
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by simp)

/-- The free sheaf of modules of rank `0` is zero. -/
lemma isZero_free_fin_zero : IsZero (SheafOfModules.free (R := R) (Fin 0)) :=
  (IsZero.iff_id_eq_zero _).2 ((SheafOfModules.free (Fin 0)).freeHomEquiv.injective
    (Subsingleton.elim _ _))

/-- A module isomorphic to a free module of finite rank has a resolution of length `0`. -/
lemma hasFFR_zero_of_iso {M : SheafOfModules.{0} R} {r : ℕ}
    (e : SheafOfModules.free (Fin r) ≅ M) : HasFFR M 0 := by
  let K := (ChainComplex.single₀ (SheafOfModules.{0} R)).obj (SheafOfModules.free (Fin r))
  have hz : ∀ i, 0 < i → IsZero (K.X i) := fun i hi =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  refine ⟨K, (HomologicalComplex.singleObjXSelf _ 0 _).hom ≫ e.hom, fun i => ?_,
    fun i hi => hz i hi, fun i hi => ?_, epi_comp _ _, ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact ⟨r, ⟨HomologicalComplex.singleObjXSelf _ 0 _⟩⟩
    · exact ⟨0, ⟨(hz i hi).iso isZero_free_fin_zero⟩⟩
  · exact (K.exactAt_iff _).2 (ShortComplex.exact_of_isZero_X₂ _ (hz i hi))
  · have h0 : K.d 1 0 = 0 := (hz 1 Nat.zero_lt_one).eq_of_src _ _
    refine ⟨by rw [h0, zero_comp], ?_⟩
    rw [ShortComplex.exact_iff_mono _ h0]
    exact mono_comp _ _

/-- The augmentation of a resolution of length `0` is an isomorphism. -/
lemma isIso_of_hasFFR_zero {M : SheafOfModules.{0} R}
    (K : ChainComplex (SheafOfModules.{0} R) ℕ) (ε : K.X 0 ⟶ M)
    (hzero : ∀ i, 0 < i → IsZero (K.X i)) (hε : Epi ε) (h0 : K.d 1 0 ≫ ε = 0)
    (hex : (ShortComplex.mk _ _ h0).Exact) : IsIso ε := by
  have hd : K.d 1 0 = 0 := (hzero 1 Nat.zero_lt_one).eq_of_src _ _
  have : Mono ε := (ShortComplex.exact_iff_mono _ hd).1 hex
  exact isIso_of_mono_of_epi ε

/-- **Truncation.** The kernel of the augmentation of a resolution of length `≤ ℓ + 1` has a
resolution of length `≤ ℓ`. -/
lemma hasFFR_kernel {M : SheafOfModules.{0} R} {ℓ : ℕ}
    (K : ChainComplex (SheafOfModules.{0} R) ℕ) (ε : K.X 0 ⟶ M)
    (hfree : ∀ i, ∃ r : ℕ, Nonempty (K.X i ≅ SheafOfModules.free (Fin r)))
    (hzero : ∀ i, ℓ + 1 < i → IsZero (K.X i)) (hexact : ∀ i, 0 < i → K.ExactAt i) (hε : Epi ε)
    (h : K.d 1 0 ≫ ε = 0) (hex : (ShortComplex.mk _ _ h).Exact) : HasFFR (kernel ε) ℓ := by
  obtain ⟨hε', hexact', h', hex'⟩ := truncate_resolution K ε hexact h hex
  exact ⟨_, _, fun i => hfree (i + 1), fun i hi => hzero (i + 1) (by omega), hexact', hε', h',
    hex'⟩

/-- **Splicing.** If `φ : F ⟶ N` is an epimorphism from a free module of finite rank whose
kernel has a resolution of length `≤ ℓ`, then `N` has a resolution of length `≤ ℓ + 1`. -/
lemma hasFFR_of_epi {F N : SheafOfModules.{0} R} {p : ℕ}
    (eF : F ≅ SheafOfModules.free (Fin p)) (φ : F ⟶ N) [hφ : Epi φ] {ℓ : ℕ}
    (hk : HasFFR (kernel φ) ℓ) : HasFFR N (ℓ + 1) := by
  obtain ⟨K, ε, hfree, hzero, hexact, hε, h0, hex⟩ := hk
  have w : K.d 1 0 ≫ (ε ≫ kernel.ι φ) = 0 := by rw [reassoc_of% h0, zero_comp]
  let K' := K.augment (ε ≫ kernel.ι φ) w
  have h' : K'.d 1 0 ≫ φ = 0 := by
    change (ε ≫ kernel.ι φ) ≫ φ = 0
    rw [Category.assoc, kernel.condition, comp_zero]
  refine ⟨K', φ, fun i => ?_, fun i hi => ?_, fun i hi => ?_, hφ, h', ?_⟩
  · rcases i with _ | i
    · exact ⟨p, ⟨eF⟩⟩
    · exact hfree i
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact hzero j (by omega)
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [HomologicalComplex.exactAt_iff' _ (j + 2) (j + 1) j (by simp) (by simp)]
    rcases j with _ | j
    · change (ShortComplex.mk (K.d 1 0) (ε ≫ kernel.ι φ) w).Exact
      let ψ : ShortComplex.mk _ _ h0 ⟶ ShortComplex.mk (K.d 1 0) (ε ≫ kernel.ι φ) w :=
        { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι φ
          comm₁₂ := by simp
          comm₂₃ := by simp }
      haveI : Epi ψ.τ₁ := inferInstanceAs (Epi (𝟙 _))
      haveI : IsIso ψ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
      haveI : Mono ψ.τ₃ := inferInstanceAs (Mono (kernel.ι φ))
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).1 hex
    · exact (K.exactAt_iff' (j + 2) (j + 1) j (by simp) (by simp)).1 (hexact (j + 1) (by omega))
  · change (ShortComplex.mk (ε ≫ kernel.ι φ) φ h').Exact
    let ψ : ShortComplex.mk (ε ≫ kernel.ι φ) φ h' ⟶
        ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ) :=
      { τ₁ := ε, τ₂ := 𝟙 _, τ₃ := 𝟙 _
        comm₁₂ := by simp
        comm₂₃ := by simp }
    haveI : Epi ψ.τ₁ := hε
    haveI : IsIso ψ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    haveI : Mono ψ.τ₃ := inferInstanceAs (Mono (𝟙 _))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ))

section Biprod

variable {D : Type*} [Category D] [Abelian D]

/-- The kernel of `f ⊞ 𝟙 : A ⊞ B ⟶ N ⊞ B` is the kernel of `f`. -/
noncomputable def kernelBiprodMapIdIso {A B N : D} (f : A ⟶ N) :
    kernel (biprod.map f (𝟙 B)) ≅ kernel f := by
  refine (IsLimit.conePointUniqueUpToIso (kernelIsKernel (biprod.map f (𝟙 B)))
    (KernelFork.IsLimit.ofι (kernel.ι f ≫ biprod.inl) (by simp)
      (fun g hg => kernel.lift f (g ≫ biprod.fst) ?_) (fun g hg => ?_) (fun g hg m hm => ?_)))
  · have := hg =≫ biprod.fst
    simpa using this
  · have h2 : g ≫ biprod.snd = 0 := by simpa using hg =≫ biprod.snd
    ext
    · simp
    · simp [h2]
  · apply (cancel_mono (kernel.ι f)).1
    simp [← hm]

/-- The kernel of `(φ, 0) : A ⊞ B ⟶ N` is `ker φ ⊞ B`. -/
noncomputable def kernelBiprodDescZeroIso {A B N : D} (φ : A ⟶ N) :
    kernel (biprod.desc φ (0 : B ⟶ N)) ≅ kernel φ ⊞ B := by
  refine (IsLimit.conePointUniqueUpToIso (kernelIsKernel (biprod.desc φ (0 : B ⟶ N)))
    (KernelFork.IsLimit.ofι (biprod.map (kernel.ι φ) (𝟙 B)) (by ext <;> simp)
      (fun g hg => biprod.lift (kernel.lift φ (g ≫ biprod.fst) ?_) (g ≫ biprod.snd))
      (fun g hg => ?_) (fun g hg m hm => ?_)))
  · have : g ≫ biprod.desc φ (0 : B ⟶ N) = (g ≫ biprod.fst) ≫ φ := by
      rw [biprod.desc_eq]
      simp
    rw [← this, hg]
  · ext <;> simp
  · ext
    · simp [← hm]
    · simp [← hm]

/-- The kernel of `(0, φ) : A ⊞ B ⟶ N` is `A ⊞ ker φ`. -/
noncomputable def kernelBiprodDescZeroIso' {A B N : D} (φ : B ⟶ N) :
    kernel (biprod.desc (0 : A ⟶ N) φ) ≅ A ⊞ kernel φ := by
  refine (IsLimit.conePointUniqueUpToIso (kernelIsKernel (biprod.desc (0 : A ⟶ N) φ))
    (KernelFork.IsLimit.ofι (biprod.map (𝟙 A) (kernel.ι φ)) (by ext <;> simp)
      (fun g hg => biprod.lift (g ≫ biprod.fst) (kernel.lift φ (g ≫ biprod.snd) ?_))
      (fun g hg => ?_) (fun g hg m hm => ?_)))
  · have : g ≫ biprod.desc (0 : A ⟶ N) φ = (g ≫ biprod.snd) ≫ φ := by
      rw [biprod.desc_eq]
      simp
    rw [← this, hg]
  · ext <;> simp
  · ext
    · simp [← hm]
    · simp [← hm]

end Biprod

/-- `𝒪^{(I ⊕ J)} ≅ 𝒪^{(I)} ⊞ 𝒪^{(J)}`. -/
noncomputable def freeSumIso (I I' : Type) :
    SheafOfModules.free (R := R) (I ⊕ I') ≅ SheafOfModules.free I ⊞ SheafOfModules.free I' where
  hom := (SheafOfModules.free I ⊞ SheafOfModules.free I').freeHomEquiv.symm
    (Sum.elim (fun i => SheafOfModules.sectionsMap biprod.inl (SheafOfModules.freeSection i))
      (fun j => SheafOfModules.sectionsMap biprod.inr (SheafOfModules.freeSection j)))
  inv := biprod.desc (SheafOfModules.freeMap Sum.inl) (SheafOfModules.freeMap Sum.inr)
  hom_inv_id := by
    apply (SheafOfModules.free (I ⊕ I')).freeHomEquiv.injective
    funext x
    rw [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply]
    rcases x with i | j
    · change SheafOfModules.sectionsMap (biprod.inl ≫ _) (SheafOfModules.freeSection i) = _
      rw [biprod.inl_desc, SheafOfModules.sectionMap_freeMap_freeSection]
    · change SheafOfModules.sectionsMap (biprod.inr ≫ _) (SheafOfModules.freeSection j) = _
      rw [biprod.inr_desc, SheafOfModules.sectionMap_freeMap_freeSection]
  inv_hom_id := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      apply (SheafOfModules.free I ⊞ SheafOfModules.free I').freeHomEquiv.injective
      funext i
      rw [SheafOfModules.freeHomEquiv_comp_apply, SheafOfModules.freeHomEquiv_freeMap]
      change SheafOfModules.sectionsMap _ (SheafOfModules.freeSection (Sum.inl i)) = _
      rw [← SheafOfModules.freeHomEquiv_apply, Equiv.apply_symm_apply,
        SheafOfModules.freeHomEquiv_apply]
      rfl
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      apply (SheafOfModules.free I ⊞ SheafOfModules.free I').freeHomEquiv.injective
      funext i
      rw [SheafOfModules.freeHomEquiv_comp_apply, SheafOfModules.freeHomEquiv_freeMap]
      change SheafOfModules.sectionsMap _ (SheafOfModules.freeSection (Sum.inr i)) = _
      rw [← SheafOfModules.freeHomEquiv_apply, Equiv.apply_symm_apply,
        SheafOfModules.freeHomEquiv_apply]
      rfl

/-- `𝒪^{(I)} ≅ 𝒪^{(I')}` for `I ≃ I'`. -/
noncomputable def freeCongrIso {I I' : Type} (e : I ≃ I') :
    SheafOfModules.free (R := R) I ≅ SheafOfModules.free I' :=
  SheafOfModules.freeFunctor.mapIso e.toIso

/-- `𝒪ʳ ⊞ 𝒪^q ≅ 𝒪^{r + q}`. -/
noncomputable def freeBiprodIso (r q : ℕ) :
    SheafOfModules.free (R := R) (Fin r) ⊞ SheafOfModules.free (Fin q) ≅
      SheafOfModules.free (Fin (r + q)) :=
  (freeSumIso (Fin r) (Fin q)).symm ≪≫ freeCongrIso finSumFinEquiv

/-- Adding a free summand of finite rank keeps a resolution of length `≤ ℓ`. -/
lemma hasFFR_biprod_free (ℓ : ℕ) : ∀ (A : SheafOfModules.{0} R), HasFFR A ℓ →
    ∀ q : ℕ, HasFFR (A ⊞ SheafOfModules.free (Fin q)) ℓ := by
  induction ℓ with
  | zero =>
    intro A hA q
    obtain ⟨K, ε, hfree, hzero, -, hε, h0, hex⟩ := hA
    have := isIso_of_hasFFR_zero K ε hzero hε h0 hex
    obtain ⟨r, ⟨e⟩⟩ := hfree 0
    exact hasFFR_zero_of_iso ((freeBiprodIso r q).symm ≪≫ biprod.mapIso (e.symm ≪≫ asIso ε)
      (Iso.refl _))
  | succ ℓ ih =>
    intro A hA q
    obtain ⟨K, ε, hfree, hzero, hexact, hε, h0, hex⟩ := hA
    have hk := hasFFR_kernel K ε hfree hzero hexact hε h0 hex
    obtain ⟨r, ⟨e⟩⟩ := hfree 0
    have : Epi (biprod.map ε (𝟙 (SheafOfModules.free (R := R) (Fin q)))) := inferInstance
    exact hasFFR_of_epi (biprod.mapIso e (Iso.refl _) ≪≫ freeBiprodIso r q)
      (biprod.map ε (𝟙 _)) (hk.of_iso (kernelBiprodMapIdIso ε).symm)

/-- Exact functors preserving free modules of finite rank preserve finite free resolutions. -/
lemma HasFFR.map {C' : Type*} [Category C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{0}} [HasWeakSheafify J' AddCommGrpCat.{0}]
    [J'.WEqualsLocallyBijective AddCommGrpCat.{0}] [HasSheafify J' AddCommGrpCat.{0}]
    (G : SheafOfModules.{0} R ⥤ SheafOfModules.{0} R') [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G]
    (hG : ∀ r : ℕ, Nonempty (G.obj (SheafOfModules.free (Fin r)) ≅ SheafOfModules.free (Fin r)))
    {M : SheafOfModules.{0} R} {ℓ : ℕ} (h : HasFFR M ℓ) : HasFFR (G.obj M) ℓ := by
  obtain ⟨K, ε, hfree, hzero, hexact, hε, h0, hex⟩ := h
  have h0' : ((G.mapHomologicalComplex _).obj K).d 1 0 ≫ G.map ε = 0 := by
    change G.map (K.d 1 0) ≫ G.map ε = 0
    rw [← G.map_comp, h0, G.map_zero]
  refine ⟨(G.mapHomologicalComplex _).obj K, G.map ε, fun i => ?_, fun i hi => G.map_isZero
    (hzero i hi), fun i hi => (show (K.sc i).Exact from hexact i hi).map G, inferInstance, h0',
    hex.map G⟩
  obtain ⟨r, ⟨e⟩⟩ := hfree i
  obtain ⟨e'⟩ := hG r
  exact ⟨r, ⟨G.mapIso e ≪≫ e'⟩⟩

/-- Adding a free summand of finite rank on the left keeps a resolution of length `≤ ℓ`. -/
lemma hasFFR_free_biprod (ℓ : ℕ) (A : SheafOfModules.{0} R) (hA : HasFFR A ℓ) (q : ℕ) :
    HasFFR (SheafOfModules.free (Fin q) ⊞ A) ℓ :=
  (hasFFR_biprod_free ℓ A hA q).of_iso (biprod.braiding _ _)

end FFR

/-! ### Local properties on a cover by two opens -/

section OverLocal

variable {X : TopCat.{0}}

/-- The sheaf condition on `Over T` for a family of arrows covering `A`. -/
lemma over_isSheafFor {T : Opens X}
    (F : Sheaf ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{0})
    (A : Over T) {ι : Type} (Y : ι → Over T) (f : ∀ i, Y i ⟶ A)
    (hcov : ∀ x ∈ A.left, ∃ i, x ∈ (Y i).left) :
    Presieve.IsSheafFor (F.obj ⋙ forget AddCommGrpCat) (Presieve.ofArrows Y f) := by
  have hF := (Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget AddCommGrpCat)).1 F.property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  rw [Presieve.isSheafFor_iff_generate]
  apply hF
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨i, hi⟩ := hcov x hx
  refine ⟨(Y i).left, (f i).left, ?_, hi⟩
  rw [Sieve.overEquiv_iff]
  refine ⟨Y i, Over.homMk (𝟙 _) (Subsingleton.elim _ _), f i, Presieve.ofArrows.mk i,
    over_hom_ext _ _⟩

/-- Sections of a sheaf on `Over T` agreeing on a cover of `A` agree. -/
lemma over_ext {T : Opens X} (F : Sheaf ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{0})
    (A : Over T) {ι : Type} (Y : ι → Over T) (f : ∀ i, Y i ⟶ A)
    (hcov : ∀ x ∈ A.left, ∃ i, x ∈ (Y i).left) (s t : F.obj.obj (op A))
    (h : ∀ i, F.obj.map (f i).op s = F.obj.map (f i).op t) : s = t :=
  (over_isSheafFor F A Y f hcov).isSeparatedFor.ext fun _ _ hg => by
    obtain ⟨i⟩ := hg
    exact h i

/-- Gluing of two sections of a sheaf on `Over T`, over opens `B₁, B₂` covering `A`, which
agree on `B₁ ⊓ B₂`. -/
lemma over_glue {T : Opens X} (F : Sheaf ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{0})
    (A B₁ B₂ B₁₂ : Over T) (f₁ : B₁ ⟶ A) (f₂ : B₂ ⟶ A) (g₁ : B₁₂ ⟶ B₁) (g₂ : B₁₂ ⟶ B₂)
    (hcov : A.left ≤ B₁.left ⊔ B₂.left) (hint : B₁.left ⊓ B₂.left ≤ B₁₂.left)
    (s₁ : F.obj.obj (op B₁)) (s₂ : F.obj.obj (op B₂))
    (hs : F.obj.map g₁.op s₁ = F.obj.map g₂.op s₂) :
    ∃ s : F.obj.obj (op A), F.obj.map f₁.op s = s₁ ∧ F.obj.map f₂.op s = s₂ := by
  let Y : Bool → Over T := fun b => if b then B₁ else B₂
  let f : ∀ b, Y b ⟶ A := fun b => match b with
    | true => f₁
    | false => f₂
  have hsh := over_isSheafFor F A Y f (fun x hx => by
    rcases hcov hx with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩)
  let x : ∀ b, (F.obj ⋙ forget AddCommGrpCat).obj (op (Y b)) := fun b => match b with
    | true => s₁
    | false => s₂
  have hc : Presieve.Arrows.Compatible (F.obj ⋙ forget AddCommGrpCat) f x := by
    have key : ∀ (Z : Over T) (a : Z ⟶ B₁) (b : Z ⟶ B₂),
        F.obj.map a.op s₁ = F.obj.map b.op s₂ := by
      intro Z a b
      have hZ : Z.left ≤ B₁₂.left := fun z hz => hint ⟨a.left.le hz, b.left.le hz⟩
      let k : Z ⟶ B₁₂ := Over.homMk (homOfLE hZ) (Subsingleton.elim _ _)
      rw [over_hom_ext a (k ≫ g₁), over_hom_ext b (k ≫ g₂), op_comp, op_comp,
        Functor.map_comp, Functor.map_comp]
      change F.obj.map k.op (F.obj.map g₁.op s₁) = F.obj.map k.op (F.obj.map g₂.op s₂)
      rw [hs]
    intro i j Z gi gj _
    rcases i with _ | _ <;> rcases j with _ | _
    · change F.obj.map gi.op s₂ = F.obj.map gj.op s₂
      rw [over_hom_ext gi gj]
    · exact (key Z gj gi).symm
    · exact key Z gi gj
    · change F.obj.map gi.op s₁ = F.obj.map gj.op s₁
      rw [over_hom_ext gi gj]
  obtain ⟨s, hs', -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsh x hc
  exact ⟨s, hs' true, hs' false⟩

variable {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

/-- A sheaf of modules on `Over T` all of whose modules of sections are trivial is zero. -/
lemma isZero_of_forall_subsingleton {T : Opens X} (Z : SheafOfModules.{0} (R.over T))
    (h : ∀ A : Over T, Subsingleton (Z.val.obj (op A))) : IsZero Z := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  ext A z
  exact Subsingleton.elim _ _

/-- Every module of sections of a zero sheaf of modules is trivial. -/
lemma subsingleton_of_isZero {T : Opens X} {Z : SheafOfModules.{0} (R.over T)}
    (hZ : IsZero Z) (A : Over T) : Subsingleton (Z.val.obj (op A)) :=
  ModuleCat.isZero_iff_subsingleton.1 ((SheafOfModules.evaluation _ (op A)).map_isZero hZ)

/-- The open `A ⊓ T₁` of `T`, for `A : Over T` and `T₁ ≤ T`, as an object over `T₁`. -/
abbrev interOver {T T₁ : Opens X} (A : Over T) : Over T₁ :=
  Over.mk (homOfLE (inf_le_right : A.left ⊓ T₁ ≤ T₁))

/-- The inclusion of `A ⊓ T₁`, viewed as an object over `T`, into `A`. -/
abbrev interToOver {T T₁ : Opens X} (h₁ : T₁ ≤ T) (A : Over T) :
    (Over.map (homOfLE h₁)).obj (interOver (T₁ := T₁) A) ⟶ A :=
  Over.homMk (homOfLE inf_le_left) (Subsingleton.elim _ _)

/-- **Vanishing is local.** A sheaf of modules on `Over T` vanishing on `T₁` and on `T₂`, where
`T = T₁ ∪ T₂`, vanishes. -/
lemma isZero_of_isZero_res {T T₁ T₂ : Opens X} (h₁ : T₁ ≤ T) (h₂ : T₂ ≤ T)
    (hcov : T ≤ T₁ ⊔ T₂) (Z : SheafOfModules.{0} (R.over T))
    (hz₁ : IsZero ((res R h₁).obj Z)) (hz₂ : IsZero ((res R h₂).obj Z)) : IsZero Z := by
  refine isZero_of_forall_subsingleton Z fun A => ⟨fun s t => ?_⟩
  let Y : Bool → Over T := fun b => if b then (Over.map (homOfLE h₁)).obj (interOver A)
    else (Over.map (homOfLE h₂)).obj (interOver A)
  let f : ∀ b, Y b ⟶ A := fun b => match b with
    | true => interToOver h₁ A
    | false => interToOver h₂ A
  refine over_ext ((SheafOfModules.toSheaf _).obj Z) A Y f (fun x hx => ?_) s t fun b => ?_
  · rcases hcov (A.hom.le hx) with h | h
    · exact ⟨true, ⟨hx, h⟩⟩
    · exact ⟨false, ⟨hx, h⟩⟩
  · rcases b with _ | _
    · exact (subsingleton_of_isZero hz₂ (interOver A)).elim _ _
    · exact (subsingleton_of_isZero hz₁ (interOver A)).elim _ _

/-- **Surjectivity is local.** A morphism of sheaves of modules on `Over T` whose restrictions to
`T₁` and `T₂` are epimorphisms, where `T ≤ T₁ ⊔ T₂`, is an epimorphism. -/
lemma epi_of_epi_res {T T₁ T₂ : Opens X} (h₁ : T₁ ≤ T) (h₂ : T₂ ≤ T)
    (hcov : T ≤ T₁ ⊔ T₂) {M N : SheafOfModules.{0} (R.over T)} (f : M ⟶ N)
    (hf₁ : Epi ((res R h₁).map f)) (hf₂ : Epi ((res R h₂).map f)) : Epi f := by
  have := preservesColimits_res R h₁
  have := preservesColimits_res R h₂
  refine Preadditive.epi_of_isZero_cokernel _ (isZero_of_isZero_res h₁ h₂ hcov _ ?_ ?_)
  · exact (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso (res R h₁) f)
  · exact (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso (res R h₂) f)

/-- **Injectivity is local.** A morphism of sheaves of modules on `Over T` whose restrictions to
`T₁` and `T₂` are monomorphisms, where `T ≤ T₁ ⊔ T₂`, is a monomorphism. -/
lemma mono_of_mono_res {T T₁ T₂ : Opens X} (h₁ : T₁ ≤ T) (h₂ : T₂ ≤ T)
    (hcov : T ≤ T₁ ⊔ T₂) {M N : SheafOfModules.{0} (R.over T)} (f : M ⟶ N)
    (hf₁ : Mono ((res R h₁).map f)) (hf₂ : Mono ((res R h₂).map f)) : Mono f := by
  have := preservesFiniteLimits_res R h₁
  have := preservesFiniteLimits_res R h₂
  refine Preadditive.mono_of_isZero_kernel _ (isZero_of_isZero_res h₁ h₂ hcov _ ?_ ?_)
  · exact (isZero_kernel_of_mono _).of_iso (PreservesKernel.iso (res R h₁) f)
  · exact (isZero_kernel_of_mono _).of_iso (PreservesKernel.iso (res R h₂) f)

/-- **Gluing of sections.** Sections of `M` over `T₁` and over `T₂` agreeing over `T₁ ⊓ T₂` glue
to a section over `T`, where `T ≤ T₁ ⊔ T₂`. -/
lemma exists_glue {T T₁ T₂ : Opens X} (h₁ : T₁ ≤ T) (h₂ : T₂ ≤ T)
    (hcov : T ≤ T₁ ⊔ T₂) (M : SheafOfModules.{0} (R.over T))
    (s₁ : Γ ((res R h₁).obj M)) (s₂ : Γ ((res R h₂).obj M))
    (hs : M.val.map (Over.homMk (homOfLE inf_le_left) (Subsingleton.elim _ _) :
        Over.mk (homOfLE (inf_le_left.trans h₁ : T₁ ⊓ T₂ ≤ T)) ⟶
          (Over.map (homOfLE h₁)).obj (topOver T₁)).op s₁ =
      M.val.map (Over.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _) :
        Over.mk (homOfLE (inf_le_left.trans h₁ : T₁ ⊓ T₂ ≤ T)) ⟶
          (Over.map (homOfLE h₂)).obj (topOver T₂)).op s₂) :
    ∃ s : Γ M, rΓ h₁ M s = s₁ ∧ rΓ h₂ M s = s₂ :=
  over_glue ((SheafOfModules.toSheaf _).obj M) (topOver T) _ _ _ _ _ _ _
    (fun x hx => hcov hx) (fun _ hx => hx) s₁ s₂ hs

end OverLocal

section Blocks

open Matrix

variable {S : Type*} [Ring S] {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- The block matrix `fromBlocks 1 B (-A) (1 - A * B)` is a right inverse of
`fromBlocks (1 - B * A) (-B) A 1`. -/
lemma fromBlocks_mul_inv (A : Matrix q p S) (B : Matrix p q S) :
    fromBlocks (1 - B * A) (-B) A 1 * fromBlocks 1 B (-A) (1 - A * B) = 1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · rw [Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, neg_neg, sub_add_cancel]
  · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_one,
      Matrix.mul_assoc]
    abel
  · rw [Matrix.mul_one, Matrix.one_mul, add_neg_cancel]
  · rw [Matrix.one_mul, add_sub_cancel]

/-- The block matrix `fromBlocks 1 B (-A) (1 - A * B)` is a left inverse of
`fromBlocks (1 - B * A) (-B) A 1`. -/
lemma fromBlocks_inv_mul (A : Matrix q p S) (B : Matrix p q S) :
    fromBlocks 1 B (-A) (1 - A * B) * fromBlocks (1 - B * A) (-B) A 1 = 1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · rw [Matrix.one_mul, sub_add_cancel]
  · rw [Matrix.one_mul, Matrix.mul_one, neg_add_cancel]
  · rw [Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  · rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      add_sub_cancel]

/-- If `vₖ = ∑ⱼ Aₖⱼ uⱼ` and `uⱼ = ∑ₖ Bⱼₖ vₖ`, then the block matrix
`fromBlocks (1 - B * A) (-B) A 1` sends the family `(u, 0)` to the family `(0, v)`. -/
lemma fromBlocks_relation {N : Type*} [AddCommGroup N] [Module S N] (u : p → N)
    (v : q → N) (A : Matrix q p S) (B : Matrix p q S) (hv : ∀ k, v k = ∑ j, A k j • u j)
    (hu : ∀ j, u j = ∑ k, B j k • v k) (x : p ⊕ q) :
    Sum.elim (0 : p → N) v x =
      ∑ y, fromBlocks (1 - B * A) (-B) A 1 x y • Sum.elim u (0 : q → N) y := by
  rw [Fintype.sum_sum_type]
  rcases x with j | k
  · simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      smul_zero,
      Finset.sum_const_zero, add_zero, Matrix.sub_apply, one_apply, mul_apply, sub_smul, ite_smul,
      one_smul, zero_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, ← hv, ← hu, sub_self]
  · simp only [Sum.elim_inr, Sum.elim_inl, Pi.zero_apply, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      smul_zero, Finset.sum_const_zero, add_zero, hv]

end Blocks

/-! ### Restrictions and matrices -/

section Matrices

variable {X : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

/-- Restriction of sheaves of modules from `W` to `V ≤ W` is additive. -/
lemma additive_res {V W : Opens X} (h : V ≤ W) : (res R h).Additive := by
  have := preservesFiniteLimits_res R h
  have : PreservesBinaryBiproducts (res R h) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Restricting twice is restricting once. -/
noncomputable def resResIso {W₂ W₁ W₀ : Opens X} (h₂ : W₂ ≤ W₁) (h₁ : W₁ ≤ W₀)
    (h : W₂ ≤ W₀) (M : SheafOfModules.{0} (R.over W₀)) :
    (res R h₂).obj ((res R h₁).obj M) ≅ (res R h).obj M :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun _ _ _ => rfl))

/-- `resResIso` is the identity on sections. -/
lemma resResIso_hom_app {W₂ W₁ W₀ : Opens X} (h₂ : W₂ ≤ W₁) (h₁ : W₁ ≤ W₀)
    (h : W₂ ≤ W₀) (M : SheafOfModules.{0} (R.over W₀)) (A : (Over W₂)ᵒᵖ) (m) :
    (resResIso h₂ h₁ h M).hom.val.app A m = m := rfl

/-- The inverse of `resResIso` is the identity on sections. -/
lemma resResIso_inv_app {W₂ W₁ W₀ : Opens X} (h₂ : W₂ ≤ W₁) (h₁ : W₁ ≤ W₀)
    (h : W₂ ≤ W₀) (M : SheafOfModules.{0} (R.over W₀)) (A : (Over W₂)ᵒᵖ) (m) :
    (resResIso h₂ h₁ h M).inv.val.app A m = m := rfl

/-- Restricting a section from `W₀` to `W₁` and then to `W₂` is, through `resResIso`,
restricting it from `W₀` to `W₂`. -/
lemma rΓ_rΓ {W₂ W₁ W₀ : Opens X} (h₂ : W₂ ≤ W₁) (h₁ : W₁ ≤ W₀)
    (M : SheafOfModules.{0} (R.over W₀)) (m : Γ M) :
    (resResIso h₂ h₁ (h₂.trans h₁) M).hom.val.app _ (rΓ h₂ _ (rΓ h₁ M m)) =
      rΓ (h₂.trans h₁) M m := by
  rw [resResIso_hom_app]
  change M.val.map ((Over.map (homOfLE h₁)).map
      (toTopOver ((Over.map (homOfLE h₂)).obj (topOver W₂)))).op
      (M.val.map (toTopOver ((Over.map (homOfLE h₁)).obj (topOver W₁))).op m) =
    M.val.map (toTopOver ((Over.map (homOfLE (h₂.trans h₁))).obj (topOver W₂))).op m
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- Restricting a function from `W₀` to `W₁` and then to `W₂` is restricting it from `W₀` to
`W₂`. -/
lemma rR_rR {W₂ W₁ W₀ : Opens X} (h₂ : W₂ ≤ W₁) (h₁ : W₁ ≤ W₀)
    (a : (R.over W₀).obj.obj (op (topOver W₀))) :
    rR h₂ (rR h₁ a) = rR (h₂.trans h₁) a := by
  show (R.obj.map _ ≫ R.obj.map _) a = R.obj.map _ a
  rw [← Functor.map_comp]
  rfl

/-- Restriction of a resolution. -/
lemma hasFFR_res {V W : Opens X} (h : V ≤ W) {M : SheafOfModules.{0} (R.over W)}
    {ℓ : ℕ} (hM : HasFFR M ℓ) : HasFFR ((res R h).obj M) ℓ := by
  have := preservesFiniteLimits_res R h
  have := preservesColimits_res R h
  have := additive_res (R := R) h
  exact HasFFR.map (res R h) (fun r => ⟨(freeRes h (Fin r)).symm⟩) hM

/-- The coefficient of `e_l` in a section of `𝒪^q`. -/
noncomputable def coeff {T : Opens X} {q : ℕ} (l : Fin q)
    (v : Γ (SheafOfModules.free (R := R.over T) (Fin q))) : (R.over T).obj.obj (op (topOver T)) :=
  (MMP.freeProj l).val.app _ v

/-- The coefficient of `e_l` in `∑ⱼ aⱼ eⱼ` is `a_l`. -/
lemma coeff_sum_smul {T : Opens X} {q : ℕ} (l : Fin q)
    (a : Fin q → (R.over T).obj.obj (op (topOver T))) :
    coeff l (∑ j, a j • eb (R := R) j) = a l := by
  have h1 : ∀ j : Fin q, coeff l (eb (R := R) (T := T) j) = if j = l then 1 else 0 := by
    intro j
    rw [coeff, eb, freeSection_coe]
    change ((SheafOfModules.ιFree j ≫ MMP.freeProj l).val.app _) (one1 _) = _
    rw [MMP.ιFree_freeProj]
    split_ifs
    · rfl
    · rfl
  have h2 : coeff l (∑ j, a j • eb (R := R) (T := T) j) = ∑ j, a j * coeff l (eb j) := by
    rw [coeff, map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
  rw [h2]
  simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `ofMatrix` is injective. -/
lemma ofMatrix_injective {T : Opens X} {p q : ℕ}
    {a b : Matrix (Fin p) (Fin q) ((R.over T).obj.obj (op (topOver T)))}
    (h : ofMatrix a = ofMatrix b) : a = b := by
  ext k l
  have := congrArg (fun f => coeff l (f.val.app (op (topOver T)) (eb k))) h
  simpa only [ofMatrix, ofTop_app_eb, coeff_sum_smul] using this

/-- Every morphism `𝒪ᵖ ⟶ 𝒪^q` is `ofMatrix a` for some matrix `a`. -/
lemma exists_eq_ofMatrix {T : Opens X} {p q : ℕ}
    (f : SheafOfModules.free (R := R.over T) (Fin p) ⟶ SheafOfModules.free (Fin q)) :
    ∃ a : Matrix (Fin p) (Fin q) ((R.over T).obj.obj (op (topOver T))), f = ofMatrix a := by
  choose a ha using fun k => MMP.exists_eq_sum_smul_freeSection (R := R.over T)
    (op (topOver T)) (f.val.app (op (topOver T)) (eb k))
  refine ⟨Matrix.of a, ?_⟩
  rw [eq_ofTop f, ofMatrix]
  congr 1
  funext k
  rw [ha k]
  rfl

/-- `ofMatrix a` is an isomorphism when the matrix `a` is invertible. -/
lemma isIso_ofMatrix {T : Opens X} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (a : Matrix I J ((R.over T).obj.obj (op (topOver T))))
    (b : Matrix J I ((R.over T).obj.obj (op (topOver T))))
    (hab : a * b = 1) (hba : b * a = 1) : IsIso (ofMatrix a) :=
  ⟨ofMatrix b, by rw [ofMatrix_comp_ofMatrix, hab, ofMatrix_one],
    by rw [ofMatrix_comp_ofMatrix, hba, ofMatrix_one]⟩

/-- If `ofMatrix a ≫ ofMatrix b` is the identity, then `a * b = 1`. -/
lemma mul_eq_one_of_ofMatrix_comp_eq_id {T : Opens X} {p q : ℕ}
    (a : Matrix (Fin p) (Fin q) ((R.over T).obj.obj (op (topOver T))))
    (b : Matrix (Fin q) (Fin p) ((R.over T).obj.obj (op (topOver T))))
    (h : ofMatrix a ≫ ofMatrix b = 𝟙 _) : a * b = 1 :=
  ofMatrix_injective (by rw [← ofMatrix_comp_ofMatrix, h, ofMatrix_one])

/-- Two bases of the same module differ by an invertible matrix. -/
lemma exists_transition {T : Opens X} {p q : ℕ} {N : SheafOfModules.{0} (R.over T)}
    (χ₁ : SheafOfModules.free (Fin p) ≅ N) (χ₂ : SheafOfModules.free (Fin q) ≅ N) :
    ∃ (G : Matrix (Fin q) (Fin p) ((R.over T).obj.obj (op (topOver T))))
      (H : Matrix (Fin p) (Fin q) ((R.over T).obj.obj (op (topOver T)))),
      G * H = 1 ∧ H * G = 1 ∧ ofMatrix G ≫ χ₁.hom = χ₂.hom := by
  obtain ⟨G, hG⟩ := exists_eq_ofMatrix (χ₂.hom ≫ χ₁.inv)
  obtain ⟨H, hH⟩ := exists_eq_ofMatrix (χ₁.hom ≫ χ₂.inv)
  refine ⟨G, H, mul_eq_one_of_ofMatrix_comp_eq_id G H ?_,
    mul_eq_one_of_ofMatrix_comp_eq_id H G ?_, ?_⟩
  · rw [← hG, ← hH]
    simp
  · rw [← hH, ← hG]
    simp
  · rw [← hG]
    simp

/-- `ofTop` of a tuple with a vanishing second block. -/
lemma ofTop_sumElim_zero {T : Opens X} {M : SheafOfModules.{0} (R.over T)} {I J : Type}
    (u : I → Γ M) :
    ofTop (Sum.elim u (0 : J → Γ M)) = (freeSumIso I J).hom ≫ biprod.desc (ofTop u) 0 := by
  apply M.freeHomEquiv.injective
  funext x
  rw [SheafOfModules.freeHomEquiv_comp_apply]
  change M.freeHomEquiv (M.freeHomEquiv.symm _) x = SheafOfModules.sectionsMap _
    ((SheafOfModules.free I ⊞ SheafOfModules.free J).freeHomEquiv
      ((SheafOfModules.free I ⊞ SheafOfModules.free J).freeHomEquiv.symm _) x)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rcases x with i | j
  · change secOfTop M (u i) = SheafOfModules.sectionsMap (biprod.inl ≫ _) _
    rw [biprod.inl_desc, ← SheafOfModules.freeHomEquiv_apply, ofTop, Equiv.apply_symm_apply]
  · change secOfTop M 0 = SheafOfModules.sectionsMap (biprod.inr ≫ _) _
    rw [biprod.inr_desc]
    refine Subtype.ext (funext fun A => ?_)
    rw [secOfTop_coe, map_zero]
    rfl

/-- `ofTop` of a tuple with a vanishing first block. -/
lemma ofTop_sumElim_zero' {T : Opens X} {M : SheafOfModules.{0} (R.over T)} {I J : Type}
    (v : J → Γ M) :
    ofTop (Sum.elim (0 : I → Γ M) v) = (freeSumIso I J).hom ≫ biprod.desc 0 (ofTop v) := by
  apply M.freeHomEquiv.injective
  funext x
  rw [SheafOfModules.freeHomEquiv_comp_apply]
  change M.freeHomEquiv (M.freeHomEquiv.symm _) x = SheafOfModules.sectionsMap _
    ((SheafOfModules.free I ⊞ SheafOfModules.free J).freeHomEquiv
      ((SheafOfModules.free I ⊞ SheafOfModules.free J).freeHomEquiv.symm _) x)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rcases x with i | j
  · change secOfTop M 0 = SheafOfModules.sectionsMap (biprod.inl ≫ _) _
    rw [biprod.inl_desc]
    refine Subtype.ext (funext fun A => ?_)
    rw [secOfTop_coe, map_zero]
    rfl
  · change secOfTop M (v j) = SheafOfModules.sectionsMap (biprod.inr ≫ _) _
    rw [biprod.inr_desc, ← SheafOfModules.freeHomEquiv_apply, ofTop, Equiv.apply_symm_apply]

/-- A kernel conjugate, by isomorphisms, to the restriction of a kernel with a resolution has a
resolution. -/
lemma hasFFR_kernel_of_comp_eq {V W : Opens X} (hVW : V ≤ W)
    {P Q : SheafOfModules.{0} (R.over V)} {P' Q' : SheafOfModules.{0} (R.over V)}
    {E F : SheafOfModules.{0} (R.over W)} (e₁ : P' ⟶ P) (x : P ⟶ Q) (e₂ : Q ⟶ Q')
    (y₁ : P' ⟶ (res R hVW).obj E) (f : E ⟶ F) (y₂ : (res R hVW).obj F ⟶ Q')
    [IsIso e₁] [IsIso e₂] [IsIso y₁] [IsIso y₂] (h : e₁ ≫ x ≫ e₂ = y₁ ≫ (res R hVW).map f ≫ y₂)
    {ℓ : ℕ} (hk : HasFFR (kernel f) ℓ) : HasFFR (kernel x) ℓ := by
  have := preservesFiniteLimits_res R hVW
  have h1 := hasFFR_res hVW hk
  have h2 := h1.of_iso (PreservesKernel.iso (res R hVW) f)
  have h3 := h2.of_iso ((kernelCompMono ((res R hVW).map f) y₂).symm ≪≫
    (kernelIsIsoComp y₁ ((res R hVW).map f ≫ y₂)).symm)
  have h4 := h3.of_iso (kernelIsoOfEq h.symm)
  exact h4.of_iso (kernelIsIsoComp e₁ (x ≫ e₂) ≪≫ kernelCompMono x e₂)

end Matrices

/-! ### Blocks and boxes -/

section Boxes

variable {n : ℕ}

/-- The block `∏ᵢ [aᵢ, bᵢ] × [cᵢ, dᵢ]`. -/
abbrev block (a b c d : Fin n → ℝ) : Set (EuclideanSpace ℂ (Fin n)) :=
  {z | ∀ i, z i ∈ Set.Icc (a i) (b i) ×ℂ Set.Icc (c i) (d i)}

/-- The open box `∏ᵢ (aᵢ, bᵢ) × (cᵢ, dᵢ)`. -/
abbrev box (a b c d : Fin n → ℝ) : Set (EuclideanSpace ℂ (Fin n)) :=
  {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)}

/-- The box `box a b c d` is open. -/
lemma isOpen_box (a b c d : Fin n → ℝ) : IsOpen (box a b c d) := by
  simp only [box, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i =>
    (IsOpen.reProdIm isOpen_Ioo isOpen_Ioo).preimage (PiLp.continuous_apply 2 _ i)

/-- The block `block a b c d` is compact. -/
lemma isCompact_block (a b c d : Fin n → ℝ) : IsCompact (block a b c d) := by
  have h : block a b c d = (EuclideanSpace.equiv (Fin n) ℂ).symm ''
      Set.univ.pi fun i => Set.Icc (a i) (b i) ×ℂ Set.Icc (c i) (d i) := by
    ext z
    simp only [block, Set.mem_setOf_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hz
      exact ⟨EuclideanSpace.equiv (Fin n) ℂ z, hz, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      exact hw
  rw [h]
  exact (isCompact_univ_pi fun i => isCompact_Icc.reProdIm isCompact_Icc).image
    (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous

/-- If every coordinate of `x ∈ ℂⁿ` has norm `< η`, then `‖x‖ < (n + 1) η`. -/
lemma norm_lt_of_forall_norm_lt {x : EuclideanSpace ℂ (Fin n)} {η : ℝ} (hη : 0 < η)
    (hx : ∀ i, ‖x i‖ < η) : ‖x‖ < (n + 1) * η := by
  have h1 : ‖x‖ ^ 2 ≤ n * η ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin n, η ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hx i).le 2
      _ = n * η ^ 2 := by simp
  have h2 : (n : ℝ) * η ^ 2 < ((n + 1) * η) ^ 2 := by
    have : (n : ℝ) ≤ (n + 1) ^ 2 - 1 := by nlinarith
    nlinarith [sq_nonneg η, mul_pos hη hη]
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (h1.trans_lt h2)

/-- Clamping `x` into `[a, b]` moves it by less than `δ` when `x ∈ (a - δ, b + δ)`. -/
lemma abs_sub_max_min_lt {a b x δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (h₁ : a - δ < x)
    (h₂ : x < b + δ) : |x - max a (min x b)| < δ := by
  refine abs_lt.2 ⟨?_, ?_⟩
  · rw [neg_lt_sub_iff_lt_add]
    exact max_lt (by linarith) ((min_le_left _ _).trans_lt (by linarith))
  · rcases le_total x b with h | h
    · rw [min_eq_left h]
      linarith [le_max_right a x]
    · rw [min_eq_right h, max_eq_right hab]
      linarith

/-- Widening a nonempty block by `δ` in every direction lands in its `(n + 1) (2 δ)`-thickening. -/
lemma box_subset_thickening_block {a b c d : Fin n → ℝ} (hab : ∀ i, a i ≤ b i)
    (hcd : ∀ i, c i ≤ d i) {δ : ℝ} (hδ0 : 0 < δ) :
    box (fun i => a i - δ) (fun i => b i + δ) (fun i => c i - δ) (fun i => d i + δ) ⊆
      Metric.thickening ((n + 1) * (2 * δ)) (block a b c d) := by
  intro z hz
  let w : EuclideanSpace ℂ (Fin n) := (EuclideanSpace.equiv (Fin n) ℂ).symm fun i =>
    ⟨max (a i) (min (z i).re (b i)), max (c i) (min (z i).im (d i))⟩
  have hw : w ∈ block a b c d := fun i =>
    ⟨⟨le_max_left _ _, max_le (hab i) (min_le_right _ _)⟩,
      ⟨le_max_left _ _, max_le (hcd i) (min_le_right _ _)⟩⟩
  refine Metric.mem_thickening_iff.2 ⟨w, hw, ?_⟩
  rw [dist_eq_norm]
  have hcoord : ∀ i, ‖(z - w) i‖ < 2 * δ := by
    intro i
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz i
    have : (z - w) i = z i - ⟨max (a i) (min (z i).re (b i)), max (c i) (min (z i).im (d i))⟩ :=
      rfl
    rw [this]
    calc ‖z i - ⟨max (a i) (min (z i).re (b i)), max (c i) (min (z i).im (d i))⟩‖
        ≤ |(z i - ⟨max (a i) (min (z i).re (b i)), max (c i) (min (z i).im (d i))⟩).re| +
          |(z i - ⟨max (a i) (min (z i).re (b i)), max (c i) (min (z i).im (d i))⟩).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ < δ + δ :=
        add_lt_add (abs_sub_max_min_lt hδ0 (hab i) h1 h2) (abs_sub_max_min_lt hδ0 (hcd i) h3 h4)
      _ = 2 * δ := by ring
  exact norm_lt_of_forall_norm_lt (by positivity) hcoord

/-- **Boxes between a block and an open set.** If a block `K` of `ℂⁿ` lies in an open subset `U`
and `K ⊆ O` for an open `O ⊆ U`, there is an open product of open rectangles `P` with
`K ⊆ P ⊆ O`. -/
lemma exists_box_between (U : Opens (EuclideanSpace ℂ (Fin n))) (a b c d : Fin n → ℝ)
    (hKU : block a b c d ⊆ U) (O : Opens (TopCat.of U))
    (hKO : (Subtype.val : U → _) ⁻¹' block a b c d ⊆ O) :
    ∃ (P : Opens (TopCat.of U)), P ≤ O ∧
      (∃ a' b' c' d' : Fin n → ℝ, Subtype.val '' (P : Set U) = box a' b' c' d') ∧
      (Subtype.val : U → _) ⁻¹' block a b c d ⊆ P := by
  by_cases hne : (block a b c d).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    have hab : ∀ i, a i ≤ b i := fun i => (hz₀ i).1.1.trans (hz₀ i).1.2
    have hcd : ∀ i, c i ≤ d i := fun i => (hz₀ i).2.1.trans (hz₀ i).2.2
    let O' : Set (EuclideanSpace ℂ (Fin n)) := Subtype.val '' (O : Set U)
    have hO' : IsOpen O' := U.isOpenEmbedding'.isOpenMap _ O.isOpen
    have hKO' : block a b c d ⊆ O' := fun z hz => ⟨⟨z, hKU hz⟩, hKO hz, rfl⟩
    obtain ⟨ε, hε, hεK⟩ := (isCompact_block a b c d).exists_thickening_subset_open hO' hKO'
    set δ : ℝ := ε / (2 * (n + 1)) with hδ
    have hδ0 : 0 < δ := by positivity
    let B := box (fun i => a i - δ) (fun i => b i + δ) (fun i => c i - δ) (fun i => d i + δ)
    have hBO : B ⊆ O' := fun z hz => hεK (by
      have hε' : (n + 1 : ℝ) * (2 * δ) = ε := by rw [hδ]; field_simp
      rw [← hε']
      exact box_subset_thickening_block hab hcd hδ0 hz)
    refine ⟨⟨{x : U | (x : EuclideanSpace ℂ (Fin n)) ∈ B},
      (isOpen_box _ _ _ _).preimage continuous_subtype_val⟩, ?_,
      ⟨fun i => a i - δ, fun i => b i + δ, fun i => c i - δ, fun i => d i + δ, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := hBO hx
      rw [← Subtype.ext hxy]
      exact hy
    · ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hz
        obtain ⟨y, -, hyz⟩ := hBO hz
        exact ⟨⟨z, hyz ▸ y.2⟩, hz, rfl⟩
    · intro x hx i
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx i
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · obtain ⟨i₀⟩ : Nonempty (Fin n) := by
      by_contra hn
      rw [not_nonempty_iff] at hn
      exact hne ⟨0, fun i => (IsEmpty.false i).elim⟩
    refine ⟨⊥, bot_le, ⟨0, 0, 0, 0, ?_⟩, ?_⟩
    · ext z
      simp only [Opens.coe_bot, Set.image_empty, Set.mem_empty_iff_false, false_iff]
      intro hz
      have := (hz i₀).1
      simp at this
    · intro x hx
      exact (hne ⟨x.1, hx⟩).elim

/-- Merging along one real direction: a property of intervals `[x, y] ⊆ [lo, hi]` holding for
short intervals and stable under gluing at interior points holds for `[lo, hi]`. -/
lemma interval_induction (Q : ℝ → ℝ → Prop) {lo hi η : ℝ} (hη : 0 < η) (hlh : lo ≤ hi)
    (hsmall : ∀ x y, lo ≤ x → x ≤ y → y ≤ hi → y - x ≤ η → Q x y)
    (hglue : ∀ x t y, lo ≤ x → x < t → t < y → y ≤ hi → Q x t → Q t y → Q x y) : Q lo hi := by
  by_cases hsm : hi - lo ≤ η
  · exact hsmall lo hi le_rfl hlh le_rfl hsm
  push Not at hsm
  set N : ℕ := ⌈(hi - lo) / η⌉₊ with hN
  have hlen : 0 < hi - lo := lt_trans hη hsm
  have hN1 : 1 ≤ N := by
    rw [hN, Nat.one_le_ceil_iff]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set h := (hi - lo) / N with hh
  have hhpos : 0 < h := by positivity
  have hhη : h ≤ η := by
    rw [hh, div_le_iff₀ hNpos]
    have := Nat.le_ceil ((hi - lo) / η)
    rw [← hN, div_le_iff₀ hη] at this
    linarith
  let t : ℕ → ℝ := fun k => lo + k * h
  have ht0 : t 0 = lo := by simp [t]
  have htN : t N = hi := by
    simp only [t, hh]; field_simp; ring
  have hmono : ∀ k, t k < t (k + 1) := fun k => by simp only [t]; push_cast; linarith
  have hle : ∀ k, k ≤ N → t k ≤ hi := fun k hk => by
    rw [← htN]; simp only [t]
    have : (k : ℝ) ≤ N := by exact_mod_cast hk
    nlinarith
  have hge : ∀ k, lo ≤ t k := fun k => by
    simp only [t]
    have : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have key : ∀ k, 1 ≤ k → k ≤ N → Q lo (t k) := by
    intro k hk1 hkN
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · refine hsmall lo (t 1) le_rfl (hge 1) (hle 1 hkN) ?_
        simp [t, hhη]
      · have hQk := ih hk (by omega)
        have hQ2 : Q (t k) (t (k + 1)) := hsmall _ _ (hge k) (hmono k).le (hle _ hkN) (by
          simp only [t]; push_cast; linarith)
        have hlt : lo < t k := by
          simp only [t]
          have : (0 : ℝ) < k := by exact_mod_cast hk
          nlinarith
        exact hglue lo (t k) (t (k + 1)) le_rfl hlt (hmono k) (hle _ hkN) hQk hQ2
  simpa [htN] using key N hN1 le_rfl

/-- Updating one coordinate of `a ≤ b` inside `[a₀, b₀]` to `a i ≤ x ≤ y ≤ b i` keeps
`a₀ ≤ a ≤ b ≤ b₀`. -/
lemma le_update_le_update_le {a₀ a b b₀ : Fin n → ℝ} (h₁ : a₀ ≤ a) (h₂ : a ≤ b) (h₃ : b ≤ b₀)
    {i : Fin n} {x y : ℝ} (hx : a i ≤ x) (hxy : x ≤ y) (hy : y ≤ b i) :
    a₀ ≤ Function.update a i x ∧ Function.update a i x ≤ Function.update b i y ∧
      Function.update b i y ≤ b₀ :=
  ⟨le_update_iff.2 ⟨(h₁ i).trans hx, fun j _ => h₁ j⟩,
    update_le_update_iff.2 ⟨hxy, fun j _ => h₂ j⟩,
    update_le_iff.2 ⟨hy.trans (h₃ i), fun j _ => h₃ j⟩⟩

/-- **Subdivision of a block.** A property of sub-blocks of `∏ [a₀, b₀] × [c₀, d₀]` holding for
blocks with all sides `≤ η` and stable under gluing two adjacent blocks along a real or imaginary
cut holds for the whole block. -/
lemma block_induction
    (G : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → Prop)
    (a₀ b₀ c₀ d₀ : Fin n → ℝ) (hab₀ : a₀ ≤ b₀) (hcd₀ : c₀ ≤ d₀) {η : ℝ} (hη : 0 < η)
    (hsmall : ∀ a b c d, a₀ ≤ a → a ≤ b → b ≤ b₀ → c₀ ≤ c → c ≤ d → d ≤ d₀ →
      (∀ i, b i - a i ≤ η) → (∀ i, d i - c i ≤ η) → G a b c d)
    (hre : ∀ a b c d i t, a₀ ≤ a → a ≤ b → b ≤ b₀ → c₀ ≤ c → c ≤ d → d ≤ d₀ →
      a i < t → t < b i → G a (Function.update b i t) c d → G (Function.update a i t) b c d →
      G a b c d)
    (him : ∀ a b c d i t, a₀ ≤ a → a ≤ b → b ≤ b₀ → c₀ ≤ c → c ≤ d → d ≤ d₀ →
      c i < t → t < d i → G a b c (Function.update d i t) → G a b (Function.update c i t) d →
      G a b c d) :
    G a₀ b₀ c₀ d₀ := by
  classical
  let P : Finset (Fin n × Bool) → Prop := fun D => ∀ a b c d, a₀ ≤ a → a ≤ b → b ≤ b₀ →
    c₀ ≤ c → c ≤ d → d ≤ d₀ → (∀ i, (i, false) ∉ D → b i - a i ≤ η) →
    (∀ i, (i, true) ∉ D → d i - c i ≤ η) → G a b c d
  have hP : ∀ D, P D := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro a b c d h1 h2 h3 h4 h5 h6 hb hd
      exact hsmall a b c d h1 h2 h3 h4 h5 h6 (fun i => hb i (Finset.notMem_empty _))
        (fun i => hd i (Finset.notMem_empty _))
    | insert e D he ih =>
      intro a b c d h1 h2 h3 h4 h5 h6 hb hd
      obtain ⟨i, _ | _⟩ := e
      · -- a real direction
        have key := interval_induction (fun x y => G (Function.update a i x)
          (Function.update b i y) c d) hη (h2 i) (fun x y hx hxy hy hyx => by
            obtain ⟨e₁, e₂, e₃⟩ := le_update_le_update_le h1 h2 h3 hx hxy hy
            refine ih _ _ c d e₁ e₂ e₃ h4 h5 h6 (fun i' hi' => ?_) (fun i' hi' => hd i' (by
              simpa only [Finset.mem_insert, Prod.mk.injEq, Bool.true_eq_false, and_false,
                false_or] using hi'))
            rcases eq_or_ne i' i with rfl | hj
            · simpa using hyx
            · simpa only [Function.update_of_ne hj] using hb i' (by simp [Prod.mk.injEq, hj, hi']))
          (fun x t y hx hxt hty hy hQ₁ hQ₂ => by
            obtain ⟨e₁, e₂, e₃⟩ := le_update_le_update_le h1 h2 h3 hx (hxt.trans hty).le hy
            exact hre _ _ c d i t e₁ e₂ e₃ h4 h5 h6 (by simpa using hxt) (by simpa using hty)
              (by simpa using hQ₁) (by simpa using hQ₂))
        simpa using key
      · -- an imaginary direction
        have key := interval_induction (fun x y => G a b (Function.update c i x)
          (Function.update d i y)) hη (h5 i) (fun x y hx hxy hy hyx => by
            obtain ⟨e₁, e₂, e₃⟩ := le_update_le_update_le h4 h5 h6 hx hxy hy
            refine ih a b _ _ h1 h2 h3 e₁ e₂ e₃ (fun i' hi' => hb i' (by
              simpa only [Finset.mem_insert, Prod.mk.injEq, Bool.false_eq_true, and_false,
                false_or] using hi')) (fun i' hi' => ?_)
            rcases eq_or_ne i' i with rfl | hj
            · simpa using hyx
            · simpa only [Function.update_of_ne hj] using hd i' (by simp [Prod.mk.injEq, hj, hi']))
          (fun x t y hx hxt hty hy hQ₁ hQ₂ => by
            obtain ⟨e₁, e₂, e₃⟩ := le_update_le_update_le h4 h5 h6 hx (hxt.trans hty).le hy
            exact him a b _ _ i t h1 h2 h3 e₁ e₂ e₃ (by simpa using hxt) (by simpa using hty)
              (by simpa using hQ₁) (by simpa using hQ₂))
        simpa using key
  exact hP Finset.univ a₀ b₀ c₀ d₀ le_rfl hab₀ le_rfl le_rfl hcd₀ le_rfl
    (fun i hi => (hi (Finset.mem_univ _)).elim) (fun i hi => (hi (Finset.mem_univ _)).elim)

/-- Raising the lower bounds and lowering the upper bounds of a block shrinks it. -/
lemma block_mono {a b c d a' b' c' d' : Fin n → ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    (hc : c ≤ c') (hd : d' ≤ d) : block a' b' c' d' ⊆ block a b c d := fun z hz i => by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz i
  exact ⟨⟨(ha i).trans h1, h2.trans (hb i)⟩, (hc i).trans h3, h4.trans (hd i)⟩

/-- A block with `a ≤ b` and `c ≤ d` is nonempty. -/
lemma block_nonempty {a b c d : Fin n → ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (block a b c d).Nonempty :=
  ⟨(EuclideanSpace.equiv (Fin n) ℂ).symm fun i => ⟨a i, c i⟩, fun i =>
    ⟨⟨le_rfl, hab i⟩, le_rfl, hcd i⟩⟩

/-- Lowering the `i`-th real upper bound of a block to `t` cuts it along `Re zᵢ ≤ t`. -/
lemma mem_block_update_b_iff {a b c d : Fin n → ℝ} {i : Fin n} {t : ℝ} (ht : t ≤ b i)
    {z : EuclideanSpace ℂ (Fin n)} :
    z ∈ block a (Function.update b i t) c d ↔ z ∈ block a b c d ∧ (z i).re ≤ t := by
  constructor
  · intro hz
    refine ⟨fun j => ?_, by simpa using (Complex.mem_reProdIm.1 (hz i)).1.2⟩
    obtain ⟨⟨e1, e2⟩, e3⟩ := hz j
    refine ⟨⟨e1, ?_⟩, e3⟩
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self] at e2
      exact e2.trans ht
    · rwa [Function.update_of_ne hj] at e2
  · rintro ⟨hz, hzt⟩ j
    obtain ⟨⟨e1, e2⟩, e3⟩ := hz j
    refine ⟨⟨e1, ?_⟩, e3⟩
    rcases eq_or_ne j i with rfl | hj
    · rwa [Function.update_self]
    · rwa [Function.update_of_ne hj]

/-- Raising the `i`-th real lower bound of a block to `t` cuts it along `t ≤ Re zᵢ`. -/
lemma mem_block_update_a_iff {a b c d : Fin n → ℝ} {i : Fin n} {t : ℝ} (ht : a i ≤ t)
    {z : EuclideanSpace ℂ (Fin n)} :
    z ∈ block (Function.update a i t) b c d ↔ z ∈ block a b c d ∧ t ≤ (z i).re := by
  constructor
  · intro hz
    refine ⟨fun j => ?_, by simpa using (Complex.mem_reProdIm.1 (hz i)).1.1⟩
    obtain ⟨⟨e1, e2⟩, e3⟩ := hz j
    refine ⟨⟨?_, e2⟩, e3⟩
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self] at e1
      exact ht.trans e1
    · rwa [Function.update_of_ne hj] at e1
  · rintro ⟨hz, hzt⟩ j
    obtain ⟨⟨e1, e2⟩, e3⟩ := hz j
    refine ⟨⟨?_, e2⟩, e3⟩
    rcases eq_or_ne j i with rfl | hj
    · rwa [Function.update_self]
    · rwa [Function.update_of_ne hj]

/-- Lowering the `i`-th imaginary upper bound of a block to `t` cuts it along `Im zᵢ ≤ t`. -/
lemma mem_block_update_d_iff {a b c d : Fin n → ℝ} {i : Fin n} {t : ℝ} (ht : t ≤ d i)
    {z : EuclideanSpace ℂ (Fin n)} :
    z ∈ block a b c (Function.update d i t) ↔ z ∈ block a b c d ∧ (z i).im ≤ t := by
  constructor
  · intro hz
    refine ⟨fun j => ?_, by simpa using (Complex.mem_reProdIm.1 (hz i)).2.2⟩
    obtain ⟨e0, e1, e2⟩ := hz j
    refine ⟨e0, e1, ?_⟩
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self] at e2
      exact e2.trans ht
    · rwa [Function.update_of_ne hj] at e2
  · rintro ⟨hz, hzt⟩ j
    obtain ⟨e0, e1, e2⟩ := hz j
    refine ⟨e0, e1, ?_⟩
    rcases eq_or_ne j i with rfl | hj
    · rwa [Function.update_self]
    · rwa [Function.update_of_ne hj]

/-- Raising the `i`-th imaginary lower bound of a block to `t` cuts it along `t ≤ Im zᵢ`. -/
lemma mem_block_update_c_iff {a b c d : Fin n → ℝ} {i : Fin n} {t : ℝ} (ht : c i ≤ t)
    {z : EuclideanSpace ℂ (Fin n)} :
    z ∈ block a b (Function.update c i t) d ↔ z ∈ block a b c d ∧ t ≤ (z i).im := by
  constructor
  · intro hz
    refine ⟨fun j => ?_, by simpa using (Complex.mem_reProdIm.1 (hz i)).2.1⟩
    obtain ⟨e0, e1, e2⟩ := hz j
    refine ⟨e0, ?_, e2⟩
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self] at e1
      exact ht.trans e1
    · rwa [Function.update_of_ne hj] at e1
  · rintro ⟨hz, hzt⟩ j
    obtain ⟨e0, e1, e2⟩ := hz j
    refine ⟨e0, ?_, e2⟩
    rcases eq_or_ne j i with rfl | hj
    · rwa [Function.update_self]
    · rwa [Function.update_of_ne hj]

/-- Cutting a block along `Re zᵢ = t` writes it as the union of the two halves. -/
lemma block_cut_re_union {a b c d : Fin n → ℝ} (i : Fin n) {t : ℝ} (h1 : a i ≤ t)
    (h2 : t ≤ b i) :
    block a (Function.update b i t) c d ∪ block (Function.update a i t) b c d = block a b c d := by
  ext z
  constructor
  · rintro (hz | hz) j
    · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hz j
      by_cases hj : j = i
      · subst hj; rw [Function.update_self] at e2; exact ⟨⟨e1, e2.trans h2⟩, e3, e4⟩
      · rw [Function.update_of_ne hj] at e2; exact ⟨⟨e1, e2⟩, e3, e4⟩
    · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hz j
      by_cases hj : j = i
      · subst hj; rw [Function.update_self] at e1; exact ⟨⟨h1.trans e1, e2⟩, e3, e4⟩
      · rw [Function.update_of_ne hj] at e1; exact ⟨⟨e1, e2⟩, e3, e4⟩
  · intro hz
    rcases le_total (z i).re t with ht | ht
    · refine Or.inl fun j => ?_
      obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hz j
      by_cases hj : j = i
      · subst hj; exact ⟨⟨e1, by rwa [Function.update_self]⟩, e3, e4⟩
      · exact ⟨⟨e1, by rwa [Function.update_of_ne hj]⟩, e3, e4⟩
    · refine Or.inr fun j => ?_
      obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hz j
      by_cases hj : j = i
      · subst hj; exact ⟨⟨by rwa [Function.update_self], e2⟩, e3, e4⟩
      · exact ⟨⟨by rwa [Function.update_of_ne hj], e2⟩, e3, e4⟩

/-- The two halves of a block cut along `Re zᵢ = t` meet in the face `Re zᵢ = t`. -/
lemma block_cut_re_inter {a b c d : Fin n → ℝ} (i : Fin n) {t : ℝ} (h1 : a i ≤ t)
    (h2 : t ≤ b i) :
    block a (Function.update b i t) c d ∩ block (Function.update a i t) b c d =
      block (Function.update a i t) (Function.update b i t) c d := by
  ext z
  constructor
  · rintro ⟨hz₁, hz₂⟩ j
    obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hz₁ j
    obtain ⟨⟨f1, f2⟩, -, -⟩ := hz₂ j
    exact ⟨⟨f1, e2⟩, e3, e4⟩
  · intro hz
    refine ⟨fun j => ?_, fun j => ?_⟩
    · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hz j
      refine ⟨⟨?_, e2⟩, e3, e4⟩
      by_cases hj : j = i
      · subst hj; rw [Function.update_self] at e1; exact h1.trans e1
      · rwa [Function.update_of_ne hj] at e1
    · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hz j
      refine ⟨⟨e1, ?_⟩, e3, e4⟩
      by_cases hj : j = i
      · subst hj; rw [Function.update_self] at e2; exact e2.trans h2
      · rwa [Function.update_of_ne hj] at e2

/-- Cutting a block along `Im zᵢ = t` writes it as the union of the two halves. -/
lemma block_cut_im_union {a b c d : Fin n → ℝ} (i : Fin n) {t : ℝ} (h1 : c i ≤ t)
    (h2 : t ≤ d i) :
    block a b c (Function.update d i t) ∪ block a b (Function.update c i t) d = block a b c d := by
  ext z
  constructor
  · rintro (hz | hz) j
    · obtain ⟨e0, e1, e2⟩ := hz j
      by_cases hj : j = i
      · subst hj; rw [Function.update_self] at e2; exact ⟨e0, e1, e2.trans h2⟩
      · rw [Function.update_of_ne hj] at e2; exact ⟨e0, e1, e2⟩
    · obtain ⟨e0, e1, e2⟩ := hz j
      by_cases hj : j = i
      · subst hj; rw [Function.update_self] at e1; exact ⟨e0, h1.trans e1, e2⟩
      · rw [Function.update_of_ne hj] at e1; exact ⟨e0, e1, e2⟩
  · intro hz
    rcases le_total (z i).im t with ht | ht
    · refine Or.inl fun j => ?_
      obtain ⟨e0, e1, e2⟩ := hz j
      by_cases hj : j = i
      · subst hj; exact ⟨e0, e1, by rwa [Function.update_self]⟩
      · exact ⟨e0, e1, by rwa [Function.update_of_ne hj]⟩
    · refine Or.inr fun j => ?_
      obtain ⟨e0, e1, e2⟩ := hz j
      by_cases hj : j = i
      · subst hj; exact ⟨e0, by rwa [Function.update_self], e2⟩
      · exact ⟨e0, by rwa [Function.update_of_ne hj], e2⟩

/-- The two halves of a block cut along `Im zᵢ = t` meet in the face `Im zᵢ = t`. -/
lemma block_cut_im_inter {a b c d : Fin n → ℝ} (i : Fin n) {t : ℝ} (h1 : c i ≤ t)
    (h2 : t ≤ d i) :
    block a b c (Function.update d i t) ∩ block a b (Function.update c i t) d =
      block a b (Function.update c i t) (Function.update d i t) := by
  ext z
  constructor
  · rintro ⟨hz₁, hz₂⟩ j
    obtain ⟨e0, e1, e2⟩ := hz₁ j
    obtain ⟨-, f1, f2⟩ := hz₂ j
    exact ⟨e0, f1, e2⟩
  · intro hz
    refine ⟨fun j => ?_, fun j => ?_⟩
    · obtain ⟨e0, e1, e2⟩ := hz j
      refine ⟨e0, ?_, e2⟩
      by_cases hj : j = i
      · subst hj; rw [Function.update_self] at e1; exact h1.trans e1
      · rwa [Function.update_of_ne hj] at e1
    · obtain ⟨e0, e1, e2⟩ := hz j
      refine ⟨e0, e1, ?_⟩
      by_cases hj : j = i
      · subst hj; rw [Function.update_self] at e2; exact e2.trans h2
      · rwa [Function.update_of_ne hj] at e2

end Boxes

/-! ### Holomorphic functions and sections -/

section Holomorphic

variable {n : ℕ}

variable {U : Opens (EuclideanSpace ℂ (Fin n))}

/-- The image in `ℂⁿ` of an open subset `Y` of `U`. -/
def imO (Y : Opens (TopCat.of U)) : Opens (EuclideanSpace ℂ (Fin n)) :=
  ⟨Subtype.val '' (Y : Set U), U.isOpenEmbedding'.isOpenMap _ Y.isOpen⟩

/-- The image in `ℂⁿ` of a point of `Y` lies in `imO Y`. -/
lemma mem_imO {Y : Opens (TopCat.of U)} (y : Y) : ((y : U) : EuclideanSpace ℂ (Fin n)) ∈ imO Y :=
  ⟨y.1, y.2, rfl⟩

/-- A point of `imO Y` lies in `U`. -/
lemma mem_U_of_mem_imO {Y : Opens (TopCat.of U)} {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ imO Y) : z ∈ U := by
  obtain ⟨x, -, rfl⟩ := hz
  exact x.2

/-- A point of `imO Y`, as a point of `U`, lies in `Y`. -/
lemma mem_of_mem_imO {Y : Opens (TopCat.of U)} {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ imO Y) : (⟨z, mem_U_of_mem_imO hz⟩ : U) ∈ Y := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact hx

/-- A set whose preimage in `U` lies in `Y` lies in `imO Y`. -/
lemma subset_imO {K : Set (EuclideanSpace ℂ (Fin n))} {Y : Opens (TopCat.of U)} (hKU : K ⊆ U)
    (hK : (Subtype.val : U → _) ⁻¹' K ⊆ Y) : K ⊆ imO Y := fun z hz =>
  ⟨⟨z, hKU hz⟩, hK (show (⟨z, hKU hz⟩ : U).1 ∈ K from hz), rfl⟩

/-- A function holomorphic near the image of `Y`, as a section of `𝒪_U` over `Y`. -/
noncomputable def secOfFun (Y : Opens (TopCat.of U)) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (O : Set (EuclideanSpace ℂ (Fin n))) (hO : IsOpen O) (hF : DifferentiableOn ℂ F O)
    (hY : ∀ y : Y, ((y : U) : EuclideanSpace ℂ (Fin n)) ∈ O) :
    𝒪[n, U].presheaf.obj (op Y) :=
  ⟨fun y => F y.1.1, by
    have h1 : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ F O :=
      ((analyticOnNhd_of_differentiableOn hO hF).contDiffOn hO.uniqueDiffOn).contMDiffOn
    have h2 : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞
        (fun y : Y => ((y : U) : EuclideanSpace ℂ (Fin n))) :=
      contMDiff_subtype_val.comp contMDiff_subtype_val
    intro y
    exact ((h1.contMDiffAt (hO.mem_nhds (hY y))).comp y (h2 y))⟩

open scoped Classical in
/-- A section of `𝒪_U` over `Y`, as a function on `ℂⁿ` (extended by zero). -/
noncomputable def funOfSec {Y : Opens (TopCat.of U)} (s : 𝒪[n, U].presheaf.obj (op Y)) :
    EuclideanSpace ℂ (Fin n) → ℂ := fun z =>
  if h : z ∈ imO Y then s ⟨⟨z, mem_U_of_mem_imO h⟩, mem_of_mem_imO h⟩ else 0

/-- `funOfSec s` agrees with `s` on `Y`. -/
lemma funOfSec_apply {Y : Opens (TopCat.of U)} (s : 𝒪[n, U].presheaf.obj (op Y)) (y : Y) :
    funOfSec s ((y : U) : EuclideanSpace ℂ (Fin n)) = s y := by
  rw [funOfSec, dif_pos (mem_imO y)]

/-- `funOfSec s` is holomorphic on `imO Y`. -/
lemma differentiableOn_funOfSec {Y : Opens (TopCat.of U)}
    (s : 𝒪[n, U].presheaf.obj (op Y)) : DifferentiableOn ℂ (funOfSec s) (imO Y) := by
  intro z hz
  let ψ : imO Y → Y := fun x => ⟨⟨x.1, mem_U_of_mem_imO x.2⟩, mem_of_mem_imO x.2⟩
  have hψ : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ ψ :=
    contMDiff_val_val' ψ fun _ => rfl
  have hs : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (fun x : imO Y => s (ψ x)) :=
    (show ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (s : Y → ℂ) from s.2).comp hψ
  have heq : (fun x : imO Y => funOfSec s x) = fun x => s (ψ x) := by
    funext x
    rw [funOfSec, dif_pos x.2]
  have hz' : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (funOfSec s) z := by
    have := hs ⟨z, hz⟩
    rw [← heq] at this
    exact contMDiffAt_subtype_iff.1 this
  exact (hz'.contDiffAt.differentiableAt (by simp)).differentiableWithinAt

end Holomorphic

/-! ### Cartan's splitting on blocks of `ℂⁿ` -/

section Splitting

open Filter Topology Set

/-- Cartan's splitting property for a pair of sets: every invertible holomorphic matrix near
`K₁ ∩ K₂` is `g' g''⁻¹` near `K₁ ∩ K₂`, with `g'`, `g''` invertible holomorphic near `K₁`, `K₂`. -/
def SplitProp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (K₁ K₂ : Set V) :
    Prop :=
  ∀ (m : Type) [Fintype m] [DecidableEq m] (g : V → Matrix m m ℂ) (O : Set V), IsOpen O →
    K₁ ∩ K₂ ⊆ O → (∀ i j, DifferentiableOn ℂ (fun z => g z i j) O) → (∀ z ∈ O, IsUnit (g z)) →
    ∃ (O' O'' : Set V) (g' g'' : V → Matrix m m ℂ),
      IsOpen O' ∧ K₁ ⊆ O' ∧ (∀ i j, DifferentiableOn ℂ (fun z => g' z i j) O') ∧
      (∀ z ∈ O', IsUnit (g' z)) ∧
      IsOpen O'' ∧ K₂ ⊆ O'' ∧ (∀ i j, DifferentiableOn ℂ (fun z => g'' z i j) O'') ∧
      (∀ z ∈ O'', IsUnit (g'' z)) ∧
      ∀ᶠ z in 𝓝ˢ (K₁ ∩ K₂), g z = g' z * (g'' z)⁻¹

/-- Cartan's splitting property is preserved under preimage by a continuous linear equivalence. -/
lemma SplitProp.preimage {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] (φ : V ≃L[ℂ] V') {K₁ K₂ : Set V'}
    (h : SplitProp K₁ K₂) : SplitProp (φ ⁻¹' K₁) (φ ⁻¹' K₂) := by
  intro m _ _ g O hO hKO hg hgu
  obtain ⟨O', O'', g', g'', hO', hK₁, hg', hg'u, hO'', hK₂, hg'', hg''u, hev⟩ :=
    h m (g ∘ φ.symm) (φ.symm ⁻¹' O) (hO.preimage φ.symm.continuous)
      (fun w hw => by
        have := hKO (show φ.symm w ∈ φ ⁻¹' K₁ ∩ φ ⁻¹' K₂ by simpa using hw)
        exact this)
      (fun i j => (hg i j).comp φ.symm.differentiableOn (fun w hw => hw))
      (fun w hw => hgu _ hw)
  refine ⟨φ ⁻¹' O', φ ⁻¹' O'', g' ∘ φ, g'' ∘ φ, hO'.preimage φ.continuous,
    fun z hz => hK₁ hz, fun i j => (hg' i j).comp φ.differentiableOn (fun z hz => hz),
    fun z hz => hg'u _ hz, hO''.preimage φ.continuous, fun z hz => hK₂ hz,
    fun i j => (hg'' i j).comp φ.differentiableOn (fun z hz => hz), fun z hz => hg''u _ hz, ?_⟩
  have ht : Tendsto φ (𝓝ˢ (φ ⁻¹' K₁ ∩ φ ⁻¹' K₂)) (𝓝ˢ (K₁ ∩ K₂)) :=
    φ.continuous.tendsto_nhdsSet fun z hz => hz
  filter_upwards [ht.eventually hev] with z hz
  simpa using hz

/-- Cartan's lemma, for a cut `Re zᵢ₀ = t` of a block of `ℂ^ι`. -/
lemma splitProp_re {ι : Type*} [Fintype ι] (x₀ x₁ y₀ y₁ : ι → ℝ)
    (hx : ∀ i, x₀ i ≤ x₁ i) (hy : ∀ i, y₀ i ≤ y₁ i) (i₀ : ι) (t : ℝ) (h₀ : x₀ i₀ < t)
    (h₁ : t < x₁ i₀) :
    SplitProp ((univ.pi fun i => Icc (x₀ i) (x₁ i) ×ℂ Icc (y₀ i) (y₁ i)) ∩ {z | (z i₀).re ≤ t})
      ((univ.pi fun i => Icc (x₀ i) (x₁ i) ×ℂ Icc (y₀ i) (y₁ i)) ∩ {z | t ≤ (z i₀).re}) := by
  intro m _ _ g O hO hKO hg hgu
  exact MMP.Gaga.exists_eq_mul_inv_of_isUnit_of_differentiableOn_block x₀ x₁ y₀ y₁ hx hy _ rfl
    i₀ t h₀ h₁ g O hO hKO hg hgu

variable {n : ℕ}

/-- Cartan's lemma in `ℂⁿ` for a cut `Re zᵢ₀ = t` of a block. -/
lemma splitProp_block_re (a b c d : Fin n → ℝ) (hab : ∀ i, a i ≤ b i)
    (hcd : ∀ i, c i ≤ d i) (i₀ : Fin n) (t : ℝ) (h₀ : a i₀ < t) (h₁ : t < b i₀) :
    SplitProp (block a (Function.update b i₀ t) c d) (block (Function.update a i₀ t) b c d) := by
  let e := EuclideanSpace.equiv (Fin n) ℂ
  have h1 : block a (Function.update b i₀ t) c d = e ⁻¹'
      ((univ.pi fun i => Icc (a i) (b i) ×ℂ Icc (c i) (d i)) ∩ {z | (z i₀).re ≤ t}) := by
    ext z
    rw [mem_block_update_b_iff h₁.le]
    exact ⟨fun ⟨h, h'⟩ => ⟨fun i _ => h i, h'⟩, fun ⟨h, h'⟩ => ⟨fun i => h i (mem_univ _), h'⟩⟩
  have h2 : block (Function.update a i₀ t) b c d = e ⁻¹'
      ((univ.pi fun i => Icc (a i) (b i) ×ℂ Icc (c i) (d i)) ∩ {z | t ≤ (z i₀).re}) := by
    ext z
    rw [mem_block_update_a_iff h₀.le]
    exact ⟨fun ⟨h, h'⟩ => ⟨fun i _ => h i, h'⟩, fun ⟨h, h'⟩ => ⟨fun i => h i (mem_univ _), h'⟩⟩
  rw [h1, h2]
  exact (splitProp_re a b c d hab hcd i₀ t h₀ h₁).preimage e

/-- The rotation `zᵢ₀ ↦ -i zᵢ₀` of `ℂ^ι`, which turns `Im zᵢ₀` into `Re zᵢ₀`. -/
noncomputable def rotI (i₀ : Fin n) : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun w i => if i = i₀ then -Complex.I * w i else w i
      invFun := fun w i => if i = i₀ then Complex.I * w i else w i
      map_add' := fun w w' => by
        ext i; by_cases hi : i = i₀ <;> simp [hi, mul_add]
      map_smul' := fun c w => by
        ext i; by_cases hi : i = i₀ <;> simp [hi]; ring
      left_inv := fun w => by
        ext i; by_cases hi : i = i₀ <;> simp [hi, ← mul_assoc]
      right_inv := fun w => by
        ext i; by_cases hi : i = i₀ <;> simp [hi, ← mul_assoc] }

/-- `rotI i₀` multiplies the `i₀`-th coordinate by `-i` and fixes the others. -/
lemma rotI_apply (i₀ : Fin n) (w : Fin n → ℂ) (i : Fin n) :
    rotI i₀ w i = if i = i₀ then -Complex.I * w i else w i := rfl

/-- The real and imaginary parts of `-i z` are `Im z` and `-Re z`. -/
lemma rot_re_im (z : ℂ) : (-Complex.I * z).re = z.im ∧ (-Complex.I * z).im = -z.re := by
  simp

/-- Cartan's lemma in `ℂⁿ` for a cut `Im zᵢ₀ = t` of a block. -/
lemma splitProp_block_im (a b c d : Fin n → ℝ) (hab : ∀ i, a i ≤ b i)
    (hcd : ∀ i, c i ≤ d i) (i₀ : Fin n) (t : ℝ) (h₀ : c i₀ < t) (h₁ : t < d i₀) :
    SplitProp (block a b c (Function.update d i₀ t)) (block a b (Function.update c i₀ t) d) := by
  let φ := (EuclideanSpace.equiv (Fin n) ℂ).trans (rotI i₀)
  let a' := Function.update a i₀ (c i₀)
  let b' := Function.update b i₀ (d i₀)
  let c' := Function.update c i₀ (-b i₀)
  let d' := Function.update d i₀ (-a i₀)
  have hφ : ∀ z i, φ z i = if i = i₀ then -Complex.I * z i else z i := fun _ _ => rfl
  have hab' : ∀ i, a' i ≤ b' i := by
    intro i; by_cases hi : i = i₀
    · subst hi; simp [a', b', hcd]
    · simp [a', b', Function.update_of_ne hi, hab]
  have hcd' : ∀ i, c' i ≤ d' i := by
    intro i; by_cases hi : i = i₀
    · subst hi; simp [c', d', hab]
    · simp [c', d', Function.update_of_ne hi, hcd]
  have coordA : ∀ (z : EuclideanSpace ℂ (Fin n)) (i : Fin n),
      φ z i ∈ Icc (a' i) (b' i) ×ℂ Icc (c' i) (d' i) ↔
        z i ∈ Icc (a i) (b i) ×ℂ Icc (c i) (d i) := by
    intro z i
    rw [hφ]
    by_cases hi : i = i₀
    · subst hi
      simp only [if_true, Complex.mem_reProdIm, mem_Icc, (rot_re_im _).1, (rot_re_im _).2,
        a', b', c', d', Function.update_self]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨by linarith, by linarith⟩, h1, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨h3, h4⟩, by linarith, by linarith⟩
    · simp only [hi, if_false, a', b', c', d', Function.update_of_ne hi]
  have coordB : ∀ z : EuclideanSpace ℂ (Fin n), (φ z i₀).re = (z i₀).im := by
    intro z; rw [hφ, if_pos rfl, (rot_re_im _).1]
  have hd : ∀ z : EuclideanSpace ℂ (Fin n), z ∈ block a b c (Function.update d i₀ t) ↔
      (∀ i, z i ∈ Icc (a i) (b i) ×ℂ Icc (c i) (d i)) ∧ (z i₀).im ≤ t :=
    fun _ => mem_block_update_d_iff h₁.le
  have hc : ∀ z : EuclideanSpace ℂ (Fin n), z ∈ block a b (Function.update c i₀ t) d ↔
      (∀ i, z i ∈ Icc (a i) (b i) ×ℂ Icc (c i) (d i)) ∧ t ≤ (z i₀).im :=
    fun _ => mem_block_update_c_iff h₀.le
  have h1 : block a b c (Function.update d i₀ t) = φ ⁻¹'
      ((univ.pi fun i => Icc (a' i) (b' i) ×ℂ Icc (c' i) (d' i)) ∩ {z | (z i₀).re ≤ t}) := by
    ext z
    rw [hd]
    simp only [mem_preimage, mem_inter_iff, Set.mem_pi, mem_univ, true_implies, mem_setOf_eq,
      coordA, coordB]
  have h2 : block a b (Function.update c i₀ t) d = φ ⁻¹'
      ((univ.pi fun i => Icc (a' i) (b' i) ×ℂ Icc (c' i) (d' i)) ∩ {z | t ≤ (z i₀).re}) := by
    ext z
    rw [hc]
    simp only [mem_preimage, mem_inter_iff, Set.mem_pi, mem_univ, true_implies, mem_setOf_eq,
      coordA, coordB]
  rw [h1, h2]
  exact (splitProp_re a' b' c' d' hab' hcd' i₀ t (by simpa [a'] using h₀)
    (by simpa [b'] using h₁)).preimage φ

section Inverse

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- A finite product of functions holomorphic on `O` is holomorphic on `O`. -/
lemma differentiableOn_finset_prod {ι : Type*} (s : Finset ι) {f : ι → V → ℂ}
    {O : Set V} (hf : ∀ i, DifferentiableOn ℂ (f i) O) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) O := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a).mul ih

/-- The determinant of a matrix of functions holomorphic on `O` is holomorphic on `O`. -/
lemma differentiableOn_det {m : Type*} [Fintype m] [DecidableEq m]
    {g : V → Matrix m m ℂ} {O : Set V}
    (hg : ∀ i j, DifferentiableOn ℂ (fun z => g z i j) O) :
    DifferentiableOn ℂ (fun z => (g z).det) O := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  refine DifferentiableOn.const_smul ?_ _
  exact differentiableOn_finset_prod _ fun i => hg _ _

/-- The entries of the pointwise inverse of a pointwise invertible matrix of functions
holomorphic on `O` are holomorphic on `O`. -/
lemma differentiableOn_inv {m : Type*} [Fintype m] [DecidableEq m]
    {g : V → Matrix m m ℂ} {O : Set V}
    (hg : ∀ i j, DifferentiableOn ℂ (fun z => g z i j) O) (hu : ∀ z ∈ O, IsUnit (g z)) :
    ∀ i j, DifferentiableOn ℂ (fun z => (g z)⁻¹ i j) O := by
  intro i j
  have hdet : DifferentiableOn ℂ (fun z => (g z).det) O := differentiableOn_det hg
  have hadj : DifferentiableOn ℂ (fun z => (g z).adjugate i j) O := by
    simp only [Matrix.adjugate_apply]
    refine differentiableOn_det fun k l => ?_
    by_cases hk : k = j
    · subst hk; simp only [Matrix.updateRow_self]; exact differentiableOn_const _
    · simp only [Matrix.updateRow_ne hk]; exact hg k l
  have heq : ∀ z ∈ O, (g z)⁻¹ i j = ((g z).det)⁻¹ * (g z).adjugate i j := by
    intro z hz
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  refine (DifferentiableOn.mul (hdet.inv fun z hz => ?_) hadj).congr heq
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (hu z hz)).ne_zero

end Inverse

end Splitting

/-! ### Inverse images along open embeddings -/

section InverseImage

variable {X : TopCat.{0}}

/-- The inclusion of opens `P ≤ W'` is an open embedding. -/
lemma isOpenEmbedding_inclusion {P W' : Opens X} (h : P ≤ W') :
    Topology.IsOpenEmbedding (TopCat.ofHom (X := TopCat.of P) (Y := TopCat.of W')
      ⟨Set.inclusion h, by fun_prop⟩) :=
  Topology.IsOpenEmbedding.of_comp _ W'.isOpenEmbedding' P.isOpenEmbedding'

/-- The inverse image along `P ⊆ W' ⊆ X` is the inverse image along `P ⊆ X`. -/
noncomputable def pullbackPullbackIso (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {P W' : Opens X} (h : P ≤ W') :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (TopCat.ofHom (X := TopCat.of P) (Y := TopCat.of W')
      ⟨Set.inclusion h, by fun_prop⟩)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' W')).obj F) ≅
      (P.isOpenEmbedding.sheafPullback AddCommGrpCat.{0}).obj F := by
  let hi := isOpenEmbedding_inclusion h
  refine ((hi.sheafPullbackIso AddCommGrpCat.{0}).app _) ≪≫
    (hi.sheafPullback AddCommGrpCat.{0}).mapIso
      ((W'.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{0}).app F) ≪≫ ?_
  have hV : ∀ V : Opens (TopCat.of P),
      W'.isOpenEmbedding.functor.obj (hi.functor.obj V) = P.isOpenEmbedding.functor.obj V := by
    intro V
    ext x
    simp only [IsOpenMap.coe_functor_obj, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
    (fun V => F.obj.mapIso (eqToIso (hV V.unop).symm).op) ?_)
  intro V₁ V₂ f
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  rfl

end InverseImage

/-! ### Sections of restrictions -/

section Sections2

variable {X : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

/-- Restriction of sections of `M|_B` to sections of `M|_A`, for `A ≤ B ≤ V`. -/
noncomputable def resΓ {V A B : Opens X} (hA : A ≤ V) (hB : B ≤ V) (hAB : A ≤ B)
    (M : SheafOfModules.{0} (R.over V)) (m : Γ ((res R hB).obj M)) : Γ ((res R hA).obj M) :=
  (resResIso hAB hB hA M).hom.val.app _ (rΓ hAB _ m)

/-- `resΓ` is semilinear along the restriction of functions `rR`. -/
lemma resΓ_smul {V A B : Opens X} (hA : A ≤ V) (hB : B ≤ V) (hAB : A ≤ B)
    (M : SheafOfModules.{0} (R.over V)) (a : (R.over B).obj.obj (op (topOver B)))
    (m : Γ ((res R hB).obj M)) :
    resΓ hA hB hAB M (a • m) = rR hAB a • resΓ hA hB hAB M m := by
  rw [resΓ, rΓ_smul, map_smul]
  rfl

/-- `resΓ` is additive. -/
lemma resΓ_add {V A B : Opens X} (hA : A ≤ V) (hB : B ≤ V) (hAB : A ≤ B)
    (M : SheafOfModules.{0} (R.over V)) (m m' : Γ ((res R hB).obj M)) :
    resΓ hA hB hAB M (m + m') = resΓ hA hB hAB M m + resΓ hA hB hAB M m' := by
  rw [resΓ, rΓ_add, map_add]
  rfl

/-- `resΓ` sends `0` to `0`. -/
lemma resΓ_zero {V A B : Opens X} (hA : A ≤ V) (hB : B ≤ V) (hAB : A ≤ B)
    (M : SheafOfModules.{0} (R.over V)) : resΓ hA hB hAB M 0 = 0 := by
  simp only [resΓ, rΓ, map_zero]
  exact map_zero _

/-- `resΓ` commutes with finite sums. -/
lemma resΓ_sum {V A B : Opens X} (hA : A ≤ V) (hB : B ≤ V) (hAB : A ≤ B)
    (M : SheafOfModules.{0} (R.over V)) {ι : Type*} (s : Finset ι) (m : ι → Γ ((res R hB).obj M)) :
    resΓ hA hB hAB M (∑ i ∈ s, m i) = ∑ i ∈ s, resΓ hA hB hAB M (m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using resΓ_zero hA hB hAB M
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, resΓ_add, ih]

/-- Restricting with `resΓ` from `C` to `B` and then to `A` is restricting from `C` to `A`. -/
lemma resΓ_resΓ {V A B C : Opens X} (hA : A ≤ V) (hB : B ≤ V) (hC : C ≤ V)
    (hAB : A ≤ B) (hBC : B ≤ C) (M : SheafOfModules.{0} (R.over V)) (m : Γ ((res R hC).obj M)) :
    resΓ hA hB hAB M (resΓ hB hC hBC M m) = resΓ hA hC (hAB.trans hBC) M m := by
  simp only [resΓ, resResIso_hom_app, rΓ]
  have key := PresheafOfModules.map_comp_apply M.val
    ((Over.map (homOfLE hC)).map (toTopOver ((Over.map (homOfLE hBC)).obj (topOver B)))).op
    ((Over.map (homOfLE hB)).map
      (toTopOver ((Over.map (homOfLE hAB)).obj (topOver A)))).op
    (show M.val.obj (op ((Over.map (homOfLE hC)).obj (topOver C))) from m)
  refine key.symm.trans ?_
  congr 2

/-- Restricting a combination of restrictions with `resΓ` restricts its coefficients with `rR`. -/
lemma resΓ_sum_smul_resΓ {V A B C : Opens X} (hA : A ≤ V) (hB : B ≤ V) (hC : C ≤ V)
    (hAB : A ≤ B) (hBC : B ≤ C) (M : SheafOfModules.{0} (R.over V)) {ι : Type*} [Fintype ι]
    (u : ι → (R.over B).obj.obj (op (topOver B))) (m : ι → Γ ((res R hC).obj M)) :
    resΓ hA hB hAB M (∑ y, u y • resΓ hB hC hBC M (m y)) =
      ∑ y, rR hAB (u y) • resΓ hA hC (hAB.trans hBC) M (m y) :=
  (resΓ_sum _ _ _ M _ _).trans (Finset.sum_congr rfl fun _ _ =>
    (resΓ_smul _ _ _ M _ _).trans (congrArg _ (resΓ_resΓ _ _ _ _ _ M _)))

/-- `resΓ` commutes with morphisms of sheaves of modules. -/
lemma resΓ_naturality {V A B : Opens X} (hA : A ≤ V) (hB : B ≤ V) (hAB : A ≤ B)
    {M N : SheafOfModules.{0} (R.over V)} (f : M ⟶ N) (m : Γ ((res R hB).obj M)) :
    ((res R hA).map f).val.app _ (resΓ hA hB hAB M m) =
      resΓ hA hB hAB N (((res R hB).map f).val.app _ m) :=
  PresheafOfModules.naturality_apply f.val
    ((Over.map (homOfLE hB)).map (toTopOver ((Over.map (homOfLE hAB)).obj (topOver A)))).op
    (show M.val.obj (op ((Over.map (homOfLE hB)).obj (topOver B))) from m)

/-- **Restriction of `ofTop` across nested restrictions.** Restricting `ofTop s` from `B` to `A`,
through `freeRes` and `resResIso`, is `ofTop` of the sections `resΓ hA hB hAB M (s i)`. -/
lemma ofTop_res {V A B : Opens X} (hA : A ≤ V) (hB : B ≤ V) (hAB : A ≤ B)
    (M : SheafOfModules.{0} (R.over V)) {I : Type} (s : I → Γ ((res R hB).obj M)) :
    (freeRes hAB I).hom ≫ (res R hAB).map (ofTop s) ≫ (resResIso hAB hB hA M).hom =
      ofTop (fun i => resΓ hA hB hAB M (s i)) := by
  rw [← Category.assoc, freeRes_hom_comp_res_map_ofTop, ofTop_comp]
  rfl

end Sections2

/-! ### Evaluating holomorphic functions -/

section Evaluation

variable {n : ℕ} {U : Opens (EuclideanSpace ℂ (Fin n))}

/-- Evaluation at a point of the holomorphic functions on `T`. -/
noncomputable def evO {T : Opens (TopCat.of U)} (y : T) :
    ((holomorphicRingCatSheaf n U).over T).obj.obj (op (topOver T)) →+* ℂ where
  toFun a := (show 𝒪[n, U].presheaf.obj (op T) from a) y
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Evaluating the restriction of a function at `y` is evaluating the function at `y`. -/
lemma evO_rR {T T' : Opens (TopCat.of U)} (h : T' ≤ T)
    (a : ((holomorphicRingCatSheaf n U).over T).obj.obj (op (topOver T))) (y : T') :
    evO y (rR h a) = evO ⟨y.1, h y.2⟩ a := rfl

/-- Holomorphic functions on `T` with equal values at every point are equal. -/
lemma ext_evO {T : Opens (TopCat.of U)}
    {a b : ((holomorphicRingCatSheaf n U).over T).obj.obj (op (topOver T))}
    (h : ∀ y : T, evO y a = evO y b) : a = b :=
  ContMDiffMap.ext h

/-- Matrices of holomorphic functions on `T` with equal values at every point are equal. -/
lemma matrix_ext_evO {T : Opens (TopCat.of U)} {I J : Type}
    {A B : Matrix I J (((holomorphicRingCatSheaf n U).over T).obj.obj (op (topOver T)))}
    (h : ∀ y : T, A.map (evO y) = B.map (evO y)) : A = B := by
  ext i j
  exact ext_evO fun y => congrFun (congrFun (h y) i) j

/-- A function holomorphic near the image of `T` in `ℂⁿ`, as a holomorphic function on `T`. -/
noncomputable def hol {T : Opens (TopCat.of U)} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (O : Set (EuclideanSpace ℂ (Fin n))) (hO : IsOpen O) (hF : DifferentiableOn ℂ F O)
    (hT : ∀ y : T, ((y : U) : EuclideanSpace ℂ (Fin n)) ∈ O) :
    ((holomorphicRingCatSheaf n U).over T).obj.obj (op (topOver T)) :=
  secOfFun T F O hO hF hT

/-- A holomorphic function on `T`, as a function on `ℂⁿ`. -/
noncomputable def fn {T : Opens (TopCat.of U)}
    (a : ((holomorphicRingCatSheaf n U).over T).obj.obj (op (topOver T))) :
    EuclideanSpace ℂ (Fin n) → ℂ :=
  funOfSec (Y := T) (show 𝒪[n, U].presheaf.obj (op T) from a)

/-- `fn a` agrees with `a` on `T`. -/
lemma fn_apply {T : Opens (TopCat.of U)}
    (a : ((holomorphicRingCatSheaf n U).over T).obj.obj (op (topOver T))) (y : T) :
    fn a ((y : U) : EuclideanSpace ℂ (Fin n)) = evO y a :=
  funOfSec_apply _ y

/-- `fn a` is holomorphic on `imO T`. -/
lemma differentiableOn_fn {T : Opens (TopCat.of U)}
    (a : ((holomorphicRingCatSheaf n U).over T).obj.obj (op (topOver T))) :
    DifferentiableOn ℂ (fn a) (imO T) :=
  differentiableOn_funOfSec _

end Evaluation

/-! ### Splitting a transition matrix of sections -/

section SplitSections

open Filter Topology
open scoped Matrix

variable {n : ℕ} {U : Opens (EuclideanSpace ℂ (Fin n))}

/-- A point of `U` whose image in `ℂⁿ` lies in `imO Y` lies in `Y`. -/
lemma mem_of_mem_imO' {Y : Opens (TopCat.of U)} {x : U}
    (hx : (x : EuclideanSpace ℂ (Fin n)) ∈ imO Y) : x ∈ Y := by
  obtain ⟨w, hw, hwx⟩ := hx
  rw [← Subtype.ext hwx]
  exact hw

/-- Pointwise transposes of `g` and of `g⁻¹`, for `g` pointwise invertible, are inverse. -/
lemma mul_eq_one_of_evO {T : Opens (TopCat.of U)} {I : Type} [Fintype I] [DecidableEq I]
    {A A' : Matrix I I (((holomorphicRingCatSheaf n U).over T).obj.obj (op (topOver T)))}
    {g : EuclideanSpace ℂ (Fin n) → Matrix I I ℂ}
    (hA : ∀ y : T, A.map (evO y) = (g ((y : U) : EuclideanSpace ℂ (Fin n)))ᵀ)
    (hA' : ∀ y : T, A'.map (evO y) = ((g ((y : U) : EuclideanSpace ℂ (Fin n)))⁻¹)ᵀ)
    (hu : ∀ y : T, IsUnit (g ((y : U) : EuclideanSpace ℂ (Fin n)))) :
    A * A' = 1 ∧ A' * A = 1 := by
  refine ⟨matrix_ext_evO fun y => ?_, matrix_ext_evO fun y => ?_⟩
  · rw [Matrix.map_mul, hA, hA', ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).1 (hu y)), Matrix.transpose_one, Matrix.map_one _
      (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, hA, hA', ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (hu y)), Matrix.transpose_one, Matrix.map_one _
      (map_zero _) (map_one _)]

/-- The splitting relation `g = g₁ g₂⁻¹`, read on matrices of holomorphic functions. -/
lemma map_rR_mul_map_rR_eq {T₁ T₂ B : Opens (TopCat.of U)} (hT₁₂ : T₁ ⊓ T₂ ≤ B)
    {I : Type} [Fintype I] [DecidableEq I]
    (G : Matrix I I (((holomorphicRingCatSheaf n U).over B).obj.obj (op (topOver B))))
    (U₁ : Matrix I I (((holomorphicRingCatSheaf n U).over T₁).obj.obj (op (topOver T₁))))
    (U₂ : Matrix I I (((holomorphicRingCatSheaf n U).over T₂).obj.obj (op (topOver T₂))))
    {g g₁ g₂ : EuclideanSpace ℂ (Fin n) → Matrix I I ℂ}
    (hG : ∀ y : B, G.map (evO y) = (g ((y : U) : EuclideanSpace ℂ (Fin n)))ᵀ)
    (hU₁ : ∀ y : T₁, U₁.map (evO y) = (g₁ ((y : U) : EuclideanSpace ℂ (Fin n)))ᵀ)
    (hU₂ : ∀ y : T₂, U₂.map (evO y) = (g₂ ((y : U) : EuclideanSpace ℂ (Fin n)))ᵀ)
    (hu₂ : ∀ y : T₂, IsUnit (g₂ ((y : U) : EuclideanSpace ℂ (Fin n))))
    (hrel : ∀ y : (T₁ ⊓ T₂ : Opens (TopCat.of U)), g ((y : U) : EuclideanSpace ℂ (Fin n)) =
      g₁ ((y : U) : EuclideanSpace ℂ (Fin n)) * (g₂ ((y : U) : EuclideanSpace ℂ (Fin n)))⁻¹) :
    U₂.map (rR (inf_le_right : T₁ ⊓ T₂ ≤ T₂)) * G.map (rR hT₁₂) =
      U₁.map (rR (inf_le_left : T₁ ⊓ T₂ ≤ T₁)) := by
  refine matrix_ext_evO fun y => ?_
  have e1 : (evO y) ∘ (rR (inf_le_right : T₁ ⊓ T₂ ≤ T₂)) = evO (⟨y.1, y.2.2⟩ : T₂) :=
    funext fun a => evO_rR _ a y
  have e2 : (evO y) ∘ (rR hT₁₂) = evO (⟨y.1, hT₁₂ y.2⟩ : B) := funext fun a => evO_rR _ a y
  have e3 : (evO y) ∘ (rR (inf_le_left : T₁ ⊓ T₂ ≤ T₁)) = evO (⟨y.1, y.2.1⟩ : T₁) :=
    funext fun a => evO_rR _ a y
  rw [Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map, e1, e2, e3,
    hU₂ ⟨y.1, y.2.2⟩, hG ⟨y.1, hT₁₂ y.2⟩, hU₁ ⟨y.1, y.2.1⟩, ← Matrix.transpose_mul, hrel y,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1
      (hu₂ ⟨y.1, y.2.2⟩)), Matrix.mul_one]

/-- **Cartan's splitting on thickenings** of `K₁`, `K₂` inside open sets `W₁`, `W₂`. -/
lemma exists_split_thickening {K₁ K₂ : Set (EuclideanSpace ℂ (Fin n))} (hsplit : SplitProp K₁ K₂)
    (hc₁ : IsCompact K₁) (hc₂ : IsCompact K₂) {I : Type} [Fintype I] [DecidableEq I]
    (g : EuclideanSpace ℂ (Fin n) → Matrix I I ℂ) {O W₁ W₂ : Set (EuclideanSpace ℂ (Fin n))}
    (hO : IsOpen O) (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂) (hL : K₁ ∩ K₂ ⊆ O) (hK₁ : K₁ ⊆ W₁)
    (hK₂ : K₂ ⊆ W₂) (hg : ∀ x y, DifferentiableOn ℂ (fun z => g z x y) O)
    (hgu : ∀ z ∈ O, IsUnit (g z)) :
    ∃ (η : ℝ) (O₁ O₂ : Set (EuclideanSpace ℂ (Fin n)))
      (g₁ g₂ : EuclideanSpace ℂ (Fin n) → Matrix I I ℂ), 0 < η ∧
      IsOpen O₁ ∧ (∀ x y, DifferentiableOn ℂ (fun z => g₁ z x y) O₁) ∧ (∀ z ∈ O₁, IsUnit (g₁ z)) ∧
      IsOpen O₂ ∧ (∀ x y, DifferentiableOn ℂ (fun z => g₂ z x y) O₂) ∧ (∀ z ∈ O₂, IsUnit (g₂ z)) ∧
      Metric.thickening η K₁ ⊆ O₁ ∩ W₁ ∧ Metric.thickening η K₂ ⊆ O₂ ∩ W₂ ∧
      ∀ z ∈ Metric.thickening η K₁ ∩ Metric.thickening η K₂, z ∈ O ∧ g z = g₁ z * (g₂ z)⁻¹ := by
  obtain ⟨O₁, O₂, g₁, g₂, hO₁, hKO₁, hg₁, hg₁u, hO₂, hKO₂, hg₂, hg₂u, hev⟩ :=
    hsplit I g O hO hL hg hgu
  obtain ⟨N, hN, hLN, hNev⟩ := mem_nhdsSet_iff_exists.1 hev
  obtain ⟨η₀, hη₀, hη₀s⟩ := exists_thickening_inter_thickening_subset hc₁ hc₂ (hN.inter hO)
    (fun z hz => ⟨hLN hz, hL hz⟩)
  obtain ⟨η₁, hη₁, hη₁s⟩ :=
    hc₁.exists_thickening_subset_open (hO₁.inter hW₁) fun z hz => ⟨hKO₁ hz, hK₁ hz⟩
  obtain ⟨η₂, hη₂, hη₂s⟩ :=
    hc₂.exists_thickening_subset_open (hO₂.inter hW₂) fun z hz => ⟨hKO₂ hz, hK₂ hz⟩
  refine ⟨min η₀ (min η₁ η₂), O₁, O₂, g₁, g₂, lt_min hη₀ (lt_min hη₁ hη₂), hO₁, hg₁, hg₁u, hO₂,
    hg₂, hg₂u, (Metric.thickening_mono ((min_le_right _ _).trans (min_le_left _ _)) _).trans hη₁s,
    (Metric.thickening_mono ((min_le_right _ _).trans (min_le_right _ _)) _).trans hη₂s,
    fun z hz => (fun h => ⟨h.2, hNev h.1⟩) (hη₀s ⟨Metric.thickening_mono (min_le_left _ _) _ hz.1,
      Metric.thickening_mono (min_le_left _ _) _ hz.2⟩)⟩

/-- **Cartan's splitting, for sections.** An invertible matrix `G` of holomorphic functions on a
neighbourhood `B` of `K₁ ∩ K₂` factors as `G = U₂⁻¹ U₁` near `K₁ ∩ K₂`, with `U₁`, `U₂` invertible
matrices of holomorphic functions on neighbourhoods `T₁`, `T₂` of `K₁`, `K₂` whose intersection
lies in `B`. -/
lemma exists_split_sections {K₁ K₂ : Set (EuclideanSpace ℂ (Fin n))}
    (hsplit : SplitProp K₁ K₂) (hKU : K₁ ∪ K₂ ⊆ U) (hc₁ : IsCompact K₁) (hc₂ : IsCompact K₂)
    {B W₁ W₂ : Opens (TopCat.of U)} (hK₁ : (Subtype.val : U → _) ⁻¹' K₁ ⊆ W₁)
    (hK₂ : (Subtype.val : U → _) ⁻¹' K₂ ⊆ W₂) (hLB : (Subtype.val : U → _) ⁻¹' (K₁ ∩ K₂) ⊆ B)
    {I : Type} [Fintype I] [DecidableEq I]
    (G H : Matrix I I (((holomorphicRingCatSheaf n U).over B).obj.obj (op (topOver B))))
    (hGH : G * H = 1) (hHG : H * G = 1) :
    ∃ (T₁ T₂ : Opens (TopCat.of U)) (hT₁ : T₁ ≤ W₁) (hT₂ : T₂ ≤ W₂) (hT₁₂ : T₁ ⊓ T₂ ≤ B)
      (U₁ U₁' : Matrix I I (((holomorphicRingCatSheaf n U).over T₁).obj.obj (op (topOver T₁))))
      (U₂ U₂' : Matrix I I (((holomorphicRingCatSheaf n U).over T₂).obj.obj (op (topOver T₂)))),
      (Subtype.val : U → _) ⁻¹' K₁ ⊆ T₁ ∧ (Subtype.val : U → _) ⁻¹' K₂ ⊆ T₂ ∧
      U₁ * U₁' = 1 ∧ U₁' * U₁ = 1 ∧ U₂ * U₂' = 1 ∧ U₂' * U₂ = 1 ∧
      U₂.map (rR (inf_le_right : T₁ ⊓ T₂ ≤ T₂)) * G.map (rR hT₁₂) =
        U₁.map (rR (inf_le_left : T₁ ⊓ T₂ ≤ T₁)) := by
  classical
  let O : Set (EuclideanSpace ℂ (Fin n)) := imO B
  have hL : K₁ ∩ K₂ ⊆ O := subset_imO (fun _ hz => hKU (Or.inl hz.1)) hLB
  let g : EuclideanSpace ℂ (Fin n) → Matrix I I ℂ := fun z => Matrix.of fun x y => fn (G y x) z
  let h : EuclideanSpace ℂ (Fin n) → Matrix I I ℂ := fun z => Matrix.of fun x y => fn (H y x) z
  have hgO : ∀ y : B, g ((y : U) : EuclideanSpace ℂ (Fin n)) = (G.map (evO y))ᵀ := by
    intro y; ext x w; exact fn_apply _ y
  have hhO : ∀ y : B, h ((y : U) : EuclideanSpace ℂ (Fin n)) = (H.map (evO y))ᵀ := by
    intro y; ext x w; exact fn_apply _ y
  have hgu : ∀ z ∈ O, IsUnit (g z) := by
    rintro z ⟨y, hy, rfl⟩
    refine ⟨⟨g (y : U), h (y : U), ?_, ?_⟩, rfl⟩ <;>
      rw [hgO ⟨y, hy⟩, hhO ⟨y, hy⟩, ← Matrix.transpose_mul, ← Matrix.map_mul] <;>
      simp only [hHG, hGH, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hg : ∀ x y, DifferentiableOn ℂ (fun z => g z x y) O := fun x y => differentiableOn_fn (G y x)
  have hK₁O : K₁ ⊆ imO W₁ := subset_imO (fun _ hz => hKU (Or.inl hz)) hK₁
  have hK₂O : K₂ ⊆ imO W₂ := subset_imO (fun _ hz => hKU (Or.inr hz)) hK₂
  obtain ⟨η, O₁, O₂, g₁, g₂, hη, hO₁, hg₁, hg₁u, hO₂, hg₂, hg₂u, hS₁, hS₂, hS₁₂⟩ :=
    exists_split_thickening hsplit hc₁ hc₂ g (imO B).isOpen (imO W₁).isOpen (imO W₂).isOpen hL hK₁O
      hK₂O hg hgu
  let T₁ : Opens (TopCat.of U) := ⟨Subtype.val ⁻¹' Metric.thickening η K₁,
    Metric.isOpen_thickening.preimage continuous_subtype_val⟩
  let T₂ : Opens (TopCat.of U) := ⟨Subtype.val ⁻¹' Metric.thickening η K₂,
    Metric.isOpen_thickening.preimage continuous_subtype_val⟩
  have hT₁ : T₁ ≤ W₁ := fun x hx => mem_of_mem_imO' (hS₁ hx).2
  have hT₂ : T₂ ≤ W₂ := fun x hx => mem_of_mem_imO' (hS₂ hx).2
  have hT₁₂ : T₁ ⊓ T₂ ≤ B := fun x hx => mem_of_mem_imO' (hS₁₂ _ ⟨hx.1, hx.2⟩).1
  have hy₁ : ∀ y : T₁, ((y : U) : EuclideanSpace ℂ (Fin n)) ∈ O₁ := fun y => (hS₁ y.2).1
  have hy₂ : ∀ y : T₂, ((y : U) : EuclideanSpace ℂ (Fin n)) ∈ O₂ := fun y => (hS₂ y.2).1
  let U₁ : Matrix I I (((holomorphicRingCatSheaf n U).over T₁).obj.obj (op (topOver T₁))) :=
    Matrix.of fun x y => hol (fun z => g₁ z y x) O₁ hO₁ (hg₁ y x) hy₁
  let U₁' : Matrix I I (((holomorphicRingCatSheaf n U).over T₁).obj.obj (op (topOver T₁))) :=
    Matrix.of fun x y => hol (fun z => (g₁ z)⁻¹ y x) O₁ hO₁ (differentiableOn_inv hg₁ hg₁u y x) hy₁
  let U₂ : Matrix I I (((holomorphicRingCatSheaf n U).over T₂).obj.obj (op (topOver T₂))) :=
    Matrix.of fun x y => hol (fun z => g₂ z y x) O₂ hO₂ (hg₂ y x) hy₂
  let U₂' : Matrix I I (((holomorphicRingCatSheaf n U).over T₂).obj.obj (op (topOver T₂))) :=
    Matrix.of fun x y => hol (fun z => (g₂ z)⁻¹ y x) O₂ hO₂ (differentiableOn_inv hg₂ hg₂u y x) hy₂
  have hU₁ : ∀ y : T₁, U₁.map (evO y) = (g₁ ((y : U) : EuclideanSpace ℂ (Fin n)))ᵀ :=
    fun y => by ext x w; rfl
  have hU₂ : ∀ y : T₂, U₂.map (evO y) = (g₂ ((y : U) : EuclideanSpace ℂ (Fin n)))ᵀ :=
    fun y => by ext x w; rfl
  have e12 := mul_eq_one_of_evO (A' := U₁') hU₁ (fun y => by ext x w; rfl) (hg₁u _ <| hy₁ ·)
  have e34 := mul_eq_one_of_evO (A' := U₂') hU₂ (fun y => by ext x w; rfl) (hg₂u _ <| hy₂ ·)
  refine ⟨T₁, T₂, hT₁, hT₂, hT₁₂, U₁, U₁', U₂, U₂', fun x hx =>
    Metric.self_subset_thickening hη _ hx, fun x hx => Metric.self_subset_thickening hη _ hx,
    e12.1, e12.2, e34.1, e34.2, ?_⟩
  refine map_rR_mul_map_rR_eq hT₁₂ G U₁ U₂ (g := g)
    (fun y => by rw [hgO y, Matrix.transpose_transpose]) hU₁ hU₂ (fun y => hg₂u _ (hy₂ y))
    fun y => (hS₁₂ _ ⟨y.2.1, y.2.2⟩).2

/-- `∑ y, u y • ∑ w, g y w • v w = ∑ w, (∑ y, u y * g y w) • v w`. -/
lemma sum_smul_sum {S N : Type*} [Semiring S] [AddCommMonoid N] [Module S N] {ι : Type*}
    [Fintype ι] (u : ι → S) (g : ι → ι → S) (v : ι → N) :
    ∑ y, u y • ∑ w, g y w • v w = ∑ w, (∑ y, u y * g y w) • v w := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- **Gluing twisted tuples of sections.** Given tuples `s₁`, `s₂` of sections of `M` near `K₁`
and near `K₂`, related near `K₁ ∩ K₂` by an invertible holomorphic matrix `G`, there are
invertible holomorphic matrices `U₁`, `U₂` near `K₁`, `K₂` such that the tuples `U₁ s₁` and
`U₂ s₂` glue to a tuple of sections over a neighbourhood `T₁ ∪ T₂` of `K₁ ∪ K₂`. -/
lemma exists_glue_tuple {K₁ K₂ : Set (EuclideanSpace ℂ (Fin n))}
    (hsplit : SplitProp K₁ K₂) (hKU : K₁ ∪ K₂ ⊆ U) (hc₁ : IsCompact K₁) (hc₂ : IsCompact K₂)
    {V W₁ W₂ B : Opens (TopCat.of U)} (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V) (hB₁ : B ≤ W₁)
    (hB₂ : B ≤ W₂) (hK₁ : (Subtype.val : U → _) ⁻¹' K₁ ⊆ W₁)
    (hK₂ : (Subtype.val : U → _) ⁻¹' K₂ ⊆ W₂) (hLB : (Subtype.val : U → _) ⁻¹' (K₁ ∩ K₂) ⊆ B)
    (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V))
    {I : Type} [Fintype I] [DecidableEq I]
    (s₁ : I → Γ ((res _ h₁).obj M)) (s₂ : I → Γ ((res _ h₂).obj M))
    (G H : Matrix I I (((holomorphicRingCatSheaf n U).over B).obj.obj (op (topOver B))))
    (hGH : G * H = 1) (hHG : H * G = 1)
    (hBV : B ≤ V)
    (hrel : ∀ x, resΓ hBV h₂ hB₂ M (s₂ x) = ∑ y, G x y • resΓ hBV h₁ hB₁ M (s₁ y)) :
    ∃ (T₁ T₂ : Opens (TopCat.of U)) (hT₁ : T₁ ≤ W₁) (hT₂ : T₂ ≤ W₂)
      (U₁ U₁' : Matrix I I (((holomorphicRingCatSheaf n U).over T₁).obj.obj (op (topOver T₁))))
      (U₂ U₂' : Matrix I I (((holomorphicRingCatSheaf n U).over T₂).obj.obj (op (topOver T₂)))),
      (Subtype.val : U → _) ⁻¹' K₁ ⊆ T₁ ∧ (Subtype.val : U → _) ⁻¹' K₂ ⊆ T₂ ∧
      U₁ * U₁' = 1 ∧ U₁' * U₁ = 1 ∧ U₂ * U₂' = 1 ∧ U₂' * U₂ = 1 ∧
      ∃ τ : I → Γ ((res _ (sup_le (hT₁.trans h₁) (hT₂.trans h₂))).obj M),
        (∀ x, resΓ (hT₁.trans h₁) (sup_le (hT₁.trans h₁) (hT₂.trans h₂)) le_sup_left M (τ x) =
          ∑ y, U₁ x y • resΓ (hT₁.trans h₁) h₁ hT₁ M (s₁ y)) ∧
        (∀ x, resΓ (hT₂.trans h₂) (sup_le (hT₁.trans h₁) (hT₂.trans h₂)) le_sup_right M (τ x) =
          ∑ y, U₂ x y • resΓ (hT₂.trans h₂) h₂ hT₂ M (s₂ y)) := by
  obtain ⟨T₁, T₂, hT₁, hT₂, hT₁₂, U₁, U₁', U₂, U₂', hK₁T, hK₂T, e1, e2, e3, e4, hU⟩ :=
    exists_split_sections hsplit hKU hc₁ hc₂ hK₁ hK₂ hLB G H hGH hHG
  have hT : T₁ ⊔ T₂ ≤ V := sup_le (hT₁.trans h₁) (hT₂.trans h₂)
  have hT₁V : T₁ ≤ V := hT₁.trans h₁
  have hT₂V : T₂ ≤ V := hT₂.trans h₂
  have hT₁₂V : T₁ ⊓ T₂ ≤ V := inf_le_left.trans hT₁V
  let τ₁ : I → Γ ((res _ hT₁V).obj M) := fun x => ∑ y, U₁ x y • resΓ hT₁V h₁ hT₁ M (s₁ y)
  let τ₂ : I → Γ ((res _ hT₂V).obj M) := fun x => ∑ y, U₂ x y • resΓ hT₂V h₂ hT₂ M (s₂ y)
  have r₁ : ∀ x, resΓ hT₁₂V hT₁V (inf_le_left : T₁ ⊓ T₂ ≤ T₁) M (τ₁ x) =
      ∑ y, rR (inf_le_left : T₁ ⊓ T₂ ≤ T₁) (U₁ x y) •
        resΓ hT₁₂V h₁ ((inf_le_left : T₁ ⊓ T₂ ≤ T₁).trans hT₁) M (s₁ y) := fun _ =>
    resΓ_sum_smul_resΓ _ _ _ _ _ M _ _
  have r₂ : ∀ x, resΓ hT₁₂V hT₂V (inf_le_right : T₁ ⊓ T₂ ≤ T₂) M (τ₂ x) =
      ∑ y, rR (inf_le_right : T₁ ⊓ T₂ ≤ T₂) (U₂ x y) •
        resΓ hT₁₂V h₂ ((inf_le_right : T₁ ⊓ T₂ ≤ T₂).trans hT₂) M (s₂ y) := fun _ =>
    resΓ_sum_smul_resΓ _ _ _ _ _ M _ _
  have hs₂ : ∀ y, resΓ hT₁₂V h₂ ((inf_le_right : T₁ ⊓ T₂ ≤ T₂).trans hT₂) M (s₂ y) =
      ∑ w, rR hT₁₂ (G y w) • resΓ hT₁₂V h₁ ((inf_le_left : T₁ ⊓ T₂ ≤ T₁).trans hT₁) M (s₁ w) := by
    intro y
    refine (resΓ_resΓ hT₁₂V hBV h₂ hT₁₂ hB₂ M (s₂ y)).symm.trans ?_
    refine (congrArg (resΓ hT₁₂V hBV hT₁₂ M) (hrel y)).trans ?_
    exact resΓ_sum_smul_resΓ _ _ _ _ _ M _ _
  have key : ∀ x, resΓ hT₁₂V hT₁V (inf_le_left : T₁ ⊓ T₂ ≤ T₁) M (τ₁ x) =
      resΓ hT₁₂V hT₂V (inf_le_right : T₁ ⊓ T₂ ≤ T₂) M (τ₂ x) := by
    intro x
    refine (r₁ x).trans ((r₂ x).trans ?_).symm
    refine (Finset.sum_congr rfl fun y _ => congrArg _ (hs₂ y)).trans ?_
    refine (sum_smul_sum _ _ _).trans (Finset.sum_congr rfl fun w _ => ?_)
    congr 1
    simpa only [Matrix.mul_apply, Matrix.map_apply] using congrFun (congrFun hU x) w
  have hglue : ∀ x, ∃ t : Γ ((res _ hT).obj M),
      rΓ le_sup_left _ t = (show Γ ((res _ le_sup_left).obj ((res _ hT).obj M)) from τ₁ x) ∧
      rΓ le_sup_right _ t = (show Γ ((res _ le_sup_right).obj ((res _ hT).obj M)) from τ₂ x) :=
    fun x => exists_glue le_sup_left le_sup_right le_rfl ((res _ hT).obj M) _ _ (key x)
  choose τ hτ₁ hτ₂ using hglue
  exact ⟨T₁, T₂, hT₁, hT₂, U₁, U₁', U₂, U₂', hK₁T, hK₂T, e1, e2, e3, e4, τ,
    hτ₁, hτ₂⟩

/-- The restriction of `ofTop τ` to `A ≤ T`, where `τ|_A = U s|_A`, is
`ofMatrix U ≫ (ofTop s)|_A`, up to the canonical isomorphisms. -/
lemma res_ofTop_of_eq {V T W A : Opens (TopCat.of U)} (hT : T ≤ V) (hW : W ≤ V)
    (hA : A ≤ V) (hAT : A ≤ T) (hAW : A ≤ W)
    (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V)) {I : Type} [Fintype I]
    (τ : I → Γ ((res _ hT).obj M)) (s : I → Γ ((res _ hW).obj M))
    (Uₐ : Matrix I I (((holomorphicRingCatSheaf n U).over A).obj.obj (op (topOver A))))
    (hτ : ∀ x, resΓ hA hT hAT M (τ x) = ∑ y, Uₐ x y • resΓ hA hW hAW M (s y)) :
    (freeRes hAT I).hom ≫ (res _ hAT).map (ofTop τ) ≫ (resResIso hAT hT hA M).hom =
      ofMatrix Uₐ ≫ (freeRes hAW I).hom ≫ (res _ hAW).map (ofTop s) ≫
        (resResIso hAW hW hA M).hom := by
  rw [ofTop_res, ofTop_res, ofMatrix_comp_ofTop]
  congr 1
  funext x
  exact hτ x

end SplitSections

section GlueResolutions

variable {n : ℕ} {U : Opens (EuclideanSpace ℂ (Fin n))}

/-- `ofTop` is injective. -/
lemma ofTop_injective {X : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}
    {T : Opens X} {M : SheafOfModules.{0} (R.over T)} {I : Type} {t t' : I → Γ M}
    (h : ofTop t = ofTop t') : t = t' := by
  funext i
  rw [← ofTop_app_eb t i, ← ofTop_app_eb t' i, h]

/-- If `e₁ ≫ X ≫ e₂` is an isomorphism `Y` and `e₁`, `e₂` are isomorphisms, then `X` is an
isomorphism. -/
lemma isIso_of_comp_eq {C : Type*} [Category C] {A A' B B' : C} (e₁ : A' ⟶ A) (X : A ⟶ B)
    (e₂ : B ⟶ B') (Y : A' ⟶ B') [IsIso e₁] [IsIso e₂] [IsIso Y]
    (h : e₁ ≫ X ≫ e₂ = Y) : IsIso X := by
  subst h
  have := IsIso.of_isIso_comp_left e₁ (X ≫ e₂)
  exact IsIso.of_isIso_comp_right X e₂

/-- Two mutually inverse matrices of holomorphic functions on a nonempty open are square. -/
lemma eq_of_mul_eq_one_evO {T : Opens (TopCat.of U)} (y : T) {p q : ℕ}
    (G : Matrix (Fin q) (Fin p) (((holomorphicRingCatSheaf n U).over T).obj.obj (op (topOver T))))
    (H : Matrix (Fin p) (Fin q) (((holomorphicRingCatSheaf n U).over T).obj.obj (op (topOver T))))
    (hGH : G * H = 1) (hHG : H * G = 1) : q = p := by
  simpa using Matrix.square_of_invertible (G.map (evO y)) (H.map (evO y))
    (by rw [← Matrix.map_mul, hGH, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← Matrix.map_mul, hHG, Matrix.map_one _ (map_zero _) (map_one _)])

/-- Bases of `M` on `W₁` and on `W₂` are related on `W₁ ⊓ W₂` by an invertible matrix. -/
lemma exists_transition_tuples {V W₁ W₂ : Opens (TopCat.of U)} (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V)
    (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V)) {r₁ r₂ : ℕ}
    (ψ₁ : SheafOfModules.free (Fin r₁) ≅ (res _ h₁).obj M)
    (ψ₂ : SheafOfModules.free (Fin r₂) ≅ (res _ h₂).obj M) :
    ∃ (s₁ : Fin r₁ → Γ ((res _ h₁).obj M)) (s₂ : Fin r₂ → Γ ((res _ h₂).obj M))
      (G : Matrix (Fin r₂) (Fin r₁)
        (((holomorphicRingCatSheaf n U).over (W₁ ⊓ W₂)).obj.obj (op (topOver (W₁ ⊓ W₂)))))
      (H : Matrix (Fin r₁) (Fin r₂)
        (((holomorphicRingCatSheaf n U).over (W₁ ⊓ W₂)).obj.obj (op (topOver (W₁ ⊓ W₂))))),
      ψ₁.hom = ofTop s₁ ∧ ψ₂.hom = ofTop s₂ ∧ G * H = 1 ∧ H * G = 1 ∧
      ∀ x, resΓ (inf_le_left.trans h₁) h₂ inf_le_right M (s₂ x) =
        ∑ y, G x y • resΓ (inf_le_left.trans h₁) h₁ inf_le_left M (s₁ y) := by
  have hB₁ : W₁ ⊓ W₂ ≤ W₁ := inf_le_left
  have hB₂ : W₁ ⊓ W₂ ≤ W₂ := inf_le_right
  have hBV : W₁ ⊓ W₂ ≤ V := hB₁.trans h₁
  have hχ : ∀ {W : Opens (TopCat.of U)} {r : ℕ} (hB : W₁ ⊓ W₂ ≤ W) (hW : W ≤ V)
      (ψ : SheafOfModules.free (Fin r) ≅ (res _ hW).obj M), (freeRes hB (Fin r)).hom ≫
        (res _ hB).map ψ.hom ≫ (resResIso hB hW hBV M).hom = ofTop (fun j =>
          resΓ hBV hW hB M (ψ.hom.val.app (op (topOver W)) (eb j))) := fun hB hW ψ =>
    (congrArg (fun φ => (freeRes hB _).hom ≫ (res _ hB).map φ ≫ (resResIso hB hW hBV M).hom)
      (eq_ofTop ψ.hom)).trans (ofTop_res hBV hW hB M _)
  refine Exists.elim (exists_transition
    (freeRes hB₁ (Fin r₁) ≪≫ (res _ hB₁).mapIso ψ₁ ≪≫ resResIso hB₁ h₁ hBV M)
    (freeRes hB₂ (Fin r₂) ≪≫ (res _ hB₂).mapIso ψ₂ ≪≫ resResIso hB₂ h₂ hBV M))
    fun G hG => Exists.elim hG fun H hH => ?_
  refine ⟨_, _, G, H, eq_ofTop ψ₁.hom, eq_ofTop ψ₂.hom, hH.1, hH.2.1, fun x => ?_⟩
  have h1 := ((ofMatrix_comp_ofTop G _).symm.trans
    ((congrArg (ofMatrix G ≫ ·) (hχ hB₁ h₁ ψ₁)).symm.trans (hH.2.2.trans (hχ hB₂ h₂ ψ₂))))
  exact (congrFun (ofTop_injective h1) x).symm

/-- After the matrix splitting, the glued tuple `τ` is a basis of `M` near `T₁ ⊔ T₂`. -/
lemma hasFFR_zero_of_glue_tuple {V W₁ W₂ T₁ T₂ : Opens (TopCat.of U)} (h₁ : W₁ ≤ V)
    (h₂ : W₂ ≤ V) (hT₁ : T₁ ≤ W₁) (hT₂ : T₂ ≤ W₂) (hT : T₁ ⊔ T₂ ≤ V)
    (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V)) {r : ℕ}
    (s₁ : Fin r → Γ ((res _ h₁).obj M)) (s₂ : Fin r → Γ ((res _ h₂).obj M))
    [IsIso (ofTop s₁)] [IsIso (ofTop s₂)]
    (U₁ U₁' : Matrix (Fin r) (Fin r)
      (((holomorphicRingCatSheaf n U).over T₁).obj.obj (op (topOver T₁))))
    (U₂ U₂' : Matrix (Fin r) (Fin r)
      (((holomorphicRingCatSheaf n U).over T₂).obj.obj (op (topOver T₂))))
    (e1 : U₁ * U₁' = 1) (e2 : U₁' * U₁ = 1) (e3 : U₂ * U₂' = 1) (e4 : U₂' * U₂ = 1)
    (τ : Fin r → Γ ((res _ hT).obj M))
    (hτ₁ : ∀ x, resΓ (hT₁.trans h₁) hT le_sup_left M (τ x) =
      ∑ y, U₁ x y • resΓ (hT₁.trans h₁) h₁ hT₁ M (s₁ y))
    (hτ₂ : ∀ x, resΓ (hT₂.trans h₂) hT le_sup_right M (τ x) =
      ∑ y, U₂ x y • resΓ (hT₂.trans h₂) h₂ hT₂ M (s₂ y)) :
    HasFFR ((res _ hT).obj M) 0 := by
  have := isIso_ofMatrix U₁ U₁' e1 e2
  have := isIso_ofMatrix U₂ U₂' e3 e4
  have hiso₁ : IsIso ((res _ (le_sup_left : T₁ ≤ T₁ ⊔ T₂)).map (ofTop τ)) :=
    isIso_of_comp_eq _ _ _ _
      (res_ofTop_of_eq hT h₁ (hT₁.trans h₁) le_sup_left hT₁ M τ s₁ U₁ hτ₁)
  have hiso₂ : IsIso ((res _ (le_sup_right : T₂ ≤ T₁ ⊔ T₂)).map (ofTop τ)) :=
    isIso_of_comp_eq _ _ _ _
      (res_ofTop_of_eq hT h₂ (hT₂.trans h₂) le_sup_right hT₂ M τ s₂ U₂ hτ₂)
  have := mono_of_mono_res le_sup_left le_sup_right le_rfl (ofTop τ) inferInstance inferInstance
  have := epi_of_epi_res le_sup_left le_sup_right le_rfl (ofTop τ) (IsIso.epi_of_iso _)
    (IsIso.epi_of_iso _)
  have := isIso_of_mono_of_epi (ofTop τ)
  exact hasFFR_zero_of_iso (asIso (ofTop τ))

/-- **The base case of the gluing.** Bases of `M` near `K₁` and near `K₂` glue, after the
matrix splitting, to a basis near `K₁ ∪ K₂`. -/
lemma glue_base {K₁ K₂ : Set (EuclideanSpace ℂ (Fin n))}
    (hsplit : SplitProp K₁ K₂) (hKU : K₁ ∪ K₂ ⊆ U) (hc₁ : IsCompact K₁) (hc₂ : IsCompact K₂)
    (hLne : (K₁ ∩ K₂).Nonempty) {V W₁ W₂ : Opens (TopCat.of U)} (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V)
    (hK₁ : (Subtype.val : U → _) ⁻¹' K₁ ⊆ W₁) (hK₂ : (Subtype.val : U → _) ⁻¹' K₂ ⊆ W₂)
    (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V)) {r₁ r₂ : ℕ}
    (ψ₁ : SheafOfModules.free (Fin r₁) ≅ (res _ h₁).obj M)
    (ψ₂ : SheafOfModules.free (Fin r₂) ≅ (res _ h₂).obj M) :
    ∃ (W : Opens (TopCat.of U)) (h : W ≤ V), (Subtype.val : U → _) ⁻¹' (K₁ ∪ K₂) ⊆ W ∧
      HasFFR ((res _ h).obj M) 0 := by
  have hB₁ : W₁ ⊓ W₂ ≤ W₁ := inf_le_left
  have hB₂ : W₁ ⊓ W₂ ≤ W₂ := inf_le_right
  have hBV : W₁ ⊓ W₂ ≤ V := hB₁.trans h₁
  have hLB : (Subtype.val : U → _) ⁻¹' (K₁ ∩ K₂) ⊆ (W₁ ⊓ W₂ : Opens (TopCat.of U)) :=
    fun x hx => ⟨hK₁ hx.1, hK₂ hx.2⟩
  refine Exists.elim (exists_transition_tuples h₁ h₂ M ψ₁ ψ₂) fun s₁ h => Exists.elim h
    fun s₂ h => Exists.elim h fun G h => Exists.elim h fun H h => ?_
  obtain ⟨z, hz⟩ := hLne
  have hr : r₂ = r₁ := eq_of_mul_eq_one_evO (T := W₁ ⊓ W₂)
    ⟨⟨z, hKU (Or.inl hz.1)⟩, hLB (show (⟨z, hKU (Or.inl hz.1)⟩ : U).1 ∈ K₁ ∩ K₂ from hz)⟩
    G H h.2.2.1 h.2.2.2.1
  subst hr
  obtain ⟨T₁, T₂, hT₁, hT₂, U₁, U₁', U₂, U₂', hK₁T, hK₂T, e1, e2, e3, e4, τ, hτ₁, hτ₂⟩ :=
    exists_glue_tuple hsplit hKU hc₁ hc₂ h₁ h₂ hB₁ hB₂ hK₁ hK₂ hLB M s₁ s₂ G H h.2.2.1 h.2.2.2.1
      hBV h.2.2.2.2
  have : IsIso (ofTop s₁) := h.1 ▸ inferInstance
  have : IsIso (ofTop s₂) := h.2.1 ▸ inferInstance
  exact ⟨T₁ ⊔ T₂, _, fun x hx => Or.elim hx (fun h => Or.inl (hK₁T h)) fun h => Or.inr (hK₂T h),
    hasFFR_zero_of_glue_tuple h₁ h₂ hT₁ hT₂ _ M s₁ s₂ U₁ U₁' U₂ U₂' e1 e2 e3 e4 τ hτ₁ hτ₂⟩

/-- The open of `U` underlying the top open of `P`, read through `Over P ≌ Opens P`. -/
noncomputable abbrev boxTop (P : Opens (TopCat.of U)) : Opens (TopCat.of U) :=
  ((Opens.overEquivalence P).inverse.obj ⊤).left

/-- `boxTop P` is contained in `P`. -/
lemma boxTop_le (P : Opens (TopCat.of U)) : boxTop P ≤ P :=
  ((Opens.overEquivalence P).inverse.obj ⊤).hom.le

/-- `P` is contained in `boxTop P`. -/
lemma le_boxTop (P : Opens (TopCat.of U)) : P ≤ boxTop P := fun x hx =>
  ⟨⟨x, hx⟩, trivial, rfl⟩

/-- The glued map near the first side, up to isomorphisms. -/
lemma step_eq₁ {V T W A : Opens (TopCat.of U)} (hT : T ≤ V) (hW : W ≤ V) (hA : A ≤ V)
    (hAT : A ≤ T) (hAW : A ≤ W) (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V))
    {p q : ℕ} (τ : Fin p ⊕ Fin q → Γ ((res _ hT).obj M)) (s : Fin p → Γ ((res _ hW).obj M))
    (Uₐ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
      (((holomorphicRingCatSheaf n U).over A).obj.obj (op (topOver A))))
    (hτ : ∀ x, resΓ hA hT hAT M (τ x) =
      ∑ y, Uₐ x y • resΓ hA hW hAW M (Sum.elim s (0 : Fin q → Γ ((res _ hW).obj M)) y)) :
    (freeRes hAT (Fin p ⊕ Fin q)).hom ≫ (res _ hAT).map (ofTop τ) ≫ (resResIso hAT hT hA M).hom =
      (ofMatrix Uₐ ≫ (freeRes hAW (Fin p ⊕ Fin q)).hom ≫
        (res _ hAW).map (freeSumIso (Fin p) (Fin q)).hom) ≫
        (res _ hAW).map (biprod.desc (ofTop s)
          (0 : SheafOfModules.free (Fin q) ⟶ (res _ hW).obj M)) ≫
        (resResIso hAW hW hA M).hom := by
  have e : (res _ hAW).map (ofTop (Sum.elim s (0 : Fin q → Γ ((res _ hW).obj M)))) =
      (res _ hAW).map (freeSumIso (Fin p) (Fin q)).hom ≫ (res _ hAW).map (biprod.desc (ofTop s)
          (0 : SheafOfModules.free (Fin q) ⟶ (res _ hW).obj M)) :=
    (congrArg (res _ hAW).map (ofTop_sumElim_zero s)).trans (Functor.map_comp _ _ _)
  refine (res_ofTop_of_eq hT hW hA hAT hAW M τ _ Uₐ hτ).trans ?_
  refine (congrArg (fun φ => ofMatrix Uₐ ≫ (freeRes hAW (Fin p ⊕ Fin q)).hom ≫ φ ≫
    (resResIso hAW hW hA M).hom) e).trans ?_
  simp only [Category.assoc]

/-- If `e₁ ≫ x ≫ e₂` is an epimorphism and `e₂` is an isomorphism, then `x` is an epimorphism. -/
lemma epi_of_comp_iso {C : Type*} [Category C] {A A' B B' : C} (e₁ : A' ⟶ A)
    (x : A ⟶ B) (e₂ : B ⟶ B') [IsIso e₂] (h : Epi (e₁ ≫ x ≫ e₂)) : Epi x :=
  (epi_comp_iff_of_isIso x e₂).1 (epi_of_epi e₁ _)

/-- **Local structure of the glued map, first side.** -/
lemma step_local₁ {V T W A : Opens (TopCat.of U)} (hT : T ≤ V) (hW : W ≤ V) (hA : A ≤ V)
    (hAT : A ≤ T) (hAW : A ≤ W) (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V))
    {p q ℓ : ℕ} (τ : Fin p ⊕ Fin q → Γ ((res _ hT).obj M)) (s : Fin p → Γ ((res _ hW).obj M))
    (Uₐ Uₐ' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
      (((holomorphicRingCatSheaf n U).over A).obj.obj (op (topOver A))))
    (h1 : Uₐ * Uₐ' = 1) (h2 : Uₐ' * Uₐ = 1)
    (hτ : ∀ x, resΓ hA hT hAT M (τ x) =
      ∑ y, Uₐ x y • resΓ hA hW hAW M (Sum.elim s (0 : Fin q → Γ ((res _ hW).obj M)) y))
    [Epi (ofTop s)] (hk : HasFFR (kernel (ofTop s)) ℓ) :
    Epi ((res _ hAT).map (ofTop τ)) ∧ HasFFR (kernel ((res _ hAT).map (ofTop τ))) ℓ := by
  have := isIso_ofMatrix Uₐ Uₐ' h1 h2
  have E := step_eq₁ hT hW hA hAT hAW M τ s Uₐ hτ
  refine ⟨?_, ?_⟩
  · have : Epi (biprod.desc (ofTop s)
        (0 : SheafOfModules.free (Fin q) ⟶ (res _ hW).obj M)) :=
      epi_of_epi_fac (biprod.inl_desc (ofTop s) 0)
    have := (SheafOfModules.overMapPushforwardAdj (holomorphicRingCatSheaf n U)
      (homOfLE hAW)).isLeftAdjoint
    have hR : Epi ((freeRes hAT (Fin p ⊕ Fin q)).hom ≫ (res _ hAT).map (ofTop τ) ≫
        (resResIso hAT hT hA M).hom) := by
      rw [E]
      have := Functor.map_epi (res _ hAW) (biprod.desc (ofTop s)
        (0 : SheafOfModules.free (Fin q) ⟶ (res _ hW).obj M))
      exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' this inferInstance)
    exact epi_of_comp_iso _ _ _ hR
  · exact hasFFR_kernel_of_comp_eq hAW _ _ _ _ _ _ E
      ((hasFFR_biprod_free ℓ _ hk q).of_iso (kernelBiprodDescZeroIso _).symm)

/-- The glued map near the second side, up to isomorphisms. -/
lemma step_eq₂ {V T W A : Opens (TopCat.of U)} (hT : T ≤ V) (hW : W ≤ V) (hA : A ≤ V)
    (hAT : A ≤ T) (hAW : A ≤ W) (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V))
    {p q : ℕ} (τ : Fin p ⊕ Fin q → Γ ((res _ hT).obj M)) (s : Fin q → Γ ((res _ hW).obj M))
    (Uₐ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
      (((holomorphicRingCatSheaf n U).over A).obj.obj (op (topOver A))))
    (hτ : ∀ x, resΓ hA hT hAT M (τ x) =
      ∑ y, Uₐ x y • resΓ hA hW hAW M (Sum.elim (0 : Fin p → Γ ((res _ hW).obj M)) s y)) :
    (freeRes hAT (Fin p ⊕ Fin q)).hom ≫ (res _ hAT).map (ofTop τ) ≫ (resResIso hAT hT hA M).hom =
      (ofMatrix Uₐ ≫ (freeRes hAW (Fin p ⊕ Fin q)).hom ≫
        (res _ hAW).map (freeSumIso (Fin p) (Fin q)).hom) ≫
        (res _ hAW).map (biprod.desc
          (0 : SheafOfModules.free (Fin p) ⟶ (res _ hW).obj M) (ofTop s)) ≫
        (resResIso hAW hW hA M).hom := by
  have e : (res _ hAW).map (ofTop (Sum.elim (0 : Fin p → Γ ((res _ hW).obj M)) s)) =
      (res _ hAW).map (freeSumIso (Fin p) (Fin q)).hom ≫ (res _ hAW).map (biprod.desc
          (0 : SheafOfModules.free (Fin p) ⟶ (res _ hW).obj M) (ofTop s)) :=
    (congrArg (res _ hAW).map (ofTop_sumElim_zero' s)).trans (Functor.map_comp _ _ _)
  refine (res_ofTop_of_eq hT hW hA hAT hAW M τ _ Uₐ hτ).trans ?_
  refine (congrArg (fun φ => ofMatrix Uₐ ≫ (freeRes hAW (Fin p ⊕ Fin q)).hom ≫ φ ≫
    (resResIso hAW hW hA M).hom) e).trans ?_
  simp only [Category.assoc]

/-- **Local structure of the glued map, second side.** -/
lemma step_local₂ {V T W A : Opens (TopCat.of U)} (hT : T ≤ V) (hW : W ≤ V) (hA : A ≤ V)
    (hAT : A ≤ T) (hAW : A ≤ W) (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V))
    {p q ℓ : ℕ} (τ : Fin p ⊕ Fin q → Γ ((res _ hT).obj M)) (s : Fin q → Γ ((res _ hW).obj M))
    (Uₐ Uₐ' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q)
      (((holomorphicRingCatSheaf n U).over A).obj.obj (op (topOver A))))
    (h1 : Uₐ * Uₐ' = 1) (h2 : Uₐ' * Uₐ = 1)
    (hτ : ∀ x, resΓ hA hT hAT M (τ x) =
      ∑ y, Uₐ x y • resΓ hA hW hAW M (Sum.elim (0 : Fin p → Γ ((res _ hW).obj M)) s y))
    [Epi (ofTop s)] (hk : HasFFR (kernel (ofTop s)) ℓ) :
    Epi ((res _ hAT).map (ofTop τ)) ∧ HasFFR (kernel ((res _ hAT).map (ofTop τ))) ℓ := by
  have := isIso_ofMatrix Uₐ Uₐ' h1 h2
  have E := step_eq₂ hT hW hA hAT hAW M τ s Uₐ hτ
  refine ⟨?_, ?_⟩
  · have : Epi (biprod.desc
        (0 : SheafOfModules.free (Fin p) ⟶ (res _ hW).obj M) (ofTop s)) :=
      epi_of_epi_fac (biprod.inr_desc 0 (ofTop s))
    have := (SheafOfModules.overMapPushforwardAdj (holomorphicRingCatSheaf n U)
      (homOfLE hAW)).isLeftAdjoint
    have hR : Epi ((freeRes hAT (Fin p ⊕ Fin q)).hom ≫ (res _ hAT).map (ofTop τ) ≫
        (resResIso hAT hT hA M).hom) := by
      rw [E]
      have := Functor.map_epi (res _ hAW) (biprod.desc
        (0 : SheafOfModules.free (Fin p) ⟶ (res _ hW).obj M) (ofTop s))
      exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' this inferInstance)
    exact epi_of_comp_iso _ _ _ hR
  · exact hasFFR_kernel_of_comp_eq hAW _ _ _ _ _ _ E
      ((hasFFR_free_biprod ℓ _ hk p).of_iso (kernelBiprodDescZeroIso' _).symm)

end GlueResolutions

end MMP.Analytic.CartanCompactBlocks
