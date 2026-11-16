module

public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem

/-!
# c-soft sheaves and extension by zero for cohomology with compact supports

Let `X` be a locally compact Hausdorff space and `R` a commutative ring. A sheaf `F` of
`R`-modules on `X` is *c-soft* if every section of `F` over a compact set `K ⊆ X`, that is, an
element of `colim_{W ⊇ K} F(W)`, extends to a global section: for every open `W ⊇ K` and every
`s ∈ F(W)` there are a global section `t` and an open `V` with `K ⊆ V ⊆ W` such that `t` and `s`
agree on `V`.

Then
* (a) every flasque sheaf, and every injective sheaf, is c-soft;
* (b) for a short exact sequence `0 → F' → F → F'' → 0` with `F'` c-soft, the sequence
  `0 → Γ_c(X, F') → Γ_c(X, F) → Γ_c(X, F'') → 0` is exact, and if `F` is c-soft too then so is
  `F''`;
* (c) `H^q_c(X, F) = 0` for `q > 0` when `F` is c-soft; for a bounded below complex `C^•` of
  c-soft sheaves the canonical comparison `Γ_c(X, C^•) ⟶ RΓ_c(X, C^•)` is an isomorphism, so
  that `H^q_c(X, F) ≅ H^q(Γ_c(X, C^•))` for every resolution `F → C^•` by c-soft sheaves.

Injective sheaves are c-soft as retracts of the Godement sheaf of discontinuous sections. In
(b), sections of `F''` lift locally near compact sets, the local lifts glue by c-softness of `F'`,
and hence compactly supported sections lift. Cutting an acyclic bounded below complex of c-soft
sheaves into short exact sequences of cycles shows that `Γ_c` preserves its acyclicity; applied to
mapping cones and an injective resolution this gives (c).

Now let `U ⊆ X` be open with inclusion `j`, let `j^*` be restriction of sheaves to `U` and `j_!`
its left adjoint, extension by zero. Then `j_!` is exact and fully faithful (`G ≅ j^* j_! G`), its
stalks are those of `G` on `U` and vanish off `U`, it carries c-soft sheaves to c-soft sheaves, and
compactly supported global sections of `j_! G` are those of `G`. Consequently
`H^q_c(U, G) ≅ H^q_c(X, j_! G)`, and for opens `V ⊆ U` the inclusion
`j_{V!}(F|_V) ⟶ j_{U!}(F|_U)` induces extension maps `H^q_c(V, F) ⟶ H^q_c(U, F)`, functorial in
`V ⊆ U` and natural in `F`.

The open embedding functor `Opens U ⥤ Opens X` is continuous and cocontinuous, so `j^*` also has
a right adjoint, whose counit is invertible because the functor is fully faithful; by the adjoint
triple `j_! ⊣ j^* ⊣ j_*` the unit `G ⟶ j^* j_! G` is invertible. The stalks of `j_! G` off `U`
vanish by adjunction with skyscraper sheaves. Since `j_!` is exact and carries injective sheaves
to c-soft sheaves, the universal property of `RΓ_c` gives a comparison
`RΓ_c(U, -) ⟶ RΓ_c(X, j_! -)`, invertible on injective complexes by (c), hence everywhere.

## Main results

* `MMP.Fourfold.compactSupportCohomology_of_isCSoft`: parts (a)–(c) above.
* `MMP.Fourfold.compactSupportCohomology_extendByZero`: the properties of `j_!` and the
  isomorphisms `H^q_c(U, -) ≅ H^q_c(X, j_! -)` with their extension maps.

## Implementation notes

The predicate "c-soft" is written out inside each statement as a local definition; a section over
`K` is represented by a section over an open neighbourhood `W` of `K`, and two representatives
define the same element of the colimit exactly when they agree on a smaller open neighbourhood
of `K`.

The comparison in (c) is the unit `Functor.rightDerivedFunctorPlusUnit` of the right derived
functor of `MMP.Fourfold.compactSupportSectionsFunctor`, evaluated at the complex; the derived
categories are the standard ones (`HasDerivedCategory.standard`), as in
`MMP.Fourfold.compactSupportCohomology`.

Extension by zero is `Functor.sheafPullback` along the functor `Opens U ⥤ Opens X` of the open
embedding, the left adjoint of the restriction `Functor.sheafPushforwardContinuous`. The
inclusion `j_{V!}(F|_V) ⟶ j_{U!}(F|_U)` is characterised as the unique morphism over `F`, i.e.
compatible with the counits; it exists and is unique because the counit `j_{U!} j_U^* F ⟶ F` is
a monomorphism that is invertible over `U`.

## References

* [G. E. Bredon, *Sheaf theory*][bredon1997], II.9
* [M. Kashiwara, P. Schapira, *Sheaves on manifolds*][kashiwaraschapira1990], II.2.5
* [B. Iversen, *Cohomology of sheaves*], III.7
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace MMP.Fourfold

attribute [local instance] HasDerivedCategory.standard

namespace CSoftAcyclic

variable {R : Type} [CommRing R] {X : TopCat.{0}}

private lemma res_res (F : TopCat.Sheaf (ModuleCat.{0} R) X) {A B C : Opens X} (hAB : A ≤ B)
    (hBC : B ≤ C) (s : F.obj.obj (op C)) :
    F.obj.map (homOfLE hAB).op (F.obj.map (homOfLE hBC).op s) =
      F.obj.map (homOfLE (hAB.trans hBC)).op s := by
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  rfl

private lemma res_self (F : TopCat.Sheaf (ModuleCat.{0} R) X) {A : Opens X} (h : A ≤ A)
    (s : F.obj.obj (op A)) : F.obj.map (homOfLE h).op s = s := by
  rw [show (homOfLE h).op = 𝟙 (op A) from rfl, F.obj.map_id]
  rfl

private lemma nat_res {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ G) {A B : Opens X}
    (h : A ≤ B) (s : F.obj.obj (op B)) :
    φ.hom.app (op A) (F.obj.map (homOfLE h).op s) =
      G.obj.map (homOfLE h).op (φ.hom.app (op B) s) :=
  NatTrans.naturality_apply φ.hom (homOfLE h).op s

private lemma sections_exact {S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X)}
    (hS : S.ShortExact) {U : Opens X} (s : S.X₂.obj.obj (op U))
    (h : S.g.hom.app (op U) s = 0) :
    ∃ t : S.X₁.obj.obj (op U), S.f.hom.app (op U) t = s := by
  have hS' : (S.map (TopCat.Sheaf.forget (ModuleCat.{0} R) X)).Exact :=
    (((Functor.preservesFiniteLimits_tfae (TopCat.Sheaf.forget (ModuleCat.{0} R) X)).out
      2 4 rfl rfl).mpr inferInstance S ⟨hS.exact, hS.mono_f⟩).left
  let E := (evaluation (Opens X)ᵒᵖ (ModuleCat.{0} R)).obj (op U)
  have := (((Functor.exact_tfae E).out 2 4 rfl rfl).mpr
    ⟨inferInstance, inferInstance⟩ _ hS')
  exact (ShortComplex.moduleCat_exact_iff _).mp this s h

private lemma injective_app {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ G) [Mono φ]
    (U : Opens X) : Function.Injective (φ.hom.app (op U)) := by
  have : Mono ((TopCat.Sheaf.forget (ModuleCat.{0} R) X).map φ) := inferInstance
  have : Mono (φ.hom.app (op U)) := by
    change Mono (((TopCat.Sheaf.forget (ModuleCat.{0} R) X).map φ).app (op U))
    infer_instance
  exact (ModuleCat.mono_iff_injective _).mp this

private lemma locally_surjective {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ G) [Epi φ]
    {U : Opens X} (s : G.obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ∃ t : F.obj.obj (op V), φ.hom.app (op V) t = G.obj.map (homOfLE hVU).op s := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := φ)).mpr ‹Epi φ›
  obtain ⟨V, hVU, ⟨t, ht⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff φ.hom).mp this U s x hx
  exact ⟨V, hVU, hxV, t, ht⟩

private lemma glue2 (F : TopCat.Sheaf (ModuleCat.{0} R) X) {U₁ U₂ V : Opens X} (h₁ : U₁ ≤ V)
    (h₂ : U₂ ≤ V) (hV : V ≤ U₁ ⊔ U₂) (s₁ : F.obj.obj (op U₁)) (s₂ : F.obj.obj (op U₂))
    (h : F.obj.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op s₁ =
      F.obj.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op s₂) :
    ∃ s : F.obj.obj (op V), F.obj.map (homOfLE h₁).op s = s₁ ∧
      F.obj.map (homOfLE h₂).op s = s₂ := by
  let U : Bool → Opens X := fun b => cond b U₁ U₂
  let sf : ∀ b, F.obj.obj (op (U b)) := fun b =>
    Bool.rec (motive := fun b => F.obj.obj (op (U b))) s₂ s₁ b
  have hsymm : F.obj.map (homOfLE (inf_le_left : U₂ ⊓ U₁ ≤ U₂)).op s₂ =
      F.obj.map (homOfLE (inf_le_right : U₂ ⊓ U₁ ≤ U₁)).op s₁ := by
    have := congrArg (F.obj.map (homOfLE (le_of_eq (inf_comm U₂ U₁))).op) h
    rw [res_res, res_res] at this
    exact this.symm
  have hc : TopCat.Presheaf.IsCompatible F.obj U sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · exact hsymm
    · exact h
    · rfl
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' U V (fun b => homOfLE (by
      cases b
      · exact h₂
      · exact h₁)) (hV.trans (sup_le (le_iSup U true) (le_iSup U false))) sf hc
  exact ⟨s, hs true, hs false⟩

private lemma g_f_apply {S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X)} {U : Opens X}
    (a : S.X₁.obj.obj (op U)) : S.g.hom.app (op U) (S.f.hom.app (op U) a) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
  have : S.f.hom ≫ S.g.hom = 0 := by
    change (TopCat.Sheaf.forget (ModuleCat.{0} R) X).map S.f ≫
      (TopCat.Sheaf.forget (ModuleCat.{0} R) X).map S.g = 0
    rw [← Functor.map_comp, S.zero, Functor.map_zero]
  rw [this]
  rfl

/-- c-softness: sections over a compact set extend to global sections. -/
private def IsCSoft (F : TopCat.Sheaf (ModuleCat.{0} R) X) : Prop :=
  ∀ K : Set X, IsCompact K → ∀ (W : Opens X), K ⊆ W → ∀ s : F.obj.obj (op W),
    ∃ (t : F.obj.obj (op ⊤)) (V : Opens X) (_ : K ⊆ V) (hVW : V ≤ W),
      F.obj.map (homOfLE le_top).op t = F.obj.map (homOfLE hVW).op s

/-- A section `s` of `S.X₃` over `W` lifts to `S.X₂` on an open neighbourhood of `L` inside `W`. -/
private def LiftsNear (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X)) {W : Opens X}
    (s : S.X₃.obj.obj (op W)) (L : Set X) : Prop :=
  ∃ (V : Opens X) (_ : L ⊆ V) (hVW : V ≤ W) (t : S.X₂.obj.obj (op V)),
    S.g.hom.app (op V) t = S.X₃.obj.map (homOfLE hVW).op s

private lemma liftsNear_union [T2Space X] {S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X)}
    (hS : S.ShortExact) (hA : IsCSoft S.X₁) {W : Opens X} (s : S.X₃.obj.obj (op W))
    {L₁ L₂ : Set X} (h₁ : IsCompact L₁) (h₂ : IsCompact L₂) (p₁ : LiftsNear S s L₁)
    (p₂ : LiftsNear S s L₂) : LiftsNear S s (L₁ ∪ L₂) := by
  obtain ⟨V₁, hL₁, hV₁, t₁, ht₁⟩ := p₁
  obtain ⟨V₂, hL₂, hV₂, t₂, ht₂⟩ := p₂
  let d := S.X₂.obj.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op t₁ -
    S.X₂.obj.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op t₂
  have hd : S.g.hom.app (op (V₁ ⊓ V₂)) d = 0 := by
    simp only [d, map_sub, nat_res, ht₁, ht₂, res_res, sub_self]
  obtain ⟨a, ha⟩ := sections_exact hS d hd
  obtain ⟨a', P, hLP, hPV, ha'⟩ := hA (L₁ ∩ L₂) (h₁.inter h₂) (V₁ ⊓ V₂)
    (fun x hx => ⟨hL₁ hx.1, hL₂ hx.2⟩) a
  let t₂' := t₂ + S.f.hom.app (op V₂) (S.X₁.obj.map (homOfLE (le_top : V₂ ≤ ⊤)).op a')
  have ht₂' : S.g.hom.app (op V₂) t₂' = S.X₃.obj.map (homOfLE hV₂).op s := by
    simp only [t₂', map_add, g_f_apply, ht₂, add_zero]
  have hP₁ : P ≤ V₁ := hPV.trans inf_le_left
  have hP₂ : P ≤ V₂ := hPV.trans inf_le_right
  have hP : S.X₂.obj.map (homOfLE hP₁).op t₁ = S.X₂.obj.map (homOfLE hP₂).op t₂' := by
    have e1 : S.X₂.obj.map (homOfLE hPV).op d =
        S.X₂.obj.map (homOfLE hP₁).op t₁ - S.X₂.obj.map (homOfLE hP₂).op t₂ := by
      simp only [d, map_sub, res_res]
    have e2 : S.X₂.obj.map (homOfLE hPV).op d =
        S.X₂.obj.map (homOfLE (le_top : P ≤ ⊤)).op (S.f.hom.app (op ⊤) a') := by
      rw [← ha, ← nat_res, ← ha', nat_res]
    simp only [t₂', map_add, nat_res, res_res]
    rw [← e2, e1]; abel
  obtain ⟨O₁, O₂, hO₁, hO₂, hLO₁, hLO₂, hdisj⟩ := SeparatedNhds.of_isCompact_isCompact
    (h₁.diff P.isOpen) (h₂.diff P.isOpen)
    (Set.disjoint_left.2 fun x hx1 hx2 => hx1.2 (hLP ⟨hx1.1, hx2.1⟩))
  let V₁' : Opens X := V₁ ⊓ (⟨O₁, hO₁⟩ ⊔ P)
  let V₂' : Opens X := V₂ ⊓ (⟨O₂, hO₂⟩ ⊔ P)
  have hV₁' : V₁' ≤ V₁ := inf_le_left
  have hV₂' : V₂' ≤ V₂ := inf_le_left
  have hint : V₁' ⊓ V₂' ≤ P := by
    rintro x ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd h2 (Set.disjoint_left.1 hdisj h1)
      · exact h2
    · exact h1
  have hcov₁ : L₁ ⊆ V₁' := fun x hx => ⟨hL₁ hx, by
    by_cases hxP : x ∈ P
    · exact Or.inr hxP
    · exact Or.inl (hLO₁ ⟨hx, hxP⟩)⟩
  have hcov₂ : L₂ ⊆ V₂' := fun x hx => ⟨hL₂ hx, by
    by_cases hxP : x ∈ P
    · exact Or.inr hxP
    · exact Or.inl (hLO₂ ⟨hx, hxP⟩)⟩
  obtain ⟨t, htl, htr⟩ := glue2 S.X₂ (le_sup_left : V₁' ≤ V₁' ⊔ V₂') le_sup_right le_rfl
    (S.X₂.obj.map (homOfLE hV₁').op t₁) (S.X₂.obj.map (homOfLE hV₂').op t₂') (by
      rw [res_res, res_res, ← res_res S.X₂ hint hP₁, hP, res_res])
  have hVW : V₁' ⊔ V₂' ≤ W := sup_le (hV₁'.trans hV₁) (hV₂'.trans hV₂)
  refine ⟨V₁' ⊔ V₂', Set.union_subset_union hcov₁ hcov₂, hVW, t, ?_⟩
  apply S.X₃.eq_of_locally_eq₂ (homOfLE (le_sup_left : V₁' ≤ V₁' ⊔ V₂'))
    (homOfLE le_sup_right) le_rfl
  · rw [← nat_res, htl, nat_res, ht₁, res_res, res_res]
  · rw [← nat_res, htr, nat_res, ht₂', res_res, res_res]

/-! ### Part (a) -/

private lemma isCSoft_of_isFlasque (F : TopCat.Sheaf (ModuleCat.{0} R) X) (hF : F.IsFlasque) :
    IsCSoft F := by
  intro K _ W hKW s
  have : Epi (F.obj.map (homOfLE (le_top : W ≤ ⊤)).op) := hF.epi _
  obtain ⟨t, ht⟩ := (ModuleCat.epi_iff_surjective _).mp this s
  exact ⟨t, W, hKW, le_rfl, by rw [ht, res_self]⟩

/-- The presheaf of discontinuous sections `U ↦ ∏_{x ∈ U} F_x`. -/
private noncomputable def discSections (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    TopCat.Presheaf (ModuleCat.{0} R) X where
  obj U := ModuleCat.of R ((x : U.unop) → F.presheaf.stalk x)
  map i := ModuleCat.ofHom
    { toFun := fun s x => s (i.unop x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private lemma isSheaf_discSections (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (discSections F).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget (ModuleCat.{0} R))]
  exact TopCat.Presheaf.toTypes_isSheaf X (fun x => F.presheaf.stalk x)

private noncomputable def godement (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    TopCat.Sheaf (ModuleCat.{0} R) X :=
  ⟨discSections F, isSheaf_discSections F⟩

private noncomputable def godementι (F : TopCat.Sheaf (ModuleCat.{0} R) X) : F ⟶ godement F :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom (LinearMap.pi fun x => (F.presheaf.germ U.unop x.1 x.2).hom)
      naturality _ _ i := by
        ext s; funext x
        exact TopCat.Presheaf.germ_res_apply' F.presheaf i x.1 x.2 s }

private lemma isFlasque_godement (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (godement F).IsFlasque where
  epi {U V} i := by
    rw [ModuleCat.epi_iff_surjective]
    intro s
    classical
    refine ⟨fun x => if h : x.1 ∈ V.unop then s ⟨x.1, h⟩ else 0, ?_⟩
    funext x
    change (if h : x.1 ∈ V.unop then s ⟨x.1, h⟩ else 0) = s x
    simp [x.2]

private lemma mono_godementι (F : TopCat.Sheaf (ModuleCat.{0} R) X) : Mono (godementι F) := by
  have : Mono (godementι F).hom := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun U => ?_
    rw [ModuleCat.mono_iff_injective]
    intro s t h
    exact TopCat.Presheaf.section_ext F U.unop s t fun x hx => congrFun h ⟨x, hx⟩
  exact (TopCat.Sheaf.forget (ModuleCat.{0} R) X).mono_of_mono_map this

private lemma isCSoft_of_injective (F : TopCat.Sheaf (ModuleCat.{0} R) X) [Injective F] :
    IsCSoft F := by
  intro K hK W hKW s
  have := mono_godementι F
  let r : godement F ⟶ F := Injective.factorThru (𝟙 F) (godementι F)
  have hr : godementι F ≫ r = 𝟙 F := Injective.comp_factorThru _ _
  obtain ⟨t, V, hKV, hVW, ht⟩ := isCSoft_of_isFlasque (godement F) (isFlasque_godement F) K hK W
    hKW ((godementι F).hom.app (op W) s)
  refine ⟨r.hom.app (op ⊤) t, V, hKV, hVW, ?_⟩
  rw [← nat_res, ht, ← nat_res, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
  have : (godementι F).hom ≫ r.hom = 𝟙 _ := congrArg (·.hom) hr
  rw [this]
  rfl

/-! ### Part (b) -/

private lemma liftsNear_empty {S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X)} {W : Opens X}
    (s : S.X₃.obj.obj (op W)) : LiftsNear S s ∅ := by
  have := ModuleCat.subsingleton_of_isZero S.X₃.isTerminalOfEmpty.isZero
  exact ⟨⊥, Set.empty_subset _, bot_le, 0, Subsingleton.elim _ _⟩

private lemma liftsNear_of_isCompact [LocallyCompactSpace X] [T2Space X]
    {S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X)} (hS : S.ShortExact) (hA : IsCSoft S.X₁)
    {W : Opens X} (s : S.X₃.obj.obj (op W)) {K : Set X} (hK : IsCompact K) (hKW : K ⊆ W) :
    LiftsNear S s K := by
  have := hS.epi_g
  suffices h : ∃ L, IsCompact L ∧ K ⊆ L ∧ LiftsNear S s L by
    obtain ⟨L, -, hKL, V, hLV, hVW, t, ht⟩ := h
    exact ⟨V, hKL.trans hLV, hVW, t, ht⟩
  refine hK.induction_on (p := fun T => ∃ L, IsCompact L ∧ T ⊆ L ∧ LiftsNear S s L)
    ⟨∅, isCompact_empty, subset_rfl, liftsNear_empty s⟩
    (fun T T' hTT' ⟨L, hL, hT'L, p⟩ => ⟨L, hL, hTT'.trans hT'L, p⟩)
    (fun T T' ⟨L, hL, hTL, p⟩ ⟨L', hL', hTL', p'⟩ =>
      ⟨L ∪ L', hL.union hL', Set.union_subset_union hTL hTL', liftsNear_union hS hA s hL hL' p p'⟩)
    (fun x hx => ?_)
  obtain ⟨V, hVW, hxV, t, ht⟩ := locally_surjective S.g s x (hKW hx)
  obtain ⟨N, hN, hxN, hNV⟩ := exists_compact_subset V.isOpen hxV
  exact ⟨N, mem_nhdsWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hxN), N, hN, subset_rfl,
    V, hNV, hVW, t, ht⟩

private lemma isCSoft_X₃ [LocallyCompactSpace X] [T2Space X]
    {S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X)} (hS : S.ShortExact) (hA : IsCSoft S.X₁)
    (hB : IsCSoft S.X₂) : IsCSoft S.X₃ := by
  intro K hK W hKW s
  obtain ⟨V, hKV, hVW, t, ht⟩ := liftsNear_of_isCompact hS hA s hK hKW
  obtain ⟨t', V', hKV', hV'V, ht'⟩ := hB K hK V hKV t
  refine ⟨S.g.hom.app (op ⊤) t', V', hKV', hV'V.trans hVW, ?_⟩
  rw [← nat_res, ht', nat_res, ht, res_res]

private lemma exists_res_eq_zero_of_germ (F : TopCat.Sheaf (ModuleCat.{0} R) X) {U : Opens X}
    (s : F.obj.obj (op U)) {x : X} (hx : x ∈ U) (h : F.presheaf.germ U x hx s = 0) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧ F.obj.map (homOfLE hVU).op s = 0 := by
  rw [← map_zero (ConcreteCategory.hom (F.presheaf.germ U x hx))] at h
  obtain ⟨V, hxV, i, j, e⟩ := TopCat.Presheaf.germ_eq F.presheaf x hx hx s 0 h
  exact ⟨V, i.le, hxV, by rw [show homOfLE i.le = i from rfl, e, map_zero]⟩

private lemma germ_eq_zero_of_res (F : TopCat.Sheaf (ModuleCat.{0} R) X) {U V : Opens X}
    (hVU : V ≤ U) (s : F.obj.obj (op U)) {x : X} (hxV : x ∈ V)
    (h : F.obj.map (homOfLE hVU).op s = 0) : F.presheaf.germ U x (hVU hxV) s = 0 := by
  rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVU) x hxV s]
  erw [h]
  exact map_zero _

private lemma res_eq_zero_of_germ (F : TopCat.Sheaf (ModuleCat.{0} R) X) {U V : Opens X}
    (hVU : V ≤ U) (s : F.obj.obj (op U))
    (h : ∀ x (hx : x ∈ V), F.presheaf.germ U x (hVU hx) s = 0) :
    F.obj.map (homOfLE hVU).op s = 0 :=
  TopCat.Presheaf.section_ext F V _ 0 fun x hx => by
    rw [map_zero]; erw [TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVU) x hx s]
    exact h x hx

private lemma germ_eq_zero_of_mono {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ G) [Mono φ]
    {U : Opens X} (s : F.obj.obj (op U)) {x : X} (hx : x ∈ U)
    (h : G.presheaf.germ U x hx (φ.hom.app (op U) s) = 0) : F.presheaf.germ U x hx s = 0 := by
  obtain ⟨V, hVU, hxV, e⟩ := exists_res_eq_zero_of_germ G _ hx h
  rw [← nat_res] at e
  exact germ_eq_zero_of_res F hVU s hxV (injective_app φ V (by rw [e, map_zero]))

/-- A compactly supported section of `S.X₃` lifts to a compactly supported section of `S.X₂`. -/
private lemma exists_compactSupport_lift [LocallyCompactSpace X] [T2Space X]
    {S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X)} (hS : S.ShortExact) (hA : IsCSoft S.X₁)
    (s : S.X₃.obj.obj (op ⊤)) {K : Set X} (hK : IsCompact K)
    (hs : ∀ x ∉ K, S.X₃.presheaf.germ ⊤ x trivial s = 0) :
    ∃ (u : S.X₂.obj.obj (op ⊤)) (L : Set X), IsCompact L ∧
      (∀ x ∉ L, S.X₂.presheaf.germ ⊤ x trivial u = 0) ∧ S.g.hom.app (op ⊤) u = s := by
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  let W : Opens X := ⟨interior L, isOpen_interior⟩
  let Z : Opens X := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  have hsZ : S.X₃.obj.map (homOfLE (le_top : Z ≤ ⊤)).op s = 0 :=
    res_eq_zero_of_germ S.X₃ le_top s fun x hx => hs x hx
  obtain ⟨V, hLV, _hVT, t, ht⟩ := liftsNear_of_isCompact hS hA s hL (Set.subset_univ L)
  have hB : IsCompact (L \ W) := hL.diff isOpen_interior
  let N : Opens X := V ⊓ Z
  have hBN : L \ W ⊆ N := fun x hx => ⟨hLV hx.1, fun hxK => hx.2 (hKL hxK)⟩
  have hNV : N ≤ V := inf_le_left
  have hNZ : N ≤ Z := inf_le_right
  have htN : S.g.hom.app (op N) (S.X₂.obj.map (homOfLE hNV).op t) = 0 := by
    rw [nat_res, ht, res_res, ← res_res S.X₃ hNZ le_top, hsZ, map_zero]
  obtain ⟨a, ha⟩ := sections_exact hS _ htN
  obtain ⟨a', P, hBP, hPN, ha'⟩ := hA (L \ W) hB N hBN a
  let t₁ := t - S.f.hom.app (op V) (S.X₁.obj.map (homOfLE (le_top : V ≤ ⊤)).op a')
  have ht₁ : S.g.hom.app (op V) t₁ = S.X₃.obj.map (homOfLE (le_top : V ≤ ⊤)).op s := by
    simp only [t₁, map_sub, g_f_apply, ht, sub_zero]
  have hPV : P ≤ V := hPN.trans hNV
  have ht₁P : S.X₂.obj.map (homOfLE hPV).op t₁ = 0 := by
    simp only [t₁, map_sub, nat_res, res_res]
    rw [← res_res S.X₂ hPN hNV, ← ha, ← nat_res, ← ha', nat_res, sub_self]
  let O₁ : Opens X := W ⊔ P
  let O₂ : Opens X := ⟨Lᶜ, hL.isClosed.isOpen_compl⟩
  have hWV : W ≤ V := fun x hx => hLV (interior_subset hx)
  have hO₁ : O₁ ≤ V := sup_le hWV hPV
  have hO₁₂ : O₁ ⊓ O₂ ≤ P := by
    rintro x ⟨hx | hx, hx'⟩
    · exact absurd (interior_subset hx) hx'
    · exact hx
  have hcov : (⊤ : Opens X) ≤ O₁ ⊔ O₂ := by
    intro x _
    by_cases hxL : x ∈ L
    · by_cases hxW : x ∈ interior L
      · exact Or.inl (Or.inl hxW)
      · exact Or.inl (Or.inr (hBP ⟨hxL, hxW⟩))
    · exact Or.inr hxL
  have hO₂Z : O₂ ≤ Z := fun x hx hxK => hx (hKL hxK |> interior_subset)
  obtain ⟨u, hu₁, hu₂⟩ := glue2 S.X₂ (le_top : O₁ ≤ ⊤) (le_top : O₂ ≤ ⊤) hcov
    (S.X₂.obj.map (homOfLE hO₁).op t₁) 0 (by
      rw [map_zero, res_res, ← res_res S.X₂ hO₁₂ hPV, ht₁P, map_zero])
  refine ⟨u, L, hL, fun x hx => ?_, ?_⟩
  · exact germ_eq_zero_of_res S.X₂ (le_top : O₂ ≤ ⊤) u (x := x) hx hu₂
  · apply S.X₃.eq_of_locally_eq₂ (homOfLE (le_top : O₁ ≤ ⊤)) (homOfLE (le_top : O₂ ≤ ⊤)) hcov
    · rw [← nat_res, hu₁, nat_res, ht₁, res_res]
    · rw [← nat_res, hu₂, map_zero, ← res_res S.X₃ hO₂Z le_top, hsZ, map_zero]

/-- `Γ_c` takes a short exact sequence with c-soft first term to a short exact sequence. -/
private lemma shortExact_map_compactSupportSections [LocallyCompactSpace X] [T2Space X]
    {S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X)} (hS : S.ShortExact)
    (hA : IsCSoft S.X₁) : (S.map (compactSupportSectionsFunctor R)).ShortExact := by
  have := hS.mono_f
  refine @ShortComplex.ShortExact.mk _ _ _ _ ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    rintro ⟨s, K, hK, hs⟩ h
    have h' : S.g.hom.app (op ⊤) s = 0 := congrArg Subtype.val h
    obtain ⟨a, ha⟩ := sections_exact hS s h'
    refine ⟨⟨a, K, hK, fun x hx => germ_eq_zero_of_mono S.f a trivial ?_⟩, Subtype.ext ha⟩
    rw [ha]
    exact hs x hx
  · rw [ModuleCat.mono_iff_injective]
    rintro ⟨s, _⟩ ⟨t, _⟩ h
    exact Subtype.ext (injective_app S.f ⊤ (congrArg Subtype.val h))
  · rw [ModuleCat.epi_iff_surjective]
    rintro ⟨s, K, hK, hs⟩
    obtain ⟨u, L, hL, hu, hus⟩ := exists_compactSupport_lift hS hA s hK hs
    exact ⟨⟨u, L, hL, hu⟩, Subtype.ext hus⟩

/-! ### Part (c) -/

private lemma add_app_apply {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (φ ψ : F ⟶ G) (U : Opens X)
    (s : F.obj.obj (op U)) :
    (φ + ψ).hom.app (op U) s = φ.hom.app (op U) s + ψ.hom.app (op U) s := by
  have : (φ + ψ).hom = φ.hom + ψ.hom :=
    (TopCat.Sheaf.forget (ModuleCat.{0} R) X).map_add (f := φ) (g := ψ)
  rw [this]
  rfl

private lemma comp_app_apply {F G H : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ G) (ψ : G ⟶ H)
    (U : Opens X) (s : F.obj.obj (op U)) :
    (φ ≫ ψ).hom.app (op U) s = ψ.hom.app (op U) (φ.hom.app (op U) s) := rfl

/-- A sheaf decomposing as `p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙` through two c-soft sheaves is c-soft. -/
private lemma isCSoft_of_decomp {F A B : TopCat.Sheaf (ModuleCat.{0} R) X} (hA : IsCSoft A)
    (hB : IsCSoft B) (i₁ : A ⟶ F) (p₁ : F ⟶ A) (i₂ : B ⟶ F) (p₂ : F ⟶ B)
    (h : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 F) : IsCSoft F := by
  intro K hK W hKW s
  obtain ⟨ta, Va, hKVa, hVaW, hta⟩ := hA K hK W hKW (p₁.hom.app _ s)
  obtain ⟨tb, Vb, hKVb, hVbW, htb⟩ := hB K hK W hKW (p₂.hom.app _ s)
  have hV : Va ⊓ Vb ≤ W := inf_le_left.trans hVaW
  refine ⟨i₁.hom.app _ ta + i₂.hom.app _ tb, Va ⊓ Vb, fun x hx => ⟨hKVa hx, hKVb hx⟩, hV, ?_⟩
  have ea : A.obj.map (homOfLE (le_top : Va ⊓ Vb ≤ ⊤)).op ta =
      p₁.hom.app _ (F.obj.map (homOfLE hV).op s) := by
    rw [← res_res A inf_le_left le_top, hta, res_res, nat_res]
  have eb : B.obj.map (homOfLE (le_top : Va ⊓ Vb ≤ ⊤)).op tb =
      p₂.hom.app _ (F.obj.map (homOfLE hV).op s) := by
    rw [← res_res B inf_le_right le_top, htb, res_res, nat_res]
  rw [map_add, ← nat_res, ← nat_res, ea, eb, ← comp_app_apply, ← comp_app_apply,
    ← add_app_apply, h]
  rfl

private lemma isCSoft_of_isZero {F : TopCat.Sheaf (ModuleCat.{0} R) X} (hF : IsZero F) :
    IsCSoft F :=
  isCSoft_of_decomp (isCSoft_of_isFlasque _ (isFlasque_godement F))
    (isCSoft_of_isFlasque _ (isFlasque_godement F)) 0 0 0 0 (hF.eq_of_src _ _)

private lemma isCSoft_of_iso {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (e : F ≅ G)
    (hF : IsCSoft F) : IsCSoft G :=
  isCSoft_of_decomp hF hF e.hom e.inv 0 0 (by simp)

/-- `Γ_c` of a bounded below acyclic complex of c-soft sheaves is acyclic. -/
private lemma acyclic_map_of_isCSoft [LocallyCompactSpace X] [T2Space X]
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℤ) (n₀ : ℤ) [K.IsStrictlyGE n₀]
    (hK : K.Acyclic) (hC : ∀ n, IsCSoft (K.X n)) :
    (((compactSupportSectionsFunctor R).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  let Z : ℤ → TopCat.Sheaf (ModuleCat.{0} R) X := fun m => kernel (K.d m (m + 1))
  let g : ∀ n m, K.X n ⟶ Z m := fun n m => kernel.lift _ (K.d n m) (K.d_comp_d _ _ _)
  have hg : ∀ n m, g n m ≫ kernel.ι _ = K.d n m := fun n m => kernel.lift_ι _ _ _
  let S : ∀ n m : ℤ, n + 1 = m → ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X) := fun n m _ =>
    ShortComplex.mk (kernel.ι (K.d n (n + 1))) (g n m) (by
      rw [← cancel_mono (kernel.ι (K.d m (m + 1))), Category.assoc, hg, zero_comp]
      subst ‹n + 1 = m›; exact kernel.condition _)
  have hS : ∀ (n m : ℤ) (h : n + 1 = m), (S n m h).ShortExact := by
    intro n m h
    subst h
    have hex : (K.sc' n (n + 1) (n + 1 + 1)).Exact :=
      (K.exactAt_iff' n (n + 1) (n + 1 + 1) (by simp) (by simp)).mp (hK _)
    have hepi : Epi (g n (n + 1)) := hex.epi_kernelLift
    refine ShortComplex.ShortExact.mk' ?_ inferInstance hepi
    let S' : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X) :=
      ShortComplex.mk (kernel.ι (K.d n (n + 1))) (K.d n (n + 1)) (kernel.condition _)
    let φ : S n (n + 1) rfl ⟶ S' :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι _
        comm₁₂ := by simp [S, S']
        comm₂₃ := by simp [S, S', hg] }
    have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
    exact S'.exact_of_f_is_kernel (kernelIsKernel _)
  have hZ : ∀ m, IsCSoft (Z m) := by
    have base : ∀ m, m ≤ n₀ - 1 → IsCSoft (Z m) := fun m hm =>
      isCSoft_of_isZero (IsZero.of_mono (kernel.ι _) (K.isZero_of_isStrictlyGE n₀ m (by lia)))
    intro m
    by_cases hm : m ≤ n₀ - 1
    · exact base m hm
    · refine Int.leInduction (m := n₀ - 1) (motive := fun k _ => IsCSoft (Z k)) (base _ le_rfl)
        (fun k _ hk => ?_) m (by lia)
      exact isCSoft_X₃ (hS k (k + 1) rfl) hk (hC k)
  have hΓ : ∀ (n m : ℤ) (h : n + 1 = m),
      ((S n m h).map (compactSupportSectionsFunctor R)).ShortExact := fun n m h =>
    shortExact_map_compactSupportSections (hS n m h) (hZ n)
  intro n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro s hs
  let Γ := compactSupportSectionsFunctor R (X := X)
  have h1 : Γ.map (g n (n + 1)) s = 0 := by
    apply (ModuleCat.mono_iff_injective _).mp (hΓ (n + 1) (n + 1 + 1) rfl).mono_f
    rw [map_zero]
    change (Γ.map (g n (n + 1)) ≫ Γ.map (kernel.ι (K.d (n + 1) (n + 1 + 1)))) s = 0
    rw [← Γ.map_comp, hg]
    exact hs
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hΓ n (n + 1) rfl).exact s h1
  obtain ⟨t, ht⟩ := (ModuleCat.epi_iff_surjective _).mp (hΓ (n - 1) n (by lia)).epi_g z
  refine ⟨t, ?_⟩
  change Γ.map (K.d (n - 1) n) t = s
  rw [← hg (n - 1) n, Γ.map_comp]
  change Γ.map (kernel.ι (K.d n (n + 1))) (Γ.map (g (n - 1) n) t) = s
  change Γ.map (g (n - 1) n) t = z at ht
  rwa [ht]

private lemma quasiIso_iff_acyclic_mappingCone {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

/-- `Γ_c` takes a quasi-isomorphism of bounded below complexes of c-soft sheaves to a
quasi-isomorphism. -/
private lemma quasiIso_map_of_isCSoft [LocallyCompactSpace X] [T2Space X]
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℤ} (f : K ⟶ L) [QuasiIso f]
    (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] (hK : ∀ n, IsCSoft (K.X n))
    (hL : ∀ n, IsCSoft (L.X n)) :
    QuasiIso (((compactSupportSectionsFunctor R).mapHomologicalComplex (.up ℤ)).map f) := by
  have : (CochainComplex.mappingCone f).IsStrictlyGE (min (n₁ - 1) n₂) :=
    CochainComplex.isStrictlyGE_mappingCone f n₁ n₂ _ (by lia) (by lia)
  have hc : (CochainComplex.mappingCone f).Acyclic :=
    (quasiIso_iff_acyclic_mappingCone f).mp inferInstance
  have hX : ∀ n, IsCSoft ((CochainComplex.mappingCone f).X n) := fun n =>
    isCSoft_of_decomp (hK (n + 1)) (hL n) ((CochainComplex.mappingCone.inl f).v (n + 1) n (by lia))
      ((CochainComplex.mappingCone.fst f).1.v n (n + 1) rfl)
      ((CochainComplex.mappingCone.inr f).f n)
      ((CochainComplex.mappingCone.snd f).v n n (add_zero n))
      (CochainComplex.mappingCone.id_X f n (n + 1) rfl)
  have hΓ := acyclic_map_of_isCSoft _ (min (n₁ - 1) n₂) hc hX
  rw [quasiIso_iff_acyclic_mappingCone]
  exact fun n => (hΓ n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso f _)

/-- The comparison `Γ_c(X, C) ⟶ RΓ_c(X, C)` is an isomorphism for a bounded below complex of
c-soft sheaves. -/
private lemma isIso_rightDerivedFunctorPlusUnit_app [LocallyCompactSpace X] [T2Space X]
    (C : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X))
    (hC : ∀ n, IsCSoft (C.obj.X n)) :
    IsIso ((compactSupportSectionsFunctor R).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient _).obj C)) := by
  obtain ⟨n, hn⟩ := C.property
  obtain ⟨L, hL, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective C n
  let Γ := compactSupportSectionsFunctor R (X := X)
  let α := Γ.rightDerivedFunctorPlusUnith
  let q := (HomotopyCategory.Plus.quotient _).map i
  have hi' : QuasiIso i.hom := (HomologicalComplex.mem_quasiIso_iff _).mp hi
  have hq : HomotopyCategory.Plus.quasiIso _ q := by
    rw [HomotopyCategory.Plus.quasiIso_iff]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff i.hom).mpr hi
  have hΓq : HomotopyCategory.Plus.quasiIso _ (Γ.mapHomotopyCategoryPlus.map q) := by
    rw [HomotopyCategory.Plus.quasiIso_iff]
    change HomotopyCategory.quasiIso _ _
      ((HomotopyCategory.quotient _ _).map ((Γ.mapHomologicalComplex _).map i.hom))
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
    have : ((InjectiveObject.ι _).mapCochainComplexPlus.obj L).obj.IsStrictlyGE n :=
      (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ _ _).mpr hL
    exact quasiIso_map_of_isCSoft i.hom n n hC
      (fun m => @isCSoft_of_injective _ _ _ _ (L.obj.X m).property)
  have h1 : IsIso (DerivedCategory.Plus.Qh.map q) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _) q hq
  have h2 : IsIso (DerivedCategory.Plus.Qh.map (Γ.mapHomotopyCategoryPlus.map q)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _) _ hΓq
  have h3 : IsIso (α.app ((HomotopyCategory.Plus.quotient _).obj
      ((InjectiveObject.ι _).mapCochainComplexPlus.obj L))) := inferInstance
  have nat := α.naturality q
  have h4 : IsIso ((DerivedCategory.Plus.Qh ⋙ Γ.rightDerivedFunctorPlus).map q) := by
    rw [Functor.comp_map]; infer_instance
  have : IsIso (α.app ((HomotopyCategory.Plus.quotient _).obj C) ≫
      (DerivedCategory.Plus.Qh ⋙ Γ.rightDerivedFunctorPlus).map q) := by
    rw [← nat]
    dsimp only [Functor.comp_map]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.Qh ⋙ Γ.rightDerivedFunctorPlus).map q)

section extend

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B] [HasZeroObject A]
  [HasZeroObject B] (G : A ⥤ B) [G.Additive] (K : HomologicalComplex A c)

/-- The degreewise comparison between `G` applied to an extension and the extension of `G`
applied to the complex. -/
private noncomputable def mapExtendXIso :
    ∀ o : Option ι, G.obj (HomologicalComplex.extend.X K o) ≅
      HomologicalComplex.extend.X ((G.mapHomologicalComplex c).obj K) o
  | some _ => Iso.refl _
  | none => IsZero.iso (G.map_isZero (HomologicalComplex.extend.isZero_X _ rfl))
      (HomologicalComplex.extend.isZero_X _ rfl)

private lemma mapExtendXIso_hom_d :
    ∀ o₁ o₂ : Option ι, (mapExtendXIso G K o₁).hom ≫
        HomologicalComplex.extend.d ((G.mapHomologicalComplex c).obj K) o₁ o₂ =
      G.map (HomologicalComplex.extend.d K o₁ o₂) ≫ (mapExtendXIso G K o₂).hom
  | none, _ => by
      simp only [HomologicalComplex.extend.d_none_eq_zero _ _ _ rfl, comp_zero, G.map_zero,
        zero_comp]
  | some a, some b => by
      change 𝟙 _ ≫ ((G.mapHomologicalComplex c).obj K).d a b = G.map (K.d a b) ≫ 𝟙 _
      simp
  | some _, none => by
      simp only [HomologicalComplex.extend.d_none_eq_zero' _ _ _ rfl, comp_zero, G.map_zero,
        zero_comp]

/-- `G` applied to an extension is the extension of `G` applied to the complex. -/
private noncomputable def mapExtendIso (e : c.Embedding c') :
    (G.mapHomologicalComplex c').obj (K.extend e) ≅
      ((G.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun i' => mapExtendXIso G K (e.r i'))
    (fun i' j' _ => mapExtendXIso_hom_d G K (e.r i') (e.r j'))

end extend

/-- `H^n_c(X, F)` is the cohomology of `Γ_c(X, C^•)` for a c-soft resolution `F → C^•`. -/
private lemma nonempty_iso_homology_of_resolution [LocallyCompactSpace X] [T2Space X]
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) (C : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    (ι : (CochainComplex.single₀ _).obj F ⟶ C) [QuasiIso ι] (hC : ∀ n, IsCSoft (C.X n))
    (n : ℕ) :
    Nonempty (compactSupportCohomology R n F ≅
      (((compactSupportSectionsFunctor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology
        n) := by
  let Γ := compactSupportSectionsFunctor R (X := X)
  let e := ComplexShape.embeddingUpNat
  let C' : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℤ := C.extend e
  have : CochainComplex.IsStrictlyGE C' 0 := by dsimp [C', e]; infer_instance
  let ι' : (CochainComplex.singleFunctor _ 0).obj F ⟶ C' :=
    (HomologicalComplex.extendSingleIso e F 0 0 rfl).inv ≫ (e.extendFunctor _).map ι
  have : QuasiIso (HomologicalComplex.extendMap ι e) := inferInstance
  have : QuasiIso ι' := inferInstanceAs
    (QuasiIso ((HomologicalComplex.extendSingleIso e F 0 0 rfl).inv ≫
      HomologicalComplex.extendMap ι e))
  have hC' : ∀ m, IsCSoft (C'.X m) := by
    intro m
    by_cases hm : 0 ≤ m
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      exact isCSoft_of_iso (C.extendXIso e rfl).symm (hC k)
    · exact isCSoft_of_isZero (C.isZero_extend_X e m fun i hi => hm (by
        rw [← hi]; exact Int.natCast_nonneg i))
  let P : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X) := ⟨C', 0, inferInstance⟩
  let S : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X) :=
    ⟨(CochainComplex.singleFunctor _ 0).obj F, 0, inferInstance⟩
  let f : S ⟶ P := ObjectProperty.homMk ι'
  have hf : HomotopyCategory.Plus.quasiIso _ ((HomotopyCategory.Plus.quotient _).map f) := by
    rw [HomotopyCategory.Plus.quasiIso_iff]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff ι').mpr
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
  have : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map f)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _) _ hf
  have hα := isIso_rightDerivedFunctorPlusUnit_app P hC'
  let a : (DerivedCategory.Plus.singleFunctor _ 0).obj F ≅
      DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj S) :=
    DerivedCategory.Plus.ι.preimageIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F ≪≫
      (DerivedCategory.quotientCompQhIso (TopCat.Sheaf (ModuleCat.{0} R) X)).symm.app
        ((CochainComplex.singleFunctor _ 0).obj F))
  let b := asIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map f))
  let c :=
    (asIso (Γ.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient _).obj P))).symm
  let d : (DerivedCategory.Plus.homologyFunctor _ n).obj
      (DerivedCategory.Plus.Qh.obj (Γ.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj P))) ≅
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C').homology n :=
    (DerivedCategory.homologyFunctorFactorsh _ n).app _ ≪≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} R) (ComplexShape.up ℤ) n).app
        ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C')
  let g := (HomologicalComplex.homologyFunctor _ _ (n : ℤ)).mapIso (mapExtendIso Γ C e)
  let h := HomologicalComplex.extendHomologyIso
    ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj C)
    e (j := n) (j' := (n : ℤ)) rfl
  exact ⟨(DerivedCategory.Plus.homologyFunctor _ n).mapIso
    (Γ.rightDerivedFunctorPlus.mapIso (a ≪≫ b) ≪≫ c) ≪≫ d ≪≫ g ≪≫ h⟩

end CSoftAcyclic

open CSoftAcyclic in
/-- **c-soft sheaves are `Γ_c`-acyclic.** On a locally compact Hausdorff space, call a sheaf
c-soft if sections over compact sets extend to global sections. Then (a) flasque and injective
sheaves are c-soft; (b) `Γ_c` is exact on short exact sequences whose first term is c-soft, and
c-softness passes to quotients of c-soft by c-soft; (c) c-soft sheaves have vanishing higher
compactly supported cohomology, `Γ_c` of a bounded below complex of c-soft sheaves computes its
derived functor through the canonical comparison, and `H^q_c(X, F) ≅ H^q(Γ_c(X, C^•))` for any
c-soft resolution `F → C^•`. -/
@[mmp "lem_mmp_compact_support_csoft_acyclic"]
public theorem compactSupportCohomology_of_isCSoft
    (R : Type) [CommRing R] (X : TopCat.{0}) [LocallyCompactSpace X] [T2Space X] :
    let IsCSoft : TopCat.Sheaf (ModuleCat.{0} R) X → Prop := fun F ↦
      ∀ K : Set X, IsCompact K → ∀ (W : Opens X), K ⊆ W →
        ∀ s : ((TopCat.Sheaf.forget _ X).obj F).obj (op W),
          ∃ (t : ((TopCat.Sheaf.forget _ X).obj F).obj (op ⊤)) (V : Opens X) (_ : K ⊆ V)
            (hVW : V ≤ W),
            (((TopCat.Sheaf.forget _ X).obj F).map (homOfLE le_top).op).hom t =
              (((TopCat.Sheaf.forget _ X).obj F).map (homOfLE hVW).op).hom s
    -- (a) flasque sheaves, and injective sheaves, are c-soft
    ((∀ F : TopCat.Sheaf (ModuleCat.{0} R) X, F.IsFlasque → IsCSoft F) ∧
      (∀ F : TopCat.Sheaf (ModuleCat.{0} R) X, Injective F → IsCSoft F)) ∧
    -- (b) exactness of `Γ_c` and c-softness of quotients
    (∀ S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X), S.ShortExact → IsCSoft S.X₁ →
      (S.map (compactSupportSectionsFunctor R)).ShortExact ∧ (IsCSoft S.X₂ → IsCSoft S.X₃)) ∧
    -- (c) acyclicity, the canonical comparison, and computation by c-soft resolutions
    (∀ F : TopCat.Sheaf (ModuleCat.{0} R) X, IsCSoft F → ∀ q : ℤ, 0 < q →
      Limits.IsZero (compactSupportCohomology R q F)) ∧
    (∀ C : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X),
      (∀ n, IsCSoft (C.obj.X n)) →
      IsIso ((compactSupportSectionsFunctor R).rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient _).obj C))) ∧
    (∀ (F : TopCat.Sheaf (ModuleCat.{0} R) X)
      (C : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
      (ι : (CochainComplex.single₀ _).obj F ⟶ C), QuasiIso ι → (∀ n, IsCSoft (C.X n)) →
      ∀ n : ℕ, Nonempty (compactSupportCohomology R n F ≅
        (((compactSupportSectionsFunctor R).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C).homology n)) := by
  intro IsCSoft'
  refine ⟨⟨fun F hF => isCSoft_of_isFlasque F hF, fun F hF => @isCSoft_of_injective _ _ _ F hF⟩,
    fun S hS hA => ⟨shortExact_map_compactSupportSections hS hA, fun hB => isCSoft_X₃ hS hA hB⟩,
    fun F hF q hq => ?_, fun C hC => isIso_rightDerivedFunctorPlusUnit_app C hC,
    fun F C ι hι hC n => nonempty_iso_homology_of_resolution F C ι hC n⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by lia⟩
  have hs : ∀ m, IsCSoft (((CochainComplex.single₀ _).obj F).X m) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      exact isCSoft_of_iso (HomologicalComplex.singleObjXSelf _ _ F).symm hF
    · exact isCSoft_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm)
  obtain ⟨e⟩ := nonempty_iso_homology_of_resolution F _ (𝟙 _) hs n
  refine IsZero.of_iso ?_ e
  refine (HomologicalComplex.ExactAt.of_isZero ?_).isZero_homology
  exact (compactSupportSectionsFunctor R).map_isZero
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia))

namespace ExtendByZero

variable (R : Type) [CommRing R] {X : TopCat.{0}} (U : Opens X)

private lemma isCocontinuous_functor :
    U.isOpenEmbedding.functor.IsCocontinuous (Opens.grothendieckTopology _)
      (Opens.grothendieckTopology X) where
  cover_lift {V} S hS y hy := by
    obtain ⟨W, f, hf, hW⟩ := hS (U.inclusion' y) ⟨y, hy, rfl⟩
    refine ⟨(Opens.map U.inclusion').obj W, homOfLE fun z hz => ?_, ?_, hW⟩
    · obtain ⟨z', hz', hzz'⟩ := f.le hz
      obtain rfl := U.isOpenEmbedding.injective hzz'
      exact hz'
    · have hle : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj W) ≤ W :=
        fun _ ⟨_, hz, e⟩ => e ▸ hz
      change S.arrows (U.isOpenEmbedding.functor.map _)
      rw [Subsingleton.elim (U.isOpenEmbedding.functor.map _) (homOfLE hle ≫ f)]
      exact S.downward_closed hf _

/-- Restriction `j^*`. -/
private noncomputable abbrev resF :
    TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U) :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafPushforwardContinuous _ _ _

/-- Extension by zero `j_!`. -/
private noncomputable abbrev extF :
    TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U) ⥤ TopCat.Sheaf (ModuleCat.{0} R) X :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafPullback _ _ _

private noncomputable abbrev adjF : extF R U ⊣ resF R U :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafAdjunctionContinuous _ _ _

private lemma isIso_ranCounit [Mono U.inclusion']
    (F : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ ⥤ ModuleCat.{0} R) :
    IsIso ((U.isOpenEmbedding.functor.op.ranAdjunction (ModuleCat.{0} R)).counit.app F) := by
  infer_instance

private lemma isIso_unit : IsIso (adjF R U).unit := by
  have := U.isOpenEmbedding.functor_isContinuous
  have := isCocontinuous_functor U
  have : Mono U.inclusion' := (TopCat.mono_iff_injective _).mpr U.isOpenEmbedding.injective
  let t : Adjunction.Triple (extF R U) (resF R U) _ :=
    ⟨adjF R U, U.isOpenEmbedding.functor.sheafAdjunctionCocontinuous (ModuleCat.{0} R) _ _⟩
  rw [show adjF R U = t.adj₁ from rfl, t.isIso_unit_iff_isIso_counit]
  have (F : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U)) :
      IsIso (t.adj₂.counit.app F) := by
    have h : IsIso ((sheafToPresheaf _ _).map (t.adj₂.counit.app F)) := by
      have e := Functor.sheafAdjunctionCocontinuous_counit_app_hom U.isOpenEmbedding.functor
        (ModuleCat.{0} R) (Opens.grothendieckTopology _) (Opens.grothendieckTopology X) F
      change IsIso (((U.isOpenEmbedding.functor.sheafAdjunctionCocontinuous (ModuleCat.{0} R)
        (Opens.grothendieckTopology _) (Opens.grothendieckTopology X)).counit.app F).hom)
      rw [e]
      exact isIso_ranCounit R U _
    exact isIso_of_fully_faithful (sheafToPresheaf _ _) _
  exact NatIso.isIso_of_isIso_app _

private lemma isZero_stalk_extF (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    (x : X) (hx : x ∉ U) : IsZero (((extF R U).obj G).presheaf.stalk x) := by
  classical
  rw [IsZero.iff_id_eq_zero]
  let A := ((extF R U).obj G).presheaf.stalk x
  let e := ((stalkSkyscraperSheafAdjunction x (C := ModuleCat.{0} R)).homEquiv
    ((extF R U).obj G) A).trans ((adjF R U).homEquiv G ((skyscraperSheafFunctor x).obj A))
  have : Subsingleton (G ⟶ (resF R U).obj ((skyscraperSheafFunctor x).obj A)) := by
    constructor
    intro f g
    apply Sheaf.hom_ext
    ext V : 2
    have hV : x ∉ U.isOpenEmbedding.functor.obj V.unop := fun ⟨y, _, hy⟩ => hx (hy ▸ y.2)
    exact (isTerminalSkyscraperSheafObjObjOfNotMem (A := A) (p₀ := x)
      (U := op (U.isOpenEmbedding.functor.obj V.unop)) hV).hom_ext _ _
  exact e.injective (Subsingleton.elim _ _)

/-! ### Restriction maps and gluing -/

section Restriction

variable {R} {Y : TopCat.{0}}

private lemma res_res (F : TopCat.Presheaf (ModuleCat.{0} R) Y) {A B C : Opens Y} (hAB : A ≤ B)
    (hBC : B ≤ C) (s : F.obj (op C)) :
    F.map (homOfLE hAB).op (F.map (homOfLE hBC).op s) = F.map (homOfLE (hAB.trans hBC)).op s := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp]
  rfl

/-- A germ vanishes iff the section vanishes on a neighbourhood. -/
private lemma germ_eq_zero_iff (F : TopCat.Presheaf (ModuleCat.{0} R) Y) {W : Opens Y} (x : Y)
    (hx : x ∈ W) (s : F.obj (op W)) :
    F.germ W x hx s = 0 ↔ ∃ (N : Opens Y) (_ : x ∈ N) (h : N ≤ W), F.map (homOfLE h).op s = 0 := by
  constructor
  · intro h0
    have h1 : F.germ W x hx s = F.germ W x hx 0 := by rw [h0, map_zero]
    obtain ⟨N, hN, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq F x hx hx s 0 h1
    exact ⟨N, hN, i₁.le, by rw [show homOfLE i₁.le = i₁ from rfl, e, map_zero]⟩
  · rintro ⟨N, hN, h, e⟩
    rw [← F.germ_res_apply (homOfLE h) x hN s, e, map_zero]

/-- Gluing two sections of a sheaf of modules. -/
private lemma glue2 (F : TopCat.Sheaf (ModuleCat.{0} R) Y) {A B : Opens Y}
    (a : F.obj.obj (op A)) (b : F.obj.obj (op B))
    (h : F.obj.map (homOfLE inf_le_left : A ⊓ B ⟶ A).op a =
      F.obj.map (homOfLE inf_le_right : A ⊓ B ⟶ B).op b) :
    ∃ s : F.obj.obj (op (A ⊔ B)), F.obj.map (homOfLE le_sup_left).op s = a ∧
      F.obj.map (homOfLE le_sup_right).op s = b :=
  CSoftAcyclic.glue2 F le_sup_left le_sup_right le_rfl a b h

private lemma eq_zero_of_germ (F : TopCat.Sheaf (ModuleCat.{0} R) Y) {W : Opens Y}
    (s : F.obj.obj (op W)) (h : ∀ x (hx : x ∈ W), F.presheaf.germ W x hx s = 0) : s = 0 :=
  TopCat.Presheaf.section_ext F W s 0 fun x hx => by rw [h x hx, map_zero]

private lemma germ_eq_of_res_eq' (F : TopCat.Sheaf (ModuleCat.{0} R) Y) {A C : Opens Y}
    (hA : C ≤ A) {a : F.obj.obj (op A)} {b : F.obj.obj (op C)}
    (e : F.obj.map (homOfLE hA).op a = b) (y : Y) (hy : y ∈ C) :
    F.presheaf.germ A y (hA hy) a = F.presheaf.germ C y hy b := by
  rw [← F.presheaf.germ_res_apply (homOfLE hA) y hy]
  exact congrArg _ e

private lemma res_eq_res_of_germ (F : TopCat.Sheaf (ModuleCat.{0} R) Y) {A B C : Opens Y}
    (hA : C ≤ A) (hB : C ≤ B) (a : F.obj.obj (op A)) (b : F.obj.obj (op B))
    (h : ∀ y (hy : y ∈ C), F.presheaf.germ A y (hA hy) a = F.presheaf.germ B y (hB hy) b) :
    F.obj.map (homOfLE hA).op a = F.obj.map (homOfLE hB).op b :=
  TopCat.Presheaf.section_ext F C _ _ fun y hy => by
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact h y hy

end Restriction

/-! ### Sections of the extension by zero -/

section Rho

variable {R U}

private abbrev pre (W : Opens X) : Opens ((Opens.toTopCat X).obj U) :=
  (Opens.map U.inclusion').obj W

private lemma functor_pre_le (W : Opens X) : U.isOpenEmbedding.functor.obj (pre (U := U) W) ≤ W :=
  fun _ ⟨_, h, e⟩ => e ▸ h

private lemma functor_le (V : Opens ((Opens.toTopCat X).obj U)) :
    U.isOpenEmbedding.functor.obj V ≤ U :=
  fun _ ⟨y, _, e⟩ => e ▸ y.2

private lemma le_functor_pre {W : Opens X} (hW : W ≤ U) :
    W ≤ U.isOpenEmbedding.functor.obj (pre (U := U) W) :=
  fun x hx => ⟨⟨x, hW hx⟩, hx, rfl⟩

private lemma pre_mono {W W' : Opens X} (h : W' ≤ W) : pre (U := U) W' ≤ pre W :=
  (Opens.map _).monotone h

private lemma pre_functor_le (V : Opens ((Opens.toTopCat X).obj U)) :
    pre (U := U) (U.isOpenEmbedding.functor.obj V) ≤ V := by
  rintro y ⟨z, hz, e⟩
  obtain rfl := U.isOpenEmbedding.injective e
  exact hz

variable (R U) in
/-- The unit `G ⟶ j^* j_! G` on sections over an open of `U`, as an isomorphism. -/
private noncomputable def unitApp (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    (V : Opens ((Opens.toTopCat X).obj U)) :
    G.obj.obj (op V) ≅ ((extF R U).obj G).obj.obj (op (U.isOpenEmbedding.functor.obj V)) :=
  haveI := isIso_unit R U
  ((sheafToPresheaf _ _).mapIso ((asIso (adjF R U).unit).app G)).app (op V)

private lemma unitApp_hom (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    (V : Opens ((Opens.toTopCat X).obj U)) :
    (unitApp R U G V).hom = ((adjF R U).unit.app G).hom.app (op V) := rfl

private lemma unitApp_injective (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    (V : Opens ((Opens.toTopCat X).obj U)) : Function.Injective (unitApp R U G V).hom := by
  intro a b h
  have := congrArg (unitApp R U G V).inv h
  rwa [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at this

private lemma unitApp_res (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    {V V' : Opens ((Opens.toTopCat X).obj U)} (h : V' ≤ V) (t : G.obj.obj (op V)) :
    ((extF R U).obj G).obj.map (homOfLE (U.isOpenEmbedding.functor.monotone h)).op
        ((unitApp R U G V).hom t) = (unitApp R U G V').hom (G.obj.map (homOfLE h).op t) := by
  rw [unitApp_hom, unitApp_hom]
  exact (NatTrans.naturality_apply ((adjF R U).unit.app G).hom (homOfLE h).op t).symm

private lemma unitApp_naturality {G G' : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U)}
    (φ : G ⟶ G') (V : Opens ((Opens.toTopCat X).obj U)) (t : G.obj.obj (op V)) :
    (unitApp R U G' V).hom (φ.hom.app (op V) t) =
      ((extF R U).map φ).hom.app (op (U.isOpenEmbedding.functor.obj V))
        ((unitApp R U G V).hom t) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun f => f.hom) ((adjF R U).unit.naturality φ)) (op V)) t

variable (R U) in
/-- Restriction of a section of `j_! G` over `W` to `W ∩ U`, read as a section of `G`. -/
private noncomputable def ρ (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    (W : Opens X) : ((extF R U).obj G).obj.obj (op W) ⟶ G.obj.obj (op (pre (U := U) W)) :=
  ((extF R U).obj G).obj.map (homOfLE (functor_pre_le W)).op ≫ (unitApp R U G (pre W)).inv

private lemma unitApp_ρ (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    (W : Opens X) (s : ((extF R U).obj G).obj.obj (op W)) :
    (unitApp R U G (pre W)).hom (ρ R U G W s) =
      ((extF R U).obj G).obj.map (homOfLE (functor_pre_le W)).op s := by
  simp only [ρ, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

private lemma ρ_res (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    {W W' : Opens X} (h : W' ≤ W) (s : ((extF R U).obj G).obj.obj (op W)) :
    ρ R U G W' (((extF R U).obj G).obj.map (homOfLE h).op s) =
      G.obj.map (homOfLE (pre_mono h)).op (ρ R U G W s) := by
  apply unitApp_injective
  rw [unitApp_ρ, ← unitApp_res, unitApp_ρ, res_res, res_res]

/-- If a section of `j_! G` vanishes on `W' ⊆ W`, its restriction to `U` vanishes on `W' ∩ U`. -/
private lemma ρ_res_eq_zero (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    {W W' : Opens X} (h : W' ≤ W) {s : ((extF R U).obj G).obj.obj (op W)}
    (hs : ((extF R U).obj G).obj.map (homOfLE h).op s = 0) :
    G.obj.map (homOfLE (pre_mono h)).op (ρ R U G W s) = 0 := by
  rw [← ρ_res G h, hs, map_zero]

private lemma ρ_unitApp (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    (V : Opens ((Opens.toTopCat X).obj U)) (t : G.obj.obj (op V)) :
    ρ R U G (U.isOpenEmbedding.functor.obj V) ((unitApp R U G V).hom t) =
      G.obj.map (homOfLE (pre_functor_le V)).op t := by
  apply unitApp_injective
  rw [unitApp_ρ, ← unitApp_res]

private lemma ρ_naturality {G G' : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U)}
    (φ : G ⟶ G') (W : Opens X) (s : ((extF R U).obj G).obj.obj (op W)) :
    ρ R U G' W (((extF R U).map φ).hom.app (op W) s) = φ.hom.app (op (pre W)) (ρ R U G W s) := by
  apply unitApp_injective
  rw [unitApp_ρ, unitApp_naturality, unitApp_ρ]
  exact (NatTrans.naturality_apply ((extF R U).map φ).hom (homOfLE (functor_pre_le W)).op s).symm

private lemma subsingleton_stalk (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    (x : X) (hx : x ∉ U) : Subsingleton (((extF R U).obj G).presheaf.stalk x) :=
  ModuleCat.subsingleton_of_isZero (isZero_stalk_extF R U G x hx)

private lemma exists_nhds_res_eq_zero
    (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U)) {W : Opens X}
    (s : ((extF R U).obj G).obj.obj (op W)) (x : X) (hxW : x ∈ W) (hxU : x ∉ U) :
    ∃ (N : Opens X) (_ : x ∈ N) (h : N ≤ W), ((extF R U).obj G).obj.map (homOfLE h).op s = 0 := by
  have := subsingleton_stalk G x hxU
  exact (germ_eq_zero_iff _ x hxW s).mp (Subsingleton.elim _ _)

private lemma ρ_injective (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    (W : Opens X) : Function.Injective (ρ R U G W).hom := by
  refine (injective_iff_map_eq_zero (ρ R U G W).hom).mpr fun s hs => ?_
  refine eq_zero_of_germ _ s fun x hx => ?_
  by_cases hxU : x ∈ U
  · have hx' : x ∈ U.isOpenEmbedding.functor.obj (pre W) := ⟨⟨x, hxU⟩, hx, rfl⟩
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (functor_pre_le W)) x hx', ← unitApp_ρ]
    change _ = 0 at hs
    rw [show (ρ R U G W) s = 0 from hs, map_zero, map_zero]
  · have := subsingleton_stalk G x hxU
    exact Subsingleton.elim _ _

private lemma exists_ρ_eq (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    {W O : Opens X} (hWO : W ≤ U ⊔ O) (t : G.obj.obj (op (pre (U := U) W)))
    (ht : G.obj.map (homOfLE (pre_mono (inf_le_left : W ⊓ O ≤ W))).op t = 0) :
    ∃ s, ρ R U G W s = t := by
  have hcompat : ((extF R U).obj G).obj.map
      (homOfLE inf_le_left : U.isOpenEmbedding.functor.obj (pre W) ⊓ (W ⊓ O) ⟶ _).op
        ((unitApp R U G (pre W)).hom t) =
      ((extF R U).obj G).obj.map (homOfLE inf_le_right).op 0 := by
    rw [map_zero]
    apply ρ_injective
    rw [map_zero, ρ_res, ρ_unitApp, res_res]
    have hle : pre (U := U) (U.isOpenEmbedding.functor.obj (pre W) ⊓ (W ⊓ O)) ≤ pre (W ⊓ O) :=
      pre_mono inf_le_right
    rw [← res_res G.obj hle (pre_mono (inf_le_left : W ⊓ O ≤ W)), ht, map_zero]
  obtain ⟨σ, hσA, -⟩ := glue2 ((extF R U).obj G) _ _ hcompat
  have hW : W ≤ U.isOpenEmbedding.functor.obj (pre W) ⊔ (W ⊓ O) := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl ⟨⟨x, hxU⟩, hx, rfl⟩
    · exact Or.inr ⟨hx, (hWO hx).resolve_left hxU⟩
  refine ⟨((extF R U).obj G).obj.map (homOfLE hW).op σ, ?_⟩
  apply unitApp_injective
  rwa [unitApp_ρ, res_res]

end Rho

section Mono

variable {R} {Y : TopCat.{0}}

private lemma mono_of_injective {A B : TopCat.Sheaf (ModuleCat.{0} R) Y} (f : A ⟶ B)
    (h : ∀ W : Opens Y, Function.Injective (f.hom.app (op W))) : Mono f := by
  refine ⟨fun g₁ g₂ e => ?_⟩
  apply Sheaf.hom_ext
  ext W x
  apply h W.unop
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f => f.hom) e) W) x

end Mono

private lemma additive_extF : (extF R U).Additive := by
  have : (resF R U).Additive := ⟨fun {_ _ _ _} => by apply Sheaf.hom_ext; rfl⟩
  exact (adjF R U).left_adjoint_additive

private lemma mono_map_extF {G G' : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U)}
    (f : G ⟶ G') [Mono f] : Mono ((extF R U).map f) := by
  refine mono_of_injective _ fun W => (injective_iff_map_eq_zero _).mpr fun s hs => ?_
  apply ρ_injective (G := G) W
  rw [map_zero]
  apply CSoftAcyclic.injective_app f
  rw [map_zero, ← ρ_naturality]
  rw [hs, map_zero]

private lemma counit_injective (F : TopCat.Sheaf (ModuleCat.{0} R) X) (W : Opens X) :
    Function.Injective (((adjF R U).counit.app F).hom.app (op W)) := by
  refine (injective_iff_map_eq_zero _).mpr fun T hT => ?_
  apply ρ_injective (G := (resF R U).obj F) W
  rw [map_zero]
  have tri := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f => f.hom)
    ((adjF R U).right_triangle_components F)) (op (pre W))) (ρ R U _ W T)
  change ((adjF R U).counit.app F).hom.app (op (U.isOpenEmbedding.functor.obj (pre W)))
    ((unitApp R U _ (pre W)).hom (ρ R U _ W T)) = ρ R U _ W T at tri
  rw [unitApp_ρ] at tri
  have nat := NatTrans.naturality_apply ((adjF R U).counit.app F).hom
    (homOfLE (functor_pre_le (U := U) W)).op T
  rw [← tri]
  refine nat.trans ?_
  change F.obj.map _ ((((adjF R U).counit.app F).hom.app (op W)) T) = 0
  rw [hT, map_zero]

private lemma counit_surjective (F : TopCat.Sheaf (ModuleCat.{0} R) X) {W : Opens X} (hW : W ≤ U) :
    Function.Surjective (((adjF R U).counit.app F).hom.app (op W)) := by
  obtain ⟨V, rfl⟩ : ∃ V, U.isOpenEmbedding.functor.obj V = W :=
    ⟨pre W, le_antisymm (functor_pre_le W) (le_functor_pre hW)⟩
  intro y
  refine ⟨(unitApp R U _ V).hom y, ?_⟩
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f => f.hom)
    ((adjF R U).right_triangle_components F)) (op V)) y

/-! ### Compactly supported sections of the extension by zero -/

section Gamma

variable {R U}

/-- The germs of a compactly supported section of `j_! G` vanish, along `U`, off a compact
subset of `U`. -/
private lemma exists_isCompact_germ_eq_zero_of_notMem
    (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    (s : ((extF R U).obj G).obj.obj (op ⊤)) {L : Set X} (hL : IsCompact L)
    (hs : ∀ x ∉ L, ((extF R U).obj G).presheaf.germ ⊤ x (Opens.mem_top x) s = 0) :
    ∃ K : Set ((Opens.toTopCat X).obj U), IsCompact K ∧
      ∀ y ∉ K, ((extF R U).obj G).presheaf.germ ⊤ (U.inclusion' y) (Opens.mem_top _) s = 0 := by
  let S : Set X := {x | ((extF R U).obj G).presheaf.germ ⊤ x (Opens.mem_top x) s ≠ 0}
  have hSc : IsClosed S := by
    refine isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun x hx => ?_)
    have hx0 : ((extF R U).obj G).presheaf.germ ⊤ x (Opens.mem_top x) s = 0 := not_not.mp hx
    obtain ⟨N, hxN, hN, hsN⟩ := (germ_eq_zero_iff _ x _ s).mp hx0
    refine ⟨N, fun x' hx' => ?_, N.2, hxN⟩
    change ¬ ¬ _
    rw [not_not, ← TopCat.Presheaf.germ_res_apply _ (homOfLE hN) x' hx']
    exact (congrArg _ hsN).trans (map_zero _)
  have hSL : S ⊆ L := fun x hx => by_contra fun h => hx (hs x h)
  have hSU : S ⊆ Set.range U.inclusion' := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact ⟨⟨x, hxU⟩, rfl⟩
    · have := subsingleton_stalk G x hxU
      exact absurd (Subsingleton.elim _ _) hx
  refine ⟨U.inclusion' ⁻¹' S, (U.isOpenEmbedding.isInducing.isCompact_preimage_iff hSU).mpr
    (hL.of_isClosed_subset hSc hSL), fun y hy => not_not.mp hy⟩

variable (R U) in
/-- `Γ_c(X, j_! G) ⟶ Γ_c(U, G)`, restriction to `U`. -/
private noncomputable def gammaHom (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U)) :
    compactSupportSections R ((extF R U).obj G) →ₗ[R] compactSupportSections R G where
  toFun s := ⟨ρ R U G ⊤ s.1, by
    obtain ⟨L, hL, hs⟩ := s.2
    obtain ⟨K, hK, hK'⟩ := exists_isCompact_germ_eq_zero_of_notMem G s.1 hL hs
    refine ⟨K, hK, fun y hy => ?_⟩
    obtain ⟨N, hyN, hN, hsN⟩ := (germ_eq_zero_iff _ _ _ s.1).mp (hK' y hy)
    exact (germ_eq_zero_iff _ y _ _).mpr ⟨pre N, hyN, pre_mono hN, ρ_res_eq_zero G hN hsN⟩⟩
  map_add' s t := Subtype.ext (map_add _ _ _)
  map_smul' c s := Subtype.ext (map_smul _ _ _)

private lemma gammaHom_bijective [T2Space X]
    (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U)) :
    Function.Bijective (gammaHom R U G) := by
  refine ⟨fun s t h => Subtype.ext (ρ_injective G ⊤ (congrArg Subtype.val h)), fun t => ?_⟩
  obtain ⟨K, hK, ht⟩ := t.2
  let L : Set X := U.inclusion' '' K
  have hL : IsCompact L := hK.image U.inclusion'.hom.continuous
  let O : Opens X := ⟨Lᶜ, hL.isClosed.isOpen_compl⟩
  have hO : ∀ (N : Opens X), N ≤ O →
      G.obj.map (homOfLE (pre_mono (le_top : N ≤ ⊤))).op t.1 = 0 := by
    intro N hN
    refine eq_zero_of_germ G _ fun y hy => ?_
    refine (TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (pre_mono (le_top : N ≤ ⊤))) y hy
      t.1).trans ?_
    exact ht y fun hyK => hN hy ⟨y, hyK, rfl⟩
  have hWO : (⊤ : Opens X) ≤ U ⊔ O := by
    intro x _
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · exact Or.inr fun ⟨y, _, hy⟩ => hxU (hy ▸ y.2)
  obtain ⟨σ, hσ⟩ := exists_ρ_eq G hWO t.1 (hO _ inf_le_right)
  refine ⟨⟨σ, L, hL, fun x hx => ?_⟩, Subtype.ext hσ⟩
  refine (germ_eq_zero_iff _ x _ σ).mpr ⟨O, hx, le_top, ρ_injective G O ?_⟩
  rw [ρ_res, hσ, hO O le_rfl, map_zero]

variable (R U) in
/-- `Γ_c(X, j_! G) ≅ Γ_c(U, G)`, naturally in `G`. -/
private noncomputable def gammaIso [T2Space X] :
    extF R U ⋙ compactSupportSectionsFunctor R ≅ compactSupportSectionsFunctor R :=
  NatIso.ofComponents
    (fun G => (LinearEquiv.ofBijective (gammaHom R U G) (gammaHom_bijective G)).toModuleIso)
    (fun {G G'} f => by
      ext s
      exact Subtype.ext (ρ_naturality f ⊤ s.1))

end Gamma

/-! ### The main lemmas, stated for `extF` -/

variable {R} in
/-- c-softness, in the form used by the statement. -/
private def CSoft {Y : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} R) Y) : Prop :=
  ∀ K : Set Y, IsCompact K → ∀ W : Opens Y, K ⊆ W →
    ∀ s : ((TopCat.Sheaf.forget _ Y).obj F).obj (op W),
      ∃ t : ((TopCat.Sheaf.forget _ Y).obj F).obj (op ⊤), ∃ (W' : Opens Y) (h : W' ≤ W),
        K ⊆ W' ∧ ((TopCat.Sheaf.forget _ Y).obj F).map (homOfLE h).op s =
          ((TopCat.Sheaf.forget _ Y).obj F).map (homOfLE le_top).op t

/-- Compactly supported cohomology as a functor. -/
private noncomputable abbrev hcF (Y : TopCat.{0}) (q : ℤ) :
    TopCat.Sheaf (ModuleCat.{0} R) Y ⥤ ModuleCat.{0} R :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (compactSupportSectionsFunctor R (X := Y)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ q

private lemma exact_extF :
    PreservesFiniteLimits (extF R U) ∧ PreservesFiniteColimits (extF R U) := by
  have := (adjF R U).leftAdjoint_preservesColimits
  have := additive_extF R U
  have hc : PreservesFiniteColimits (extF R U) := inferInstance
  refine ⟨(Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr fun S hS => ?_, hc⟩
  have := hS.mono_f
  exact ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mp hc S hS).1,
    mono_map_extF R U S.f⟩

private lemma stalk_extF (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
    (x : (Opens.toTopCat X).obj U) :
    Nonempty (((extF R U).obj G).presheaf.stalk x.1 ≅ G.presheaf.stalk x) := by
  have := isIso_unit R U
  let e1 : G ≅ (resF R U).obj ((extF R U).obj G) := (asIso (adjF R U).unit).app G
  let P : AlgebraicGeometry.PresheafedSpace (ModuleCat.{0} R) := ⟨X, ((extF R U).obj G).presheaf⟩
  exact ⟨(P.restrictStalkIso U.isOpenEmbedding x).symm ≪≫
    (TopCat.Presheaf.stalkFunctor _ x).mapIso ((sheafToPresheaf _ _).mapIso e1).symm⟩

/-- A section `s` of `j_! G` over `W` vanishes on an open `P ≤ W` containing `W \ U`, and the
germs of `ρ s` vanish on `P`. -/
private lemma exists_open_res_eq_zero
    (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U)) {W : Opens X}
    (s : ((extF R U).obj G).obj.obj (op W)) :
    ∃ (P : Opens X) (hPW : P ≤ W), (∀ x ∈ W, x ∉ U → x ∈ P) ∧
      ∀ (y : (Opens.toTopCat X).obj U) (hy : y.1 ∈ P),
        G.presheaf.germ (pre W) y (hPW hy) (ρ R U G W s) = 0 := by
  let Pset : Set X := {x | ∃ (N : Opens X) (hN : N ≤ W), x ∈ N ∧
    ((extF R U).obj G).obj.map (homOfLE hN).op s = 0}
  have hPopen : IsOpen Pset := isOpen_iff_forall_mem_open.mpr fun x ⟨N, hN, hxN, hs⟩ =>
    ⟨N, fun y hy => ⟨N, hN, hy, hs⟩, N.2, hxN⟩
  refine ⟨⟨Pset, hPopen⟩, fun x ⟨N, hN, hxN, _⟩ => hN hxN, fun x hxW hxU => ?_, ?_⟩
  · obtain ⟨N, hxN, hN, hs⟩ := exists_nhds_res_eq_zero G s x hxW hxU
    exact ⟨N, hN, hxN, hs⟩
  · rintro y ⟨N, hN, hyN, hs⟩
    rw [germ_eq_of_res_eq' G (pre_mono hN) (ρ_res_eq_zero G hN hs) y hyN, map_zero]

private lemma exists_compact_separation [LocallyCompactSpace X] [T2Space X] {K : Set X}
    (hK : IsCompact K) {P W : Opens X} (hPW : P ≤ W) (hWP : ∀ x ∈ W, x ∉ U → x ∈ P)
    (hKW : K ⊆ W) :
    ∃ (L : Set X) (Q₁ Q₂ : Opens X), IsCompact L ∧ (∀ x ∈ L, x ∈ U) ∧ Q₁ ≤ W ∧
      (∀ x, x ∈ Q₁ → x ∈ Q₂ → x ∈ P) ∧ (∀ x ∈ K, x ∉ interior L → x ∈ P) ∧
      (∀ x ∈ K, x ∈ L → x ∈ Q₁) ∧ (∀ x ∈ L, x ∉ interior L → x ∈ Q₂) := by
  have hA : IsCompact (K \ (P : Set X)) := hK.diff P.2
  have hAUW : K \ (P : Set X) ⊆ ((U ⊓ W : Opens X) : Set X) := fun x ⟨hxK, hxP⟩ =>
    ⟨by_contra fun hxU => hxP (hWP x (hKW hxK) hxU), hKW hxK⟩
  obtain ⟨L, hL, hAL, hLUW⟩ := exists_compact_between hA (U ⊓ W).2 hAUW
  have hLU : ∀ x ∈ L, x ∈ U := fun x hx => (hLUW hx).1
  have hLW : ∀ x ∈ L, x ∈ W := fun x hx => (hLUW hx).2
  have hKP : ∀ x ∈ K, x ∉ interior L → x ∈ P := fun x hxK hxi =>
    by_contra fun hxP => hxi (hAL ⟨hxK, hxP⟩)
  let intL : Opens X := ⟨interior L, isOpen_interior⟩
  have hB : IsCompact ((L \ interior L) \ (P : Set X)) := (hL.diff isOpen_interior).diff P.2
  have hBK : Disjoint ((L \ interior L) \ (P : Set X)) K :=
    Set.disjoint_left.mpr fun x ⟨⟨_, hxi⟩, hxP⟩ hxK => hxP (hKP x hxK hxi)
  obtain ⟨O₁, O₂, hO₁, hO₂, hBO₁, hKO₂, hO⟩ := SeparatedNhds.of_isCompact_isCompact hB hK hBK
  let Q₁ : Opens X := (intL ⊓ ⟨O₂, hO₂⟩) ⊔ P
  let Q₂ : Opens X := P ⊔ ⟨O₁, hO₁⟩
  have hQ₁W : Q₁ ≤ W := sup_le (fun x hx => hLW x (interior_subset hx.1)) hPW
  have hQ₁₂ : ∀ x, x ∈ Q₁ → x ∈ Q₂ → x ∈ P := by
    rintro x (⟨_, hx2⟩ | hx) (hx' | hx1)
    · exact hx'
    · exact absurd hx2 (Set.disjoint_left.mp hO hx1)
    · exact hx
    · exact hx
  have hKLQ₁ : ∀ x ∈ K, x ∈ L → x ∈ Q₁ := fun x hxK _ => by
    by_cases hxi : x ∈ interior L
    · exact Opens.mem_sup.mpr (Or.inl (Opens.mem_inf.mpr ⟨hxi, hKO₂ hxK⟩))
    · exact Opens.mem_sup.mpr (Or.inr (hKP x hxK hxi))
  have hdLQ₂ : ∀ x ∈ L, x ∉ interior L → x ∈ Q₂ := fun x hxL hxi => by
    by_cases hxP : x ∈ P
    · exact Opens.mem_sup.mpr (Or.inl hxP)
    · exact Opens.mem_sup.mpr (Or.inr (hBO₁ ⟨⟨hxL, hxi⟩, hxP⟩))
  exact ⟨L, Q₁, Q₂, hL, hLU, hQ₁W, hQ₁₂, hKP, hKLQ₁, hdLQ₂⟩

private lemma isCSoft_extF [LocallyCompactSpace X] [T2Space X]
    (G : TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U)) (hG : CSoft G) :
    CSoft ((extF R U).obj G) := by
  intro K hK W hKW s
  obtain ⟨P, hPW, hWP, hρP⟩ := exists_open_res_eq_zero (R := R) (U := U) (G := G) (s := s)
  obtain ⟨L, Q₁, Q₂, hL, hLU, hQ₁W, hQ₁₂, hKP, hKLQ₁, hdLQ₂⟩ :=
    exists_compact_separation U hK hPW hWP hKW
  let intL : Opens X := ⟨interior L, isOpen_interior⟩
  let Lc : Opens X := ⟨Lᶜ, hL.isClosed.isOpen_compl⟩
  -- the section `σ` of `G`: `s` near `K ∩ L`, zero near `∂L`
  let σ₁ := G.obj.map (homOfLE (pre_mono (U := U) hQ₁W)).op (ρ R U G W s)
  obtain ⟨σ, hσ₁, hσ₂⟩ := glue2 G σ₁ (0 : G.obj.obj (op (pre (U := U) Q₂))) (by
    rw [map_zero]
    refine eq_zero_of_germ G _ fun y hy => ?_
    rw [germ_eq_of_res_eq' G inf_le_left rfl y hy |>.symm,
      germ_eq_of_res_eq' G (pre_mono hQ₁W) rfl y hy.1 |>.symm]
    exact hρP y (hQ₁₂ _ hy.1 hy.2))
  have gσ₁ : ∀ y (hy : y ∈ pre (U := U) Q₁),
      G.presheaf.germ _ y ((le_sup_left : pre (U := U) Q₁ ≤ pre Q₁ ⊔ pre Q₂) hy) σ =
      G.presheaf.germ (pre W) y (pre_mono hQ₁W hy) (ρ R U G W s) := fun y hy =>
    (germ_eq_of_res_eq' G (le_sup_left : pre (U := U) Q₁ ≤ pre Q₁ ⊔ pre Q₂) hσ₁ y hy).trans
      (germ_eq_of_res_eq' G (pre_mono hQ₁W) rfl y hy).symm
  have gσ₂ : ∀ y (hy : y ∈ pre (U := U) Q₂),
      G.presheaf.germ _ y ((le_sup_right : pre (U := U) Q₂ ≤ pre Q₁ ⊔ pre Q₂) hy) σ = 0 :=
    fun y hy => (germ_eq_of_res_eq' G (le_sup_right : pre (U := U) Q₂ ≤ pre Q₁ ⊔ pre Q₂) hσ₂
      y hy).trans (map_zero _)
  -- c-softness of `G` on the compact set `(K ∩ L) ∪ ∂L`
  let K'' : Set ((Opens.toTopCat X).obj U) := U.inclusion' ⁻¹' ((K ∩ L) ∪ (L \ interior L))
  have hK'' : IsCompact K'' := (U.isOpenEmbedding.isInducing.isCompact_preimage_iff
    (fun x hx => ⟨⟨x, hLU x (hx.elim (fun h => h.2) (fun h => h.1))⟩, rfl⟩)).mpr
    ((hK.inter_right hL.isClosed).union (hL.diff isOpen_interior))
  have hK''Q : K'' ⊆ ((pre (U := U) Q₁ ⊔ pre Q₂ : Opens _) : Set _) := by
    rintro y (⟨hyK, hyL⟩ | ⟨hyL, hyi⟩)
    · exact Opens.mem_sup.mpr (Or.inl (hKLQ₁ _ hyK hyL))
    · exact Opens.mem_sup.mpr (Or.inr (hdLQ₂ _ hyL hyi))
  obtain ⟨t₀, Z, hZ, hK''Z, hσt₀⟩ := hG K'' hK'' _ hK''Q σ
  have gt₀ : ∀ y (hy : y ∈ Z), G.presheaf.germ ⊤ y trivial t₀ =
      G.presheaf.germ _ y (hZ hy) σ := fun y hy =>
    (G.presheaf.germ_ext _ hy (homOfLE hZ) (homOfLE le_top) hσt₀).symm
  -- cut off `t₀` outside `L`
  let Y₂ : Opens ((Opens.toTopCat X).obj U) := (Z ⊓ pre Q₂) ⊔ pre Lc
  obtain ⟨t₁, ht₁₁, ht₁₂⟩ := glue2 G (G.obj.map (homOfLE (le_top : pre (U := U) intL ≤ ⊤)).op t₀)
    (0 : G.obj.obj (op Y₂)) (by
      rw [map_zero]
      refine eq_zero_of_germ G _ fun y hy => ?_
      obtain ⟨hyi, hy2⟩ := Opens.mem_inf.mp hy
      have hyZ : y ∈ Z ⊓ pre Q₂ :=
        (Opens.mem_sup.mp hy2).resolve_right fun h => h (interior_subset hyi)
      exact (germ_eq_of_res_eq' G inf_le_left rfl y hy).symm.trans
        ((germ_eq_of_res_eq' G le_top rfl y hyi).symm.trans
          ((gt₀ y (Opens.mem_inf.mp hyZ).1).trans (gσ₂ y (Opens.mem_inf.mp hyZ).2))))
  have hcov : (⊤ : Opens ((Opens.toTopCat X).obj U)) ≤ pre (U := U) intL ⊔ Y₂ := by
    intro y _
    by_cases hyL : y.1 ∈ L
    · by_cases hyi : y.1 ∈ interior L
      · exact Opens.mem_sup.mpr (Or.inl hyi)
      · exact Opens.mem_sup.mpr (Or.inr (Opens.mem_sup.mpr (Or.inl (Opens.mem_inf.mpr
          ⟨hK''Z (Or.inr ⟨hyL, hyi⟩), hdLQ₂ _ hyL hyi⟩))))
    · exact Opens.mem_sup.mpr (Or.inr (Opens.mem_sup.mpr (Or.inr hyL)))
  let t := G.obj.map (homOfLE hcov).op t₁
  have gt₁ : ∀ y (hy : y ∈ pre (U := U) intL), G.presheaf.germ ⊤ y trivial t =
      G.presheaf.germ ⊤ y trivial t₀ := fun y hy =>
    (germ_eq_of_res_eq' G hcov rfl y trivial).symm.trans
      ((germ_eq_of_res_eq' G le_sup_left ht₁₁ y hy).trans
        (germ_eq_of_res_eq' G le_top rfl y hy).symm)
  have gt₂ : ∀ y (hy : y ∈ Y₂), G.presheaf.germ ⊤ y trivial t = 0 := fun y hy =>
    (germ_eq_of_res_eq' G hcov rfl y trivial).symm.trans
      ((germ_eq_of_res_eq' G le_sup_right ht₁₂ y hy).trans (map_zero _))
  -- extend by zero
  have hULc : (⊤ : Opens X) ≤ U ⊔ Lc := fun x _ => by
    by_cases hx : x ∈ L
    · exact Opens.mem_sup.mpr (Or.inl (hLU x hx))
    · exact Opens.mem_sup.mpr (Or.inr hx)
  obtain ⟨T, hT⟩ := exists_ρ_eq G hULc t (eq_zero_of_germ G _ fun y hy =>
    (germ_eq_of_res_eq' G le_top rfl y hy).symm.trans
      (gt₂ y (Opens.mem_sup.mpr (Or.inr (Opens.mem_inf.mp hy).2))))
  -- the neighbourhood of `K` on which `T` and `s` agree
  let Z' : Opens X := U.isOpenEmbedding.functor.obj Z
  let W' : Opens X := ((Z' ⊓ Q₁ ⊓ intL) ⊔ (Z' ⊓ Q₂ ⊓ P)) ⊔ (P ⊓ Lc)
  have hW'W : W' ≤ W := sup_le (sup_le (fun x hx => hQ₁W hx.1.2) (fun x hx => hPW hx.2))
    (fun x hx => hPW hx.1)
  have hmemZ' : ∀ x ∈ K'', U.inclusion' x ∈ Z' := fun x hx => ⟨x, hK''Z hx, rfl⟩
  have hKW' : K ⊆ W' := by
    intro x hxK
    by_cases hxL : x ∈ L
    · by_cases hxi : x ∈ interior L
      · exact Opens.mem_sup.mpr (Or.inl (Opens.mem_sup.mpr (Or.inl (Opens.mem_inf.mpr
          ⟨Opens.mem_inf.mpr ⟨hmemZ' ⟨x, hLU x hxL⟩ (Or.inl ⟨hxK, hxL⟩), hKLQ₁ x hxK hxL⟩, hxi⟩))))
      · exact Opens.mem_sup.mpr (Or.inl (Opens.mem_sup.mpr (Or.inr (Opens.mem_inf.mpr
          ⟨Opens.mem_inf.mpr ⟨hmemZ' ⟨x, hLU x hxL⟩ (Or.inr ⟨hxL, hxi⟩), hdLQ₂ x hxL hxi⟩,
            hKP x hxK hxi⟩))))
    · exact Opens.mem_sup.mpr (Or.inr (Opens.mem_inf.mpr
        ⟨hKP x hxK fun h => hxL (interior_subset h), hxL⟩))
  refine ⟨T, W', hW'W, hKW', ?_⟩
  apply ρ_injective G W'
  refine (ρ_res G hW'W s).trans (Eq.trans ?_ ((ρ_res G le_top T).trans (congrArg _ hT)).symm)
  refine res_eq_res_of_germ G _ _ _ _ fun y hy => ?_
  have hZ'Z : ∀ {y : (Opens.toTopCat X).obj U}, y.1 ∈ Z' → y ∈ Z := by
    rintro y ⟨z, hz, e⟩
    obtain rfl := U.isOpenEmbedding.injective e
    exact hz
  rcases Opens.mem_sup.mp hy with hy | ⟨hyP, hyL⟩
  · rcases Opens.mem_sup.mp hy with ⟨⟨hyZ, hyQ⟩, hyi⟩ | ⟨⟨hyZ, hyQ⟩, hyP⟩
    · exact (gσ₁ y hyQ).symm.trans ((gt₀ y (hZ'Z hyZ)).symm.trans (gt₁ y hyi).symm)
    · exact (hρP y hyP).trans
        (gt₂ y (Opens.mem_sup.mpr (Or.inl (Opens.mem_inf.mpr ⟨hZ'Z hyZ, hyQ⟩)))).symm
  · exact (hρP y hyP).trans (gt₂ y (Opens.mem_sup.mpr (Or.inr hyL))).symm

private lemma exists_gamma [T2Space X] :
    ∃ γ : extF R U ⋙ compactSupportSectionsFunctor R ≅ compactSupportSectionsFunctor R,
      ∀ G (s : compactSupportSections R G),
        ((TopCat.Sheaf.forget _ X).obj ((extF R U).obj G)).map
            (homOfLE (le_top : U.isOpenEmbedding.functor.obj ⊤ ≤ ⊤)).op
            ((γ.inv.app G) s).1 =
          ((TopCat.Sheaf.forget _ _).map ((adjF R U).unit.app G)).app (op ⊤) s.1 := by
  refine ⟨gammaIso R U, fun G s => ?_⟩
  have h : ρ R U G ⊤ ((gammaIso R U).inv.app G s).1 = s.1 :=
    congrArg Subtype.val ((LinearEquiv.ofBijective (gammaHom R U G)
      (gammaHom_bijective G)).apply_symm_apply s)
  exact (unitApp_ρ G ⊤ _).symm.trans (congrArg (unitApp R U G ⊤).hom h)

private lemma mono_counit (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    Mono ((adjF R U).counit.app F) :=
  mono_of_injective _ (counit_injective R U F)

private lemma exists_m (F : TopCat.Sheaf (ModuleCat.{0} R) X) {V U : Opens X} (h : V ≤ U) :
    ∃ m : (extF R V).obj ((resF R V).obj F) ⟶ (extF R U).obj ((resF R U).obj F),
      m ≫ (adjF R U).counit.app F = (adjF R V).counit.app F := by
  have : IsIso ((resF R V).map ((adjF R U).counit.app F)) := by
    have : IsIso ((sheafToPresheaf _ _).map ((resF R V).map ((adjF R U).counit.app F))) := by
      have hV : ∀ V' : (Opens ((Opens.toTopCat X).obj V))ᵒᵖ,
          IsIso (((sheafToPresheaf _ _).map ((resF R V).map ((adjF R U).counit.app F))).app V') :=
        fun V' => (ConcreteCategory.isIso_iff_bijective _).mpr
          ⟨counit_injective R U F _, counit_surjective R U F ((functor_le V'.unop).trans h)⟩
      exact NatIso.isIso_of_isIso_app _
    exact isIso_of_fully_faithful (sheafToPresheaf _ _) _
  refine ⟨((adjF R V).homEquiv _ _).symm (inv ((resF R V).map ((adjF R U).counit.app F))), ?_⟩
  rw [← Adjunction.homEquiv_naturality_right_symm, IsIso.inv_hom_id, Adjunction.homEquiv_counit,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-! ### Comparison of compactly supported cohomology -/

section Derived

private lemma preservesFiniteLimits_extF : PreservesFiniteLimits (extF R U) := (exact_extF R U).1

private lemma preservesFiniteColimits_extF : PreservesFiniteColimits (extF R U) :=
  (exact_extF R U).2

attribute [local instance] additive_extF preservesFiniteLimits_extF preservesFiniteColimits_extF

variable {R U} in
private lemma quasiIso_mapHomotopyCategory_extF
    {K L : HomotopyCategory (TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U))
      (ComplexShape.up ℤ)}
    (φ : K ⟶ L) (h : HomotopyCategory.quasiIso _ _ φ) :
    HomotopyCategory.quasiIso _ _ (((extF R U).mapHomotopyCategory _).map φ) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff
    (((extF R U).mapHomologicalComplex _).map g)).mpr
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)

/-- `j_!` on bounded below derived categories. -/
private noncomputable def extD :
    DerivedCategory.Plus (TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U)) ⥤
      DerivedCategory.Plus (TopCat.Sheaf (ModuleCat.{0} R) X) :=
  Localization.lift (W := HomotopyCategory.Plus.quasiIso _)
    ((extF R U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    (fun _ _ f hf => Localization.inverts DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso _) _ (quasiIso_mapHomotopyCategory_extF f.hom hf))
    DerivedCategory.Plus.Qh

private noncomputable def extDFac :
    DerivedCategory.Plus.Qh ⋙ extD R U ≅
      (extF R U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
  Localization.fac _ _ _

/-- The single functor to `D^+` factors through the bounded below homotopy category. -/
private noncomputable def singleIsoQh (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] :
    DerivedCategory.Plus.singleFunctor C 0 ≅
      HomotopyCategory.Plus.singleFunctor C 0 ⋙ DerivedCategory.Plus.Qh :=
  ((Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight C).preimageIso
    (DerivedCategory.singleFunctorIsoCompQh C 0)

private noncomputable def singleCompExtK :
    HomotopyCategory.Plus.singleFunctor _ 0 ⋙ (extF R U).mapHomotopyCategoryPlus ≅
      extF R U ⋙ HomotopyCategory.Plus.singleFunctor _ 0 :=
  ((HomotopyCategory.Plus.fullyFaithfulι _).whiskeringRight _).preimageIso
    (by
      refine (?_ : HomotopyCategory.singleFunctor _ 0 ⋙
        (extF R U).mapHomotopyCategory (ComplexShape.up ℤ) ≅
          extF R U ⋙ HomotopyCategory.singleFunctor _ 0)
      exact Functor.isoWhiskerRight (HomotopyCategory.singleFunctorPostcompQuotientIso _ 0) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((extF R U).mapHomotopyCategoryFactors _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex (extF R U)
        (ComplexShape.up ℤ) 0) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (HomotopyCategory.singleFunctorPostcompQuotientIso _ 0).symm)

private noncomputable def singleCompExtD :
    DerivedCategory.Plus.singleFunctor _ 0 ⋙ extD R U ≅
      extF R U ⋙ DerivedCategory.Plus.singleFunctor _ 0 :=
  Functor.isoWhiskerRight (singleIsoQh _) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (extDFac R U) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (singleCompExtK R U) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (singleIsoQh _).symm

private lemma exists_ι [LocallyCompactSpace X] [T2Space X] (q : ℤ) :
    Nonempty (hcF R ((Opens.toTopCat X).obj U) q ≅ extF R U ⋙ hcF R X q) := by
  have : LocallyCompactSpace ((Opens.toTopCat X).obj U) := U.isOpen.locallyCompactSpace
  have : T2Space ((Opens.toTopCat X).obj U) := inferInstanceAs (T2Space (U : Set X))
  let ΓU := compactSupportSectionsFunctor R (X := (Opens.toTopCat X).obj U)
  let ΓX := compactSupportSectionsFunctor R (X := X)
  let EK := (extF R U).mapHomotopyCategoryPlus
  let αU := ΓU.rightDerivedFunctorPlusUnith
  let αX := ΓX.rightDerivedFunctorPlusUnith
  let β : ΓU.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (extD R U ⋙ ΓX.rightDerivedFunctorPlus) :=
    (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryPlusCompIso (gammaIso R U)).symm
        DerivedCategory.Plus.Qh).hom ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft EK αX ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (extDFac R U).inv _ ≫
      (Functor.associator _ _ _).hom
  let τ := ΓU.rightDerivedFunctorPlus.rightDerivedDesc αU (HomotopyCategory.Plus.quasiIso _) _ β
  have hβ : ∀ Y : HomotopyCategory.Plus (InjectiveObject (TopCat.Sheaf (ModuleCat.{0} R)
      ((Opens.toTopCat X).obj U))),
      IsIso (β.app ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Y)) := by
    intro Y
    let K := (InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Y
    have hinj := (compactSupportCohomology_of_isCSoft R ((Opens.toTopCat X).obj U)).1.2
    have hc2 := (compactSupportCohomology_of_isCSoft R X).2.2.2.1
    have : IsIso (αX.app (EK.obj K)) := by
      refine hc2 ⟨(EK.obj K).obj.as, (HomotopyCategory.plus_quotient_obj_iff _).mp
        (EK.obj K).property⟩ fun n K' hK' W hKW s' => ?_
      have hG : CSoft (K.obj.as.X n) := fun K₀ hK₀ W₀ hW₀ s₀ => by
        obtain ⟨t, V, hKV, hVW, e⟩ := hinj (K.obj.as.X n) inferInstance K₀ hK₀ W₀ hW₀ s₀
        exact ⟨t, V, hVW, hKV, e.symm⟩
      obtain ⟨t, V, hVW, hKV, e⟩ := isCSoft_extF R U _ hG K' hK' W hKW s'
      exact ⟨t, V, hKV, hVW, e.symm⟩
    simp only [β, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  have hτ : IsIso τ := by
    have : ∀ D, IsIso (τ.app D) := by
      intro D
      let Φ := (InjectiveObject.ι (TopCat.Sheaf (ModuleCat.{0} R)
        ((Opens.toTopCat X).obj U))).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
      rw [← NatTrans.isIso_app_iff_of_iso τ (Φ.objObjPreimageIso D)]
      have hfac := Functor.rightDerived_fac_app ΓU.rightDerivedFunctorPlus αU
        (HomotopyCategory.Plus.quasiIso _) _ β
        ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj (Φ.objPreimage D))
      have h2 : IsIso (αU.app ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj
          (Φ.objPreimage D)) ≫ τ.app (Φ.obj (Φ.objPreimage D))) := by
        rw [show αU.app ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj (Φ.objPreimage D)) ≫
          τ.app (Φ.obj (Φ.objPreimage D)) = _ from hfac]
        exact hβ _
      exact IsIso.of_isIso_comp_left (αU.app _) (τ.app (Φ.obj (Φ.objPreimage D)))
    exact NatIso.isIso_of_isIso_app _
  exact ⟨Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (asIso τ) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (singleCompExtD R U) _ ≪≫ Functor.associator _ _ _⟩

end Derived

private lemma exists_ι_e [LocallyCompactSpace X] [T2Space X] :
    ∃ (ι : ∀ (U : Opens X) (q : ℤ), hcF R ((Opens.toTopCat X).obj U) q ≅ extF R U ⋙ hcF R X q)
      (e : ∀ (q : ℤ) {V U : Opens X}, V ≤ U →
        (resF R V ⋙ hcF R ((Opens.toTopCat X).obj V) q ⟶
          resF R U ⋙ hcF R ((Opens.toTopCat X).obj U) q)),
      (∀ (q : ℤ) (U : Opens X), e q (le_refl U) = 𝟙 _) ∧
      (∀ (q : ℤ) (V W U : Opens X) (h₁ : V ≤ W) (h₂ : W ≤ U),
        e q h₁ ≫ e q h₂ = e q (h₁.trans h₂)) ∧
      (∀ (q : ℤ) (V U : Opens X) (h : V ≤ U) (F : TopCat.Sheaf (ModuleCat.{0} R) X)
        (m : (extF R V).obj ((resF R V).obj F) ⟶ (extF R U).obj ((resF R U).obj F)),
        m ≫ (adjF R U).counit.app F = (adjF R V).counit.app F →
          (e q h).app F = (ι V q).hom.app _ ≫ (hcF R X q).map m ≫ (ι U q).inv.app _) := by
  let ιc := fun (U : Opens X) (q : ℤ) => (exists_ι R U q).some
  choose m hm using fun (F : TopCat.Sheaf (ModuleCat.{0} R) X) (V U : Opens X) (h : V ≤ U) =>
    exists_m R F h
  have uniq : ∀ F V U (h : V ≤ U)
      (m' : (extF R V).obj ((resF R V).obj F) ⟶ (extF R U).obj ((resF R U).obj F)),
      m' ≫ (adjF R U).counit.app F = (adjF R V).counit.app F → m' = m F V U h := by
    intro F V U h m' hm'
    have := mono_counit R U F
    exact (cancel_mono _).mp (hm'.trans (hm F V U h).symm)
  have mnat : ∀ {F F' : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ F') (V U : Opens X)
      (h : V ≤ U), (extF R V).map ((resF R V).map φ) ≫ m F' V U h =
        m F V U h ≫ (extF R U).map ((resF R U).map φ) := by
    intro F F' φ V U h
    have := mono_counit R U F'
    refine (cancel_mono ((adjF R U).counit.app F')).mp ?_
    have n1 : (extF R V).map ((resF R V).map φ) ≫ (adjF R V).counit.app F' =
        (adjF R V).counit.app F ≫ φ := (adjF R V).counit.naturality φ
    have n2 : (extF R U).map ((resF R U).map φ) ≫ (adjF R U).counit.app F' =
        (adjF R U).counit.app F ≫ φ := (adjF R U).counit.naturality φ
    rw [Category.assoc, hm, n1, Category.assoc, n2, ← Category.assoc, hm]
  refine ⟨ιc, fun q V U h =>
    { app := fun F => (ιc V q).hom.app ((resF R V).obj F) ≫ (hcF R X q).map (m F V U h) ≫
        (ιc U q).inv.app ((resF R U).obj F)
      naturality := ?_ }, ?_, ?_, ?_⟩
  · intro F F' φ
    have h1 : (hcF R ((Opens.toTopCat X).obj V) q).map ((resF R V).map φ) ≫
        (ιc V q).hom.app ((resF R V).obj F') =
        (ιc V q).hom.app ((resF R V).obj F) ≫
          (hcF R X q).map ((extF R V).map ((resF R V).map φ)) :=
      (ιc V q).hom.naturality ((resF R V).map φ)
    have h2 : (hcF R X q).map ((extF R U).map ((resF R U).map φ)) ≫
        (ιc U q).inv.app ((resF R U).obj F') =
        (ιc U q).inv.app ((resF R U).obj F) ≫
          (hcF R ((Opens.toTopCat X).obj U) q).map ((resF R U).map φ) :=
      (ιc U q).inv.naturality ((resF R U).map φ)
    change (hcF R ((Opens.toTopCat X).obj V) q).map ((resF R V).map φ) ≫ _ =
      _ ≫ (hcF R ((Opens.toTopCat X).obj U) q).map ((resF R U).map φ)
    rw [← Category.assoc, h1, Category.assoc, ← Category.assoc ((hcF R X q).map _),
      ← CategoryTheory.Functor.map_comp, mnat, CategoryTheory.Functor.map_comp, Category.assoc, h2]
    simp only [Category.assoc]
  · intro q U
    refine NatTrans.ext (funext fun F => ?_)
    have : m F U U le_rfl = 𝟙 _ := (uniq F U U le_rfl (𝟙 _) (Category.id_comp _)).symm
    simp [this]
  · intro q V W U h₁ h₂
    refine NatTrans.ext (funext fun F => ?_)
    have : m F V U (h₁.trans h₂) = m F V W h₁ ≫ m F W U h₂ :=
      (uniq F V U _ _ (by rw [Category.assoc, hm, hm])).symm
    simp only [NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [this, CategoryTheory.Functor.map_comp, Category.assoc]
  · intro q V U h F m' hm'
    rw [uniq F V U h m' hm']

end ExtendByZero

open ExtendByZero in
/-- Let `X` be locally compact Hausdorff and `U ⊆ X` open, with restriction `res U = j^*` and
extension by zero `ext U = j_!`, `adj U : j_! ⊣ j^*`. Then for every `U`: `j_!` is exact; the unit
`G ⟶ j^* j_! G` is invertible; `(j_! G)_x ≅ G_x` for `x ∈ U` and `(j_! G)_x = 0` for `x ∉ U`; `j_!`
preserves c-soft sheaves; and `Γ_c(X, j_! G) ≅ Γ_c(U, G)` naturally, by restriction to `U`. For
opens `V ≤ U` and a sheaf `F` on `X` there is a unique morphism `j_{V!}(F|_V) ⟶ j_{U!}(F|_U)`
over `F`. Finally there are natural isomorphisms `ι U q : H^q_c(U, -) ≅ H^q_c(X, j_{U!} -)` and
extension maps `e q : H^q_c(V, F|_V) ⟶ H^q_c(U, F|_U)` natural in `F`, functorial in `V ≤ U`,
and induced through `ι` by that morphism. Here `Hc Y q` is the functor whose value on `F` is
`MMP.Fourfold.compactSupportCohomology R q F`. -/
@[mmp "lem_mmp_compact_support_open_extension"]
public theorem compactSupportCohomology_extendByZero
    (R : Type) [CommRing R] (X : TopCat.{0}) [LocallyCompactSpace X] [T2Space X] :
    let res : ∀ U : Opens X, TopCat.Sheaf (ModuleCat.{0} R) X ⥤
        TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U) := fun U =>
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafPushforwardContinuous _ _ _
    let ext : ∀ U : Opens X, TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U) ⥤
        TopCat.Sheaf (ModuleCat.{0} R) X := fun U =>
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafPullback _ _ _
    let adj : ∀ U : Opens X, ext U ⊣ res U := fun U =>
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafAdjunctionContinuous _ _ _
    let Hc : ∀ (Y : TopCat.{0}) (_ : ℤ), TopCat.Sheaf (ModuleCat.{0} R) Y ⥤ ModuleCat.{0} R :=
      fun Y q => DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (compactSupportSectionsFunctor R (X := Y)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q
    let IsCSoft : ∀ {Y : TopCat.{0}}, TopCat.Sheaf (ModuleCat.{0} R) Y → Prop := fun {Y} F =>
      ∀ K : Set Y, IsCompact K → ∀ W : Opens Y, K ⊆ W →
        ∀ s : ((TopCat.Sheaf.forget _ Y).obj F).obj (op W),
          ∃ t : ((TopCat.Sheaf.forget _ Y).obj F).obj (op ⊤), ∃ (W' : Opens Y) (h : W' ≤ W),
            K ⊆ W' ∧ ((TopCat.Sheaf.forget _ Y).obj F).map (homOfLE h).op s =
              ((TopCat.Sheaf.forget _ Y).obj F).map (homOfLE le_top).op t
    (∀ U : Opens X,
      (PreservesFiniteLimits (ext U) ∧ PreservesFiniteColimits (ext U)) ∧
      (∀ G, IsIso ((adj U).unit.app G)) ∧
      (∀ G (x : (Opens.toTopCat X).obj U),
        Nonempty (((ext U).obj G).presheaf.stalk x.1 ≅ G.presheaf.stalk x)) ∧
      (∀ G, ∀ x ∉ U, IsZero (((ext U).obj G).presheaf.stalk x)) ∧
      (∀ G, IsCSoft G → IsCSoft ((ext U).obj G)) ∧
      (∃ γ : ext U ⋙ compactSupportSectionsFunctor R ≅ compactSupportSectionsFunctor R,
        ∀ G (s : compactSupportSections R G),
          ((TopCat.Sheaf.forget _ X).obj ((ext U).obj G)).map
              (homOfLE (le_top : U.isOpenEmbedding.functor.obj ⊤ ≤ ⊤)).op
              ((γ.inv.app G) s).1 =
            ((TopCat.Sheaf.forget _ _).map ((adj U).unit.app G)).app (op ⊤) s.1)) ∧
    (∀ (F : TopCat.Sheaf (ModuleCat.{0} R) X) (V U : Opens X), V ≤ U →
      ∃! m : (ext V).obj ((res V).obj F) ⟶ (ext U).obj ((res U).obj F),
        m ≫ (adj U).counit.app F = (adj V).counit.app F) ∧
    ∃ (ι : ∀ (U : Opens X) (q : ℤ), Hc ((Opens.toTopCat X).obj U) q ≅ ext U ⋙ Hc X q)
      (e : ∀ (q : ℤ) {V U : Opens X}, V ≤ U →
        (res V ⋙ Hc ((Opens.toTopCat X).obj V) q ⟶ res U ⋙ Hc ((Opens.toTopCat X).obj U) q)),
      (∀ (q : ℤ) (U : Opens X), e q (le_refl U) = 𝟙 _) ∧
      (∀ (q : ℤ) (V W U : Opens X) (h₁ : V ≤ W) (h₂ : W ≤ U),
        e q h₁ ≫ e q h₂ = e q (h₁.trans h₂)) ∧
      (∀ (q : ℤ) (V U : Opens X) (h : V ≤ U) (F : TopCat.Sheaf (ModuleCat.{0} R) X)
        (m : (ext V).obj ((res V).obj F) ⟶ (ext U).obj ((res U).obj F)),
        m ≫ (adj U).counit.app F = (adj V).counit.app F →
          (e q h).app F = (ι V q).hom.app _ ≫ (Hc X q).map m ≫ (ι U q).inv.app _) := by
  intro res ext adj Hc IsCSoft
  refine ⟨fun U => ⟨exact_extF R U, fun G => ?_, stalk_extF R U, isZero_stalk_extF R U,
    isCSoft_extF R U, exists_gamma R U⟩, ?_, ?_⟩
  · have := isIso_unit R U
    exact NatIso.isIso_app_of_isIso _ _
  · intro F V U h
    obtain ⟨m, hm⟩ := exists_m R F h
    have := mono_counit R U F
    exact ⟨m, hm, fun m' hm' => (cancel_mono ((adj U).counit.app F)).mp
      (hm'.trans hm.symm)⟩
  · exact exists_ι_e R

end MMP.Fourfold

end
