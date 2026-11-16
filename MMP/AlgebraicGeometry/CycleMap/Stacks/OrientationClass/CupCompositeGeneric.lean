module

public import MMP.AlgebraicTopology.ThomClass.DirectSum
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ChainBaseChangeGeneric

/-!
# Points of fibre products, pairs of bundle points, and the cup product chase

Bundle-free lemmas of the proof of Fulton's Lemma 19.2 (b) (the orientation class of a
composite).

## Main definitions

* `MMP.pairPoint`: the point `(q, q')` of `inclLeft^* Q ×ᵇ inclRight^* Q'` over `V ∩ V'`.

## Main results

* `MMP.range_map_comp_eq_inter_of_isPullback`: `X'(ℂ) = X(ℂ) ∩ Y'(ℂ)` in `Y(ℂ)`.
* `MMP.cohomologyWithSupports.map_cup_eq_map_cup_of_comp`: the cohomological
  chase: if `ι^* u_k = σ_k^* a_k`, then `ι^* (u₁ ∪ u₂) = σ^* (pr₁^* a₁ ∪ pr₂^* a₂)` for
  `σ_k = pr_k ∘ σ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, Lemma 19.2 (b).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology

namespace MMP

open UnderlyingSpace

section Points

variable {X Y X' Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [X'.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))]
  {i : X ⟶ Y} {i' : X' ⟶ Y'} {f : Y' ⟶ Y} {f' : X' ⟶ X} [i.IsOver (Spec (.of ℂ))]
  [i'.IsOver (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [f'.IsOver (Spec (.of ℂ))]

/-- **The points of a fibre product inside the base.** In a fibre square `X' = X ×_Y Y'` of
schemes over `ℂ`, the image of `X'(ℂ)` in `Y(ℂ)` is the intersection of the images of `X(ℂ)` and
`Y'(ℂ)`. -/
theorem range_map_comp_eq_inter_of_isPullback (sq : IsPullback i' f' f i) :
    range (UnderlyingSpace.map (K := ℂ) (f' ≫ i)) =
      range (UnderlyingSpace.map (K := ℂ) i) ∩ range (UnderlyingSpace.map (K := ℂ) f) := by
  ext y
  constructor
  · rintro ⟨x', rfl⟩
    refine ⟨⟨mapFun f' x', UnderlyingSpace.ext ?_⟩, ⟨mapFun i' x', UnderlyingSpace.ext ?_⟩⟩
    · change (x'.toHom ≫ f') ≫ i = x'.toHom ≫ f' ≫ i
      rw [Category.assoc]
    · change (x'.toHom ≫ i') ≫ f = x'.toHom ≫ f' ≫ i
      rw [Category.assoc, sq.w]
  · rintro ⟨hy, ⟨b, rfl⟩⟩
    obtain ⟨c, rfl⟩ := (range_map_eq_preimage_of_isPullback sq).ge hy
    refine ⟨c, UnderlyingSpace.ext ?_⟩
    change c.toHom ≫ f' ≫ i = (c.toHom ≫ i') ≫ f
    rw [Category.assoc, sq.w]

end Points

section PairPoint

open Bundle

variable {Yt : Type} [TopologicalSpace Yt] {V V' : Set Yt}
  {F : Type} {Q : V → Type} [∀ x, TopologicalSpace (Q x)] [TopologicalSpace (TotalSpace F Q)]
  {F' : Type} {Q' : V' → Type} [∀ x, TopologicalSpace (Q' x)]
  [TopologicalSpace (TotalSpace F' Q')]

variable (V V') in
/-- The inclusion `V ∩ V' ⊆ V`. -/
abbrev inclLeft : C(↥(V ∩ V'), V) := ContinuousMap.inclusion inter_subset_left

variable (V V') in
/-- The inclusion `V ∩ V' ⊆ V'`. -/
abbrev inclRight : C(↥(V ∩ V'), V') := ContinuousMap.inclusion inter_subset_right

variable (F Q F' Q') in
/-- The point `(q, q')` of `Q ⊕ Q'` over `b ∈ V ∩ V'`, for `q ∈ Q_b`, `q' ∈ Q'_b`. -/
def pairPoint (b : ↥(V ∩ V')) (q : TotalSpace F Q) (hq : q.proj = inclLeft V V' b)
    (q' : TotalSpace F' Q') (hq' : q'.proj = inclRight V V' b) :
    TotalSpace (F × F') ((inclLeft V V' *ᵖ Q) ×ᵇ (inclRight V V' *ᵖ Q')) :=
  ⟨b, ((pullbackMk (inclLeft V V') b q hq).2, (pullbackMk (inclRight V V') b q' hq').2)⟩

/-- The point `pairPoint F Q F' Q' b q hq q' hq'` lies over `b`. -/
@[simp]
lemma proj_pairPoint (b : ↥(V ∩ V')) (q : TotalSpace F Q) (hq) (q' : TotalSpace F' Q') (hq') :
    (pairPoint F Q F' Q' b q hq q' hq').proj = b :=
  rfl

/-- If `b`, `q` and `q'` are continuous, then so is
`z ↦ pairPoint F Q F' Q' (b z) (q z) _ (q' z) _` into `Q ⊕ Q'`. -/
lemma continuous_pairPoint [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F']
    [NormedSpace ℂ F'] {Z : Type*} [TopologicalSpace Z] {b : Z → ↥(V ∩ V')}
    {q : Z → TotalSpace F Q} {q' : Z → TotalSpace F' Q'}
    (hq : ∀ z, (q z).proj = inclLeft V V' (b z)) (hq' : ∀ z, (q' z).proj = inclRight V V' (b z))
    (hb : Continuous b) (hqc : Continuous q) (hqc' : Continuous q') :
    Continuous fun z ↦ pairPoint F Q F' Q' (b z) (q z) (hq z) (q' z) (hq' z) := by
  refine (FiberBundle.Prod.isInducing_diag F (inclLeft V V' *ᵖ Q) F'
    (inclRight V V' *ᵖ Q')).continuous_iff.2 (Continuous.prodMk ?_ ?_)
  · change Continuous[_, pullbackTopology F Q (inclLeft V V')]
      fun z ↦ pullbackMk (inclLeft V V') (b z) (q z) (hq z)
    rw [pullbackTopology_def]
    refine continuous_inf_rng.2
      ⟨continuous_induced_rng.2 (by exact hb), continuous_induced_rng.2 ?_⟩
    have : (Pullback.lift (inclLeft V V') ∘ fun z ↦ pullbackMk (inclLeft V V') (b z) (q z) (hq z))
        = q := funext fun z ↦ lift_pullbackMk _ _ _ _
    rwa [this]
  · change Continuous[_, pullbackTopology F' Q' (inclRight V V')]
      fun z ↦ pullbackMk (inclRight V V') (b z) (q' z) (hq' z)
    rw [pullbackTopology_def]
    refine continuous_inf_rng.2
      ⟨continuous_induced_rng.2 (by exact hb), continuous_induced_rng.2 ?_⟩
    have : (Pullback.lift (inclRight V V') ∘
        fun z ↦ pullbackMk (inclRight V V') (b z) (q' z) (hq' z)) = q' :=
      funext fun z ↦ lift_pullbackMk _ _ _ _
    rwa [this]

end PairPoint

namespace cohomologyWithSupports

variable {R : Type} [CommRing R]

/-- `eqToHom` along an equality of degrees is `congrIndex`. -/
lemma eqToHom_hom_eq_congrIndex {Y : TopCat.{0}} {S : Set Y} {k k' : ℤ} (hk : k = k')
    (h : relativeSingularCohomology R (ModuleCat.of R R) Y S k =
      relativeSingularCohomology R (ModuleCat.of R R) Y S k')
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y S k) :
    (eqToHom h).hom x = congrIndex R Y rfl hk x := by
  subst hk
  rfl

/-- The cup product commutes with the transport of degrees. -/
lemma cup_congrIndex {Y : TopCat.{0}} {X W : Set Y} (hX : IsClosed X) (hW : IsClosed W)
    {i i' j j' : ℤ} (hi : i = i') (hj : j = j')
    (a : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (b : cohomologyWithSupports R (ModuleCat.of R R) Y W j) :
    cup R Y hX hW i' j' (congrIndex R Y rfl hi a) (congrIndex R Y rfl hj b) =
      congrIndex R Y rfl (by rw [hi, hj]) (cup R Y hX hW i j a b) := by
  subst hi hj
  rfl

/-- Composition of the maps of pairs, applied to a class. -/
lemma map_hom_map_hom {Y'' Y' Y : TopCat.{0}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y) {A'' : Set Y''}
    {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A) {k : Y'' ⟶ Y}
    (hk : A'' ⊆ k ⁻¹' A) (e : g ≫ f = k) (j : ℤ)
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y A j) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) g hg j).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) f hf j).hom x) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) k hk j).hom x := by
  subst e
  rw [relativeSingularCohomology.map_comp R _ g f hg hf]
  rfl

/-- `g^*` after `forget` after `f^*` is `(f ∘ g)^*`. -/
lemma map_hom_forget_hom_pullback_hom {Y'' Y' Y : TopCat.{0}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y)
    {X : Set Y} {X' : Set Y'} (h : f ⁻¹' X ⊆ X') {A'' : Set Y''} (hg : A'' ⊆ g ⁻¹' X'ᶜ)
    (hk : A'' ⊆ (g ≫ f) ⁻¹' Xᶜ) (j : ℤ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y X j) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) g hg j).hom
        ((forget R (ModuleCat.of R R) Y' h j).hom ((pullback R (ModuleCat.of R R) f X j).hom x)) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (g ≫ f) hk j).hom x := by
  unfold forget pullback
  rw [map_hom_map_hom g (𝟙 Y') (A := (f ⁻¹' X)ᶜ) hg (compl_subset_compl.mpr h)
      (fun _ hx ↦ compl_subset_compl.mpr h (hg hx)) (Category.comp_id g),
    map_hom_map_hom g f (A' := (f ⁻¹' X)ᶜ) (A := Xᶜ)
      (fun _ hx ↦ compl_subset_compl.mpr h (hg hx)) (fun _ hx ↦ hx) hk rfl]

/-- `forget` after `f^*` is a single map of pairs. -/
lemma forget_hom_pullback_hom {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {X : Set Y} {X' : Set Y'}
    (h : f ⁻¹' X ⊆ X') (hk : X'ᶜ ⊆ f ⁻¹' Xᶜ) (j : ℤ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y X j) :
    (forget R (ModuleCat.of R R) Y' h j).hom ((pullback R (ModuleCat.of R R) f X j).hom x) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) f hk j).hom x := by
  unfold forget pullback
  rw [map_hom_map_hom (𝟙 Y') f (A' := (f ⁻¹' X)ᶜ) (A := Xᶜ) (compl_subset_compl.mpr h)
    (fun _ hx ↦ hx) hk (Category.id_comp f)]

/-- `eqToHom ∘ forget ∘ f^*` is a single map of pairs followed by `congrIndex`. -/
lemma pullback_comp_forget_comp_eqToHom_hom {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {X : Set Y}
    {X' : Set Y'} (h : f ⁻¹' X ⊆ X') {k k' : ℤ} (hk : k = k')
    (hd : cohomologyWithSupports R (ModuleCat.of R R) Y' X' k =
      cohomologyWithSupports R (ModuleCat.of R R) Y' X' k') (hm : X'ᶜ ⊆ f ⁻¹' Xᶜ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y X k) :
    (pullback R (ModuleCat.of R R) f X k ≫ forget R (ModuleCat.of R R) Y' h k ≫
        eqToHom hd).hom x =
      congrIndex R Y' rfl hk
        ((relativeSingularCohomology.map R (ModuleCat.of R R) f hm k).hom x) := by
  subst hk
  rw [eqToHom_refl, Category.comp_id, ModuleCat.hom_comp, LinearMap.comp_apply,
    forget_hom_pullback_hom f h hm]
  rfl

/-- A transport of the source set of a map of pairs is absorbed by `congrIndex`. -/
lemma congrIndex_map_hom {Y' Y : TopCat.{0}} (g : Y' ⟶ Y) {A : Set Y} {T₁ T₂ : Set Y'}
    (hT : T₁ = T₂) (h₁ : T₁ ⊆ g ⁻¹' A) (h₂ : T₂ ⊆ g ⁻¹' A) {k k' : ℤ} (hk : k = k')
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y A k) :
    congrIndex R Y' hT hk ((relativeSingularCohomology.map R (ModuleCat.of R R) g h₁ k).hom x) =
      congrIndex R Y' rfl hk
        ((relativeSingularCohomology.map R (ModuleCat.of R R) g h₂ k).hom x) := by
  subst hT
  rfl

/-- **The cohomological chase behind Lemma 19.2 (b).** Let `ι : N → Y`, `σ : N → T` and
`pr_k : T → P_k` be continuous, `Z_k ⊆ Y`, `O_k ⊆ P_k`, `S_k ⊆ N` closed, with `ι⁻¹ Z_k ⊆ S_k`
and `σ⁻¹ pr_k⁻¹ O_k ⊆ S_k`. If `ι^* u_k = (pr_k ∘ σ)^* a_k` in `H(N, N - S_k)`, then
`ι^* (u₁ ∪ u₂) = σ^* (pr₁^* a₁ ∪ pr₂^* a₂)` in `H(N, N - S₁ ∩ S₂)`. -/
theorem map_cup_eq_map_cup_of_comp {Y N T P₁ P₂ : TopCat.{0}} (ι : N ⟶ Y) (σ : N ⟶ T)
    (pr₁ : T ⟶ P₁) (pr₂ : T ⟶ P₂) {Z₁ Z₂ : Set Y} {O₁ : Set P₁} {O₂ : Set P₂} {S₁ S₂ : Set N}
    (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂) (hO₁ : IsClosed O₁) (hO₂ : IsClosed O₂)
    (hS₁ : IsClosed S₁) (hS₂ : IsClosed S₂) (hιS₁ : ι ⁻¹' Z₁ ⊆ S₁) (hιS₂ : ι ⁻¹' Z₂ ⊆ S₂)
    (hσS₁ : σ ⁻¹' (pr₁ ⁻¹' O₁) ⊆ S₁) (hσS₂ : σ ⁻¹' (pr₂ ⁻¹' O₂) ⊆ S₂) (i j : ℤ)
    (u₁ : cohomologyWithSupports R (ModuleCat.of R R) Y Z₁ i)
    (u₂ : cohomologyWithSupports R (ModuleCat.of R R) Y Z₂ j)
    (a₁ : cohomologyWithSupports R (ModuleCat.of R R) P₁ O₁ i)
    (a₂ : cohomologyWithSupports R (ModuleCat.of R R) P₂ O₂ j)
    (h₁ : (relativeSingularCohomology.map R (ModuleCat.of R R) ι
        (compl_subset_preimage_compl hιS₁) i).hom u₁ =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (σ ≫ pr₁)
        (compl_subset_preimage_compl hσS₁) i).hom a₁)
    (h₂ : (relativeSingularCohomology.map R (ModuleCat.of R R) ι
        (compl_subset_preimage_compl hιS₂) j).hom u₂ =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (σ ≫ pr₂)
        (compl_subset_preimage_compl hσS₂) j).hom a₂) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) ι
        (compl_subset_preimage_compl (inter_subset_inter hιS₁ hιS₂)) (i + j)).hom
        (cup R Y hZ₁ hZ₂ i j u₁ u₂) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) σ
        (compl_subset_preimage_compl (inter_subset_inter hσS₁ hσS₂)) (i + j)).hom
        (cup R T (hO₁.preimage pr₁.hom.continuous) (hO₂.preimage pr₂.hom.continuous) i j
          ((pullback R (ModuleCat.of R R) pr₁ O₁ i).hom a₁)
          ((pullback R (ModuleCat.of R R) pr₂ O₂ j).hom a₂)) := by
  rw [map_cup ι hZ₁ hZ₂ hS₁ hS₂ hιS₁ hιS₂, map_cup σ _ _ hS₁ hS₂ hσS₁ hσS₂, h₁, h₂,
    relativeSingularCohomology.map_comp R _ σ pr₁ (A := O₁ᶜ) (compl_subset_preimage_compl hσS₁)
      (fun _ hx ↦ hx),
    relativeSingularCohomology.map_comp R _ σ pr₂ (A := O₂ᶜ) (compl_subset_preimage_compl hσS₂)
      (fun _ hx ↦ hx)]
  rfl

end cohomologyWithSupports

end MMP
