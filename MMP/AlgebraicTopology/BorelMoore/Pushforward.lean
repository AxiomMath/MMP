module

public import MMP.AlgebraicTopology.BorelMoore.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper push-forward in Borel–Moore homology (Fulton, §19.1)

A proper continuous map `f : X → Y` induces a homomorphism `f_* : H_j X → H_j Y` on Borel–Moore
homology: a locally finite singular chain `∑ a_σ σ` on `X` is sent to `∑ a_σ (f ∘ σ)`. This is a
locally finite chain on `Y` because `f` is proper. Every point `y` of `Y` has compact fibre
`f⁻¹ y`. That fibre has an open neighbourhood `W` meeting the images of only finitely many
simplices of the chain. Since `f` is closed, some neighbourhood `V` of `y` has `f⁻¹ V ⊆ W`. Also,
the simplices with a given image simplex `f ∘ σ = τ` lie in the compact set `f⁻¹(τ(Δ))`, so there
are finitely many of them, and the coefficients of the push-forward are finite sums. Push-forward
commutes with the simplicial operators, so it is a map of simplicial modules, hence of chain
complexes, hence on homology.

## Main definitions

* `MMP.LocallyFiniteChain.properPushforward`: push-forward of locally finite chains
  along a proper map, for abstract "simplices" with carriers.
* `MMP.locallyFiniteSingularChainsMap`: the induced map of simplicial modules of
  locally finite singular chains.
* `MMP.borelMooreHomology.pushforward`: `f_* : H_j X → H_j Y`.

## Main results

* `MMP.LocallyFiniteChain.IsLocallyFiniteSet.image_of_isProperMap`: proper maps
  preserve local finiteness.
* `MMP.borelMooreHomology.pushforward_id`, `pushforward_comp`: functoriality.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960].
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology Topology

universe u

namespace MMP

namespace LocallyFiniteChain

open Classical

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S T U : Type*}
  {car : S → Set X} {carT : T → Set Y}

/-- A proper map preserves local finiteness: if `s` is locally finite for the carriers `car` in
`X`, and `φ : S → T` sends each simplex to one whose carrier lies in the image under the proper
map `f` of its carrier, then `φ '' s` is locally finite for the carriers `carT` in `Y`. -/
lemma IsLocallyFiniteSet.image_of_isProperMap {s : Set S} (hs : IsLocallyFiniteSet car s)
    {f : X → Y} (hf : IsProperMap f) (φ : S → T) (hφ : ∀ σ, carT (φ σ) ⊆ f '' car σ) :
    IsLocallyFiniteSet carT (φ '' s) := fun y ↦ by
  choose V hV hfin using hs
  have hK : IsCompact (f ⁻¹' {y}) := hf.isCompact_preimage isCompact_singleton
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover (fun x ↦ interior (V x))
    (fun x _ ↦ interior_mem_nhds.2 (hV x))
  set W := ⋃ x ∈ t, interior (V x)
  have hVy : (f '' Wᶜ)ᶜ ∈ 𝓝 y := by
    refine (hf.isClosedMap _ (isOpen_biUnion fun x _ ↦ isOpen_interior).isClosed_compl
      ).isOpen_compl.mem_nhds ?_
    rintro ⟨x, hx, rfl⟩
    exact hx (hcover rfl)
  refine ⟨_, hVy, ?_⟩
  have hfinW : {σ | σ ∈ s ∧ (car σ ∩ W).Nonempty}.Finite := by
    refine (t.finite_toSet.biUnion fun x _ ↦ hfin x).subset ?_
    rintro σ ⟨hσ, z, hz, hzW⟩
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 hzW
    exact Set.mem_iUnion₂.2 ⟨x, hx, hσ, z, hz, interior_subset hzx⟩
  refine (hfinW.image φ).subset ?_
  rintro _ ⟨⟨σ, hσ, rfl⟩, p, hp, hpV⟩
  obtain ⟨z, hz, rfl⟩ := hφ σ hp
  refine ⟨σ, ⟨hσ, z, hz, ?_⟩, rfl⟩
  by_contra hzW
  exact hpV ⟨z, hzW, rfl⟩

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- For a locally finite chain `c` on `X`, a proper map `f : X → Y` and a map of simplices
`ψ : S → U` sending carriers into the image under `f`, only finitely many simplices of `c` are
sent to a given simplex with compact nonempty carrier. -/
lemma finite_fiber_of_isProperMap {c : S → M} (hc : c ∈ lfChains R M car) {f : X → Y}
    (hf : IsProperMap f) {carU : U → Set Y} (ψ : S → U) (hψ : ∀ σ, carU (ψ σ) ⊆ f '' car σ)
    (υ : U) (hυ : IsCompact (carU υ)) (hυ' : (carU υ).Nonempty) :
    {σ | c σ ≠ 0 ∧ ψ σ = υ}.Finite := by
  refine (hc.finite_inter_compact (hf.isCompact_preimage hυ)).subset ?_
  rintro σ ⟨h1, rfl⟩
  obtain ⟨p, hp⟩ := hυ'
  obtain ⟨z, hz, rfl⟩ := hψ σ hp
  exact ⟨h1, z, hz, hp⟩

/-- Push-forward of coefficient functions along `φ` is additive on functions whose fibres over
each simplex are finite on the support. -/
lemma pushforwardFun_add_of_finite (φ : S → T) (c d : S → M)
    (hc : ∀ τ, {σ | c σ ≠ 0 ∧ φ σ = τ}.Finite) (hd : ∀ τ, {σ | d σ ≠ 0 ∧ φ σ = τ}.Finite) :
    pushforwardFun φ (c + d) = pushforwardFun φ c + pushforwardFun φ d := by
  ext τ
  let F := (hc τ).toFinset ∪ (hd τ).toFinset
  have hcF : ∀ σ, c σ ≠ 0 → φ σ = τ → σ ∈ F := fun σ h1 h2 ↦
    Finset.mem_union_left _ (by simpa using And.intro h1 h2)
  have hdF : ∀ σ, d σ ≠ 0 → φ σ = τ → σ ∈ F := fun σ h1 h2 ↦
    Finset.mem_union_right _ (by simpa using And.intro h1 h2)
  have hcdF : ∀ σ, (c + d) σ ≠ 0 → φ σ = τ → σ ∈ F := fun σ h1 h2 ↦ by
    by_cases h : c σ = 0
    · exact hdF σ (fun h' ↦ h1 (by simp [h, h'])) h2
    · exact hcF σ h h2
  rw [Pi.add_apply, pushforwardFun_apply_eq_sum φ _ τ F hcdF,
    pushforwardFun_apply_eq_sum φ _ τ F hcF, pushforwardFun_apply_eq_sum φ _ τ F hdF,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  split_ifs <;> simp

/-- Push-forward of coefficient functions along `φ` commutes with scalar multiplication on
functions whose fibres over each simplex are finite on the support. -/
lemma pushforwardFun_smul_of_finite (φ : S → T) (r : R) (c : S → M)
    (hc : ∀ τ, {σ | c σ ≠ 0 ∧ φ σ = τ}.Finite) :
    pushforwardFun φ (r • c) = r • pushforwardFun φ c := by
  ext τ
  let F := (hc τ).toFinset
  have hcF : ∀ σ, c σ ≠ 0 → φ σ = τ → σ ∈ F := fun σ h1 h2 ↦ by
    simpa [F] using And.intro h1 h2
  have hrF : ∀ σ, (r • c) σ ≠ 0 → φ σ = τ → σ ∈ F := fun σ h1 h2 ↦
    hcF σ (fun h ↦ h1 (by simp [h])) h2
  rw [Pi.smul_apply, pushforwardFun_apply_eq_sum φ _ τ F hrF,
    pushforwardFun_apply_eq_sum φ _ τ F hcF, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  split_ifs <;> simp

/-- Push-forward of coefficient functions is functorial, provided the fibres of the composite
are finite on the support. -/
lemma pushforwardFun_comp_of_finite (φ : S → T) (ψ : T → U) (c : S → M)
    (hc : ∀ υ, {σ | c σ ≠ 0 ∧ ψ (φ σ) = υ}.Finite) :
    pushforwardFun ψ (pushforwardFun φ c) = pushforwardFun (ψ ∘ φ) c := by
  ext υ
  let F := (hc υ).toFinset
  have h1 : ∀ σ, c σ ≠ 0 → (ψ ∘ φ) σ = υ → σ ∈ F := fun σ h h' ↦ by
    simpa [F] using And.intro h h'
  have h2 : ∀ τ, pushforwardFun φ c τ ≠ 0 → ψ τ = υ → τ ∈ F.image φ := fun τ h h' ↦ by
    obtain ⟨σ, hσ, rfl⟩ := support_pushforwardFun_subset φ c h
    exact Finset.mem_image_of_mem φ (h1 σ hσ h')
  rw [pushforwardFun_apply_eq_sum _ c υ F h1,
    pushforwardFun_apply_eq_sum ψ _ υ (F.image φ) h2]
  have : ∀ τ ∈ F.image φ, (if ψ τ = υ then pushforwardFun φ c τ else 0) =
      ∑ σ ∈ F, if φ σ = τ then (if ψ τ = υ then c σ else 0) else 0 := fun τ _ ↦ by
    split_ifs with hτ
    · rw [pushforwardFun_apply_eq_sum φ c τ F fun σ h h' ↦ h1 σ h (by simp [h', hτ])]
    · simp
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  rw [Finset.sum_ite_eq (F.image φ) (φ σ), if_pos (Finset.mem_image_of_mem φ hσ)]
  rfl

variable (R M) in
/-- The push-forward of locally finite chains along a proper map `f : X → Y`: a map of simplices
`φ : S → T` with `carT (φ σ) = f '' car σ` (the carriers of `T` compact and nonempty) sends a
locally finite chain `c` to `τ ↦ ∑_{φ σ = τ} c σ`. -/
def properPushforward {f : X → Y} (hf : IsProperMap f) (φ : S → T)
    (hφ : ∀ σ, carT (φ σ) = f '' car σ) (hT : ∀ τ, IsCompact (carT τ) ∧ (carT τ).Nonempty) :
    lfChains R M car →ₗ[R] lfChains R M carT where
  toFun c := ⟨pushforwardFun φ c.1,
    (c.2.image_of_isProperMap hf φ (fun σ ↦ (hφ σ).le)).mono
      (support_pushforwardFun_subset φ c.1)⟩
  map_add' c d := Subtype.ext <| pushforwardFun_add_of_finite φ c.1 d.1
    (fun τ ↦ finite_fiber_of_isProperMap c.2 hf φ (fun σ ↦ (hφ σ).le) τ (hT τ).1 (hT τ).2)
    (fun τ ↦ finite_fiber_of_isProperMap d.2 hf φ (fun σ ↦ (hφ σ).le) τ (hT τ).1 (hT τ).2)
  map_smul' r c := Subtype.ext <| pushforwardFun_smul_of_finite φ r c.1
    (fun τ ↦ finite_fiber_of_isProperMap c.2 hf φ (fun σ ↦ (hφ σ).le) τ (hT τ).1 (hT τ).2)

/-- The coefficient function of `properPushforward R M hf φ hφ hT c` is `pushforwardFun φ c`. -/
lemma properPushforward_apply_coe {f : X → Y} (hf : IsProperMap f) (φ : S → T)
    (hφ : ∀ σ, carT (φ σ) = f '' car σ) (hT : ∀ τ, IsCompact (carT τ) ∧ (carT τ).Nonempty)
    (c : lfChains R M car) :
    (properPushforward R M hf φ hφ hT c : T → M) = pushforwardFun φ c.1 := rfl

end LocallyFiniteChain

open LocallyFiniteChain

section Singular

variable {X Y : TopCat.{u}}

/-- The image of the singular simplex `f ∘ σ` is the image under `f` of the image of `σ`. -/
lemma singularSimplexImage_map {n : SimplexCategoryᵒᵖ} (f : X ⟶ Y)
    (σ : (TopCat.toSSet.obj X).obj n) :
    singularSimplexImage Y ((TopCat.toSSet.map f).app n σ) = f '' singularSimplexImage X σ := by
  simp only [singularSimplexImage]
  rw [← Set.range_comp]
  rfl

/-- The image of a singular simplex is compact and nonempty. -/
lemma singularSimplex_compact_nonempty {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj X).obj n) :
    IsCompact (singularSimplexImage X σ) ∧ (singularSimplexImage X σ).Nonempty :=
  ⟨isCompact_singularSimplexImage σ, nonempty_singularSimplexImage σ⟩

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- The map of simplicial modules of locally finite singular chains induced by a proper map
`f : X → Y`: a simplex `σ` goes to `f ∘ σ`. -/
def locallyFiniteSingularChainsMap (f : X ⟶ Y) (hf : IsProperMap f) :
    locallyFiniteSingularChains R M X ⟶ locallyFiniteSingularChains R M Y where
  app n := ModuleCat.ofHom (properPushforward R M hf ((TopCat.toSSet.map f).app n)
    (singularSimplexImage_map f) singularSimplex_compact_nonempty)
  naturality n m θ := by
    ext c : 2
    apply Subtype.ext
    change pushforwardFun ((TopCat.toSSet.map f).app m)
        (pushforwardFun ((TopCat.toSSet.obj X).map θ) c.1) =
      pushforwardFun ((TopCat.toSSet.obj Y).map θ)
        (pushforwardFun ((TopCat.toSSet.map f).app n) c.1)
    have key : ∀ σ, (TopCat.toSSet.map f).app m ((TopCat.toSSet.obj X).map θ σ) =
        (TopCat.toSSet.obj Y).map θ ((TopCat.toSSet.map f).app n σ) := fun σ ↦
      NatTrans.naturality_apply (TopCat.toSSet.map f) θ σ
    have hsub : ∀ σ, singularSimplexImage Y
        ((TopCat.toSSet.obj Y).map θ ((TopCat.toSSet.map f).app n σ)) ⊆
          f '' singularSimplexImage X σ := fun σ ↦
      (singularSimplexImage_map_subset θ _).trans (singularSimplexImage_map f σ).le
    have hfin := fun υ ↦ finite_fiber_of_isProperMap c.2 hf
        (fun σ ↦ (TopCat.toSSet.obj Y).map θ ((TopCat.toSSet.map f).app n σ)) hsub υ
        (isCompact_singularSimplexImage υ) (nonempty_singularSimplexImage υ)
    rw [pushforwardFun_comp_of_finite _ _ _ (fun υ ↦ by simpa only [key] using hfin υ),
      pushforwardFun_comp_of_finite _ _ _ hfin]
    congr 1

/-- Push-forward of locally finite singular chains along the identity is the identity. -/
lemma locallyFiniteSingularChainsMap_id :
    locallyFiniteSingularChainsMap R M (𝟙 X) (by simpa using isProperMap_id) = 𝟙 _ := by
  ext n c : 3
  apply Subtype.ext
  change pushforwardFun ((TopCat.toSSet.map (𝟙 X)).app n) c.1 = c.1
  have hid : ∀ σ, (TopCat.toSSet.map (𝟙 X)).app n σ = σ := fun σ ↦ by
    rw [CategoryTheory.Functor.map_id]
    rfl
  funext σ
  rw [pushforwardFun_apply_eq_sum _ c.1 σ {σ} (fun σ' _ h ↦ by simp [← h, hid])]
  simp [hid]

/-- Push-forward of locally finite singular chains along `f ≫ g` is the composite of the
push-forwards along `f` and along `g`. -/
lemma locallyFiniteSingularChainsMap_comp {Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f) (hg : IsProperMap g) :
    locallyFiniteSingularChainsMap R M (f ≫ g) (hg.comp hf) =
      locallyFiniteSingularChainsMap R M f hf ≫ locallyFiniteSingularChainsMap R M g hg := by
  ext n c : 3
  apply Subtype.ext
  change pushforwardFun ((TopCat.toSSet.map (f ≫ g)).app n) c.1 =
    pushforwardFun ((TopCat.toSSet.map g).app n) (pushforwardFun ((TopCat.toSSet.map f).app n) c.1)
  have hsub : ∀ σ, singularSimplexImage Z
      ((TopCat.toSSet.map g).app n ((TopCat.toSSet.map f).app n σ)) ⊆
        (g ∘ f) '' singularSimplexImage X σ := fun σ ↦ by
    rw [singularSimplexImage_map, singularSimplexImage_map, Set.image_image]
    rfl
  rw [pushforwardFun_comp_of_finite _ _ _ (fun υ ↦ finite_fiber_of_isProperMap c.2
    (hg.comp hf) _ hsub υ (isCompact_singularSimplexImage υ) (nonempty_singularSimplexImage υ))]
  rfl

end Singular

namespace borelMooreHomology

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {X Y Z : TopCat.{u}}

/-- The map of complexes of locally finite singular chains induced by a proper map. -/
def chainMap (f : X ⟶ Y) (hf : IsProperMap f) :
    borelMooreChainComplex R M X ⟶ borelMooreChainComplex R M Y :=
  (alternatingFaceMapComplex (ModuleCat.{u} R)).map (locallyFiniteSingularChainsMap R M f hf)

/-- The *proper push-forward* `f_* : H_j X → H_j Y` in Borel–Moore homology (Fulton, §19.1),
for a proper continuous map `f : X → Y`, induced by pushing locally finite chains forward along
`f`. -/
def pushforward (f : X ⟶ Y) (hf : IsProperMap f) (j : ℤ) :
    borelMooreHomology R M X j ⟶ borelMooreHomology R M Y j :=
  HomologicalComplex.homologyMap
    (HomologicalComplex.extendMap (chainMap R M f hf) ComplexShape.embeddingDownNat) (-j)

/-- The chain map induced by the identity is the identity. -/
lemma chainMap_id : chainMap R M (𝟙 X) (by simpa using isProperMap_id) = 𝟙 _ := by
  simp only [chainMap, locallyFiniteSingularChainsMap_id]
  exact (alternatingFaceMapComplex (ModuleCat.{u} R)).map_id _

/-- The chain map induced by `f ≫ g` is the composite of the chain maps induced by `f` and `g`. -/
lemma chainMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsProperMap f) (hg : IsProperMap g) :
    chainMap R M (f ≫ g) (hg.comp hf) = chainMap R M f hf ≫ chainMap R M g hg := by
  rw [chainMap, chainMap, chainMap, locallyFiniteSingularChainsMap_comp R M f g hf hg,
    CategoryTheory.Functor.map_comp]
  rfl

/-- Push-forward along the identity is the identity on Borel–Moore homology. -/
lemma pushforward_id (j : ℤ) :
    pushforward R M (𝟙 X) (by simpa using isProperMap_id) j = 𝟙 _ := by
  rw [pushforward, chainMap_id, HomologicalComplex.extendMap_id,
    HomologicalComplex.homologyMap_id]
  rfl

/-- Push-forward along `f ≫ g` is the composite of the push-forwards along `f` and `g`. -/
lemma pushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsProperMap f) (hg : IsProperMap g)
    (j : ℤ) :
    pushforward R M (f ≫ g) (hg.comp hf) j = pushforward R M f hf j ≫ pushforward R M g hg j := by
  rw [pushforward, chainMap_comp, HomologicalComplex.extendMap_comp,
    HomologicalComplex.homologyMap_comp]
  rfl

/-- Push-forward along `e.symm` is a left inverse of push-forward along a homeomorphism `e`. -/
lemma pushforward_symm_pushforward_homeomorph {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (j : ℤ) (a : borelMooreHomology R M (TopCat.of A) j) :
    (pushforward R M (TopCat.ofHom (e.symm : C(B, A))) e.symm.isProperMap j).hom
      ((pushforward R M (TopCat.ofHom (e : C(A, B))) e.isProperMap j).hom a) = a := by
  rw [← ModuleCat.comp_apply, ← pushforward_comp]
  have : TopCat.ofHom (e : C(A, B)) ≫ TopCat.ofHom (e.symm : C(B, A)) = 𝟙 (TopCat.of A) :=
    TopCat.ext fun x ↦ e.symm_apply_apply x
  simp only [this, pushforward_id]
  rfl

/-- Push-forward along a map equal to the identity is bijective. -/
lemma bijective_pushforward_of_eq_id {A : TopCat.{u}} (f : A ⟶ A) (hf : IsProperMap f)
    (h : f = 𝟙 A) (j : ℤ) : Function.Bijective (pushforward R M f hf j).hom := by
  subst h
  rw [pushforward_id]
  exact Function.bijective_id

end borelMooreHomology

end MMP
