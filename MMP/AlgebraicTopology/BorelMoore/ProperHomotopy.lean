module

public import MMP.AlgebraicTopology.BorelMoore.Pushforward
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Proper homotopy invariance of Borel–Moore push-forward (Fulton, §19.1)

Let `f g : Y → Z` be proper maps and let `H : [0, 1] × Y → Z` be a homotopy from `f` to `g`
which is itself a proper map. Then `f_* = g_* : H_k Y → H_k Z` on Borel–Moore homology, in every
degree `k`.

The singular simplicial set functor sends `H` to a combinatorial simplicial homotopy, a family of
maps `h_i` sending a singular `n`-simplex `σ` of `Y` to a singular `(n+1)`-simplex `h_i σ` of `Z`,
namely `H ∘ (α_i, σ ∘ s_i)` for a map `α_i : Δ^{n+1} → [0, 1]` and a degeneracy `s_i`. Its image
lies in `H([0, 1] × σ(Δⁿ))`. Hence `h_i` pushes locally finite chains of `Y` forward to locally
finite chains of `Z`: a family of simplices locally finite in `Y` is locally finite for the
carriers `[0, 1] × σ(Δⁿ)` in `[0, 1] × Y`, and `H` is proper. Since the simplicial identities of a
simplicial homotopy hold simplex by simplex, these push-forwards form a simplicial homotopy between
the maps of simplicial modules of locally finite chains induced by `f` and `g`. Its alternating sum
is a chain homotopy, so `f` and `g` induce the same map on homology.

## Main definitions

* `MMP.LocallyFiniteChain.IsLocallyFiniteMap`: maps of simplices that push locally
  finite chains forward.
* `MMP.LocallyFiniteChain.lfMap`: the push-forward along such a map.
* `MMP.locallyFiniteSingularChainsHomotopy`: the simplicial homotopy between the
  push-forwards of locally finite singular chains along properly homotopic maps.
* `MMP.borelMooreHomology.chainMapHomotopy`: the induced chain homotopy.

## Main results

* `MMP.borelMooreHomology.pushforward_eq_of_properHomotopy`: properly homotopic
  proper maps induce the same push-forward on Borel–Moore homology.
* `MMP.borelMooreHomology.isProperMap_of_properHomotopy_left`,
  `isProperMap_of_properHomotopy_right`: the ends of a proper homotopy are proper.

## Implementation notes

The homotopy is a homotopy `[0, 1] × Y → Z` in the sense of `ContinuousMap.Homotopy`, the unit
interval as first factor, and properness is asked of it as a map out of `[0, 1] × Y`; this is the
same as properness out of `Y × [0, 1]`. The coefficients are any module `M` over a commutative
ring `R`, as for the push-forward.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960].
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Simplicial MonoidalCategory
  CartesianMonoidalCategory

universe u

namespace MMP

namespace LocallyFiniteChain

section LocallyFiniteMap

variable {X Y Z P : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace P] {S T U : Type*} {car : S → Set X} {carT : T → Set Y} {carU : U → Set Z}

/-- A map of simplices `φ : S → T` is *locally finite* (for the carriers `car` and `carT`) if it
sends locally finite sets of simplices to locally finite sets, with finite fibres on them. Such a
map pushes locally finite chains forward to locally finite chains. -/
def IsLocallyFiniteMap (car : S → Set X) (carT : T → Set Y) (φ : S → T) : Prop :=
  ∀ s, IsLocallyFiniteSet car s → IsLocallyFiniteSet carT (φ '' s) ∧ ∀ τ, (s ∩ φ ⁻¹' {τ}).Finite

/-- A composite of locally finite maps of simplices is locally finite. -/
lemma IsLocallyFiniteMap.comp {ψ : T → U} {φ : S → T} (hψ : IsLocallyFiniteMap carT carU ψ)
    (hφ : IsLocallyFiniteMap car carT φ) : IsLocallyFiniteMap car carU (ψ ∘ φ) := by
  intro s hs
  obtain ⟨h1, h2⟩ := hφ s hs
  obtain ⟨h3, h4⟩ := hψ _ h1
  refine ⟨by rwa [Set.image_comp], fun υ ↦ ?_⟩
  refine ((h4 υ).biUnion fun τ _ ↦ h2 τ).subset ?_
  rintro σ ⟨hσ, hυ⟩
  exact Set.mem_biUnion (x := φ σ) ⟨⟨σ, hσ, rfl⟩, hυ⟩ ⟨hσ, rfl⟩

/-- A map of simplices sending each carrier into the image, under a proper map `F : P → Y`, of a
second carrier `car'` (for which every `car`-locally finite set is locally finite) is locally
finite, when the carriers of `T` are compact and nonempty. -/
lemma isLocallyFiniteMap_of_isProperMap {car' : S → Set P}
    (hcar' : ∀ s, IsLocallyFiniteSet car s → IsLocallyFiniteSet car' s)
    {F : P → Y} (hF : IsProperMap F) (φ : S → T) (hφ : ∀ σ, carT (φ σ) ⊆ F '' car' σ)
    (hT : ∀ τ, IsCompact (carT τ) ∧ (carT τ).Nonempty) : IsLocallyFiniteMap car carT φ := by
  intro s hs
  refine ⟨(hcar' s hs).image_of_isProperMap hF φ hφ, fun τ ↦ ?_⟩
  refine ((hcar' s hs).finite_inter_compact (hF.isCompact_preimage (hT τ).1)).subset ?_
  rintro σ ⟨hσ, rfl⟩
  obtain ⟨p, hp⟩ := (hT (φ σ)).2
  obtain ⟨z, hz, hzp⟩ := hφ σ hp
  exact ⟨hσ, z, hz, show F z ∈ carT (φ σ) from hzp ▸ hp⟩

/-- A carrier-decreasing map of simplices is locally finite. -/
lemma isLocallyFiniteMap_of_subset {carT : T → Set X} (φ : S → T) (hφ : ∀ σ, carT (φ σ) ⊆ car σ)
    (hT : ∀ τ, IsCompact (carT τ) ∧ (carT τ).Nonempty) : IsLocallyFiniteMap car carT φ :=
  isLocallyFiniteMap_of_isProperMap (fun _ hs ↦ hs) isProperMap_id φ (by simpa using hφ) hT

/-- A set of simplices locally finite for `car` in `X` is locally finite for `P × car` in
`P × X`. -/
lemma IsLocallyFiniteSet.univ_prod {s : Set S} (hs : IsLocallyFiniteSet car s) :
    IsLocallyFiniteSet (fun σ ↦ (Set.univ : Set P) ×ˢ car σ) s := by
  rintro ⟨t, x⟩
  obtain ⟨V, hV, hfin⟩ := hs x
  refine ⟨Prod.snd ⁻¹' V, continuous_snd.continuousAt.preimage_mem_nhds hV, hfin.subset ?_⟩
  rintro σ ⟨hσ, q, ⟨-, hq⟩, hqV⟩
  exact ⟨hσ, q.2, hq, hqV⟩

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- For a locally finite chain `c` and a locally finite map of simplices `φ`, each fibre of `φ`
meets the support of `c` in a finite set. -/
lemma finite_fiber_of_isLocallyFiniteMap {c : S → M} (hc : c ∈ lfChains R M car) {φ : S → T}
    (hφ : IsLocallyFiniteMap car carT φ) (τ : T) : {σ | c σ ≠ 0 ∧ φ σ = τ}.Finite :=
  (hφ _ hc).2 τ

/-- Pushing a locally finite chain forward along `φ` and then `ψ`, both locally finite, is pushing
it forward along `ψ ∘ φ`. -/
lemma pushforwardFun_comp_of_isLocallyFiniteMap {c : S → M} (hc : c ∈ lfChains R M car)
    {φ : S → T} {ψ : T → U} (hφ : IsLocallyFiniteMap car carT φ)
    (hψ : IsLocallyFiniteMap carT carU ψ) :
    pushforwardFun ψ (pushforwardFun φ c) = pushforwardFun (ψ ∘ φ) c :=
  pushforwardFun_comp_of_finite φ ψ c (finite_fiber_of_isLocallyFiniteMap hc (hψ.comp hφ))

/-- Two composites of locally finite maps of simplices that agree push chains forward alike. -/
lemma pushforwardFun_comp_eq {Y' T' : Type*} [TopologicalSpace Y'] {carT' : T' → Set Y'}
    {c : S → M} (hc : c ∈ lfChains R M car) {φ : S → T} {ψ : T → U} {φ' : S → T'} {ψ' : T' → U}
    (hφ : IsLocallyFiniteMap car carT φ) (hψ : IsLocallyFiniteMap carT carU ψ)
    (hφ' : IsLocallyFiniteMap car carT' φ') (hψ' : IsLocallyFiniteMap carT' carU ψ')
    (h : ψ ∘ φ = ψ' ∘ φ') :
    pushforwardFun ψ (pushforwardFun φ c) = pushforwardFun ψ' (pushforwardFun φ' c) := by
  rw [pushforwardFun_comp_of_isLocallyFiniteMap hc hφ hψ,
    pushforwardFun_comp_of_isLocallyFiniteMap hc hφ' hψ', h]

variable (R M) in
/-- The push-forward of locally finite chains along a locally finite map of simplices. -/
def lfMap (φ : S → T) (hφ : IsLocallyFiniteMap car carT φ) :
    lfChains R M car →ₗ[R] lfChains R M carT where
  toFun c := ⟨pushforwardFun φ c.1, (hφ _ c.2).1.mono (support_pushforwardFun_subset φ c.1)⟩
  map_add' c d := Subtype.ext <| pushforwardFun_add_of_finite φ c.1 d.1
    (finite_fiber_of_isLocallyFiniteMap c.2 hφ) (finite_fiber_of_isLocallyFiniteMap d.2 hφ)
  map_smul' r c := Subtype.ext <| pushforwardFun_smul_of_finite φ r c.1
    (finite_fiber_of_isLocallyFiniteMap c.2 hφ)

/-- The underlying function of `lfMap R M φ hφ c` is the push-forward of `c` along `φ`. -/
@[simp]
lemma lfMap_apply_coe (φ : S → T) (hφ : IsLocallyFiniteMap car carT φ) (c : lfChains R M car) :
    (lfMap R M φ hφ c : T → M) = pushforwardFun φ c.1 := rfl

end LocallyFiniteMap

end LocallyFiniteChain

open LocallyFiniteChain

/-- The simplex `h_i σ` of the simplicial homotopy induced by a homotopy `H` lies in
`H([0, 1] × σ(Δⁿ))`. -/
lemma singularSimplexImage_homotopy_h_subset {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) {n : ℕ} (i : Fin (n + 1)) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularSimplexImage Y (H.toSSet.toSimplicialObjectHomotopy.h i σ) ⊆
      H '' (Set.univ ×ˢ singularSimplexImage X σ) := by
  simp only [SSet.Homotopy.toSimplicialObjectHomotopy, TopCat.Homotopy.toSSet]
  set p := (SSet.prodStdSimplex₁.nonDegenerateEquiv i).1
  set w := (SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫
    TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI).app (op ⦋n + 1⦌) p with hw
  set y := (Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I).app (op ⦋n + 1⦌) w with hy
  have h1 : (TopCat.toSSet.map (fst X TopCat.I)).app _ y = w.1 :=
    congrArg (fun φ ↦ φ.app (op ⦋n + 1⦌) w) (Functor.Monoidal.μ_fst TopCat.toSSet X TopCat.I)
  have h2 : w.1 = (TopCat.toSSet.obj X).map (SSet.stdSimplex.objEquiv p.1).op σ := rfl
  have e : (ConcreteCategory.hom
          (↾fun x ↦
            (ConcreteCategory.hom
                ((SSet.yonedaEquiv.symm x ▷ Δ[1] ≫
                      TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
                        Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I ≫ TopCat.toSSet.map H.h).app
                  (op ⦋n + 1⦌)))
              p)) σ = (TopCat.toSSet.map H.h).app _ y := rfl
  rw [e, singularSimplexImage_map]
  rintro _ ⟨q, hq, rfl⟩
  have hq1 : q.1 ∈ singularSimplexImage X σ := by
    have : q.1 ∈ singularSimplexImage X ((TopCat.toSSet.map (fst X TopCat.I)).app _ y) := by
      rw [singularSimplexImage_map]
      exact ⟨q, hq, rfl⟩
    rw [h1, h2] at this
    exact singularSimplexImage_map_subset _ _ this
  exact ⟨(TopCat.I.homeomorph q.2, q.1), ⟨trivial, hq1⟩, rfl⟩

section Singular

/-- A commutative triangle of maps of types, as an equality of functions. -/
lemma hom_comp_eq_of_comp_eq {A B C : Type u} {a : A ⟶ B} {b : B ⟶ C} {c : A ⟶ C}
    (h : a ≫ b = c) : ⇑(ConcreteCategory.hom b) ∘ ⇑(ConcreteCategory.hom a) =
      ⇑(ConcreteCategory.hom c) := by
  funext x
  exact ConcreteCategory.congr_hom h x

/-- A commutative square of maps of types, as an equality of functions. -/
lemma hom_comp_eq_of_comp_eq_comp {A B B' C : Type u} {a : A ⟶ B} {b : B ⟶ C} {a' : A ⟶ B'}
    {b' : B' ⟶ C} (h : a ≫ b = a' ≫ b') :
    ⇑(ConcreteCategory.hom b) ∘ ⇑(ConcreteCategory.hom a) =
      ⇑(ConcreteCategory.hom b') ∘ ⇑(ConcreteCategory.hom a') := by
  funext x
  exact ConcreteCategory.congr_hom h x

variable {X Y : TopCat.{u}}

/-- Each simplicial operator `θ` of the singular simplicial set of `X` is a locally finite map of
singular simplices. -/
lemma isLocallyFiniteMap_simplicialMap {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    IsLocallyFiniteMap (singularSimplexImage X (n := n)) (singularSimplexImage X (n := m))
      ((TopCat.toSSet.obj X).map θ) :=
  isLocallyFiniteMap_of_subset _ (singularSimplexImage_map_subset θ)
    singularSimplex_compact_nonempty

/-- The map of singular `n`-simplices induced by a proper map `f : X ⟶ Y` is locally finite. -/
lemma isLocallyFiniteMap_toSSet_map {f : X ⟶ Y} (hf : IsProperMap f) (n : SimplexCategoryᵒᵖ) :
    IsLocallyFiniteMap (singularSimplexImage X (n := n)) (singularSimplexImage Y (n := n))
      ((TopCat.toSSet.map f).app n) :=
  isLocallyFiniteMap_of_isProperMap (fun _ hs ↦ hs) hf _
    (fun σ ↦ (singularSimplexImage_map f σ).le) singularSimplex_compact_nonempty

/-- For a homotopy `H` which is a proper map, each map `h_i` of the induced simplicial homotopy is
a locally finite map from singular `n`-simplices of `X` to singular `(n+1)`-simplices of `Y`. -/
lemma isLocallyFiniteMap_homotopy_h {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (hH : IsProperMap H) {n : ℕ} (i : Fin (n + 1)) :
    IsLocallyFiniteMap (singularSimplexImage X (n := op ⦋n⦌))
      (singularSimplexImage Y (n := op ⦋n + 1⦌)) (H.toSSet.toSimplicialObjectHomotopy.h i) :=
  isLocallyFiniteMap_of_isProperMap (fun _ hs ↦ hs.univ_prod) hH _
    (singularSimplexImage_homotopy_h_subset H i) singularSimplex_compact_nonempty

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- A homotopy `H : I × X → Y` from `f` to `g` which is a proper map induces a simplicial homotopy
between the push-forwards of locally finite singular chains along `f` and `g`. -/
def locallyFiniteSingularChainsHomotopy {f g : X ⟶ Y} (hf : IsProperMap f) (hg : IsProperMap g)
    (H : TopCat.Homotopy f g) (hH : IsProperMap H) :
    SimplicialObject.Homotopy (locallyFiniteSingularChainsMap R M f hf)
      (locallyFiniteSingularChainsMap R M g hg) where
  h i := ModuleCat.ofHom (lfMap R M _ (isLocallyFiniteMap_homotopy_h H hH i))
  h_zero_comp_δ_zero n := by
    ext c : 2
    exact Subtype.ext <| (pushforwardFun_comp_of_isLocallyFiniteMap c.2
      (isLocallyFiniteMap_homotopy_h H hH 0) (isLocallyFiniteMap_simplicialMap _)).trans
        (congrArg (fun φ ↦ pushforwardFun φ c.1) (hom_comp_eq_of_comp_eq
          (H.toSSet.toSimplicialObjectHomotopy.h_zero_comp_δ_zero n)))
  h_last_comp_δ_last n := by
    ext c : 2
    exact Subtype.ext <| (pushforwardFun_comp_of_isLocallyFiniteMap c.2
      (isLocallyFiniteMap_homotopy_h H hH _) (isLocallyFiniteMap_simplicialMap _)).trans
        (congrArg (fun φ ↦ pushforwardFun φ c.1) (hom_comp_eq_of_comp_eq
          (H.toSSet.toSimplicialObjectHomotopy.h_last_comp_δ_last n)))
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    ext c : 2
    exact Subtype.ext <| pushforwardFun_comp_eq c.2 (isLocallyFiniteMap_homotopy_h H hH j.succ)
      (isLocallyFiniteMap_simplicialMap (X := Y) _) (isLocallyFiniteMap_simplicialMap (X := X) _)
      (isLocallyFiniteMap_homotopy_h H hH j) (hom_comp_eq_of_comp_eq_comp
        (H.toSSet.toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_of_lt i j hij))
  h_succ_comp_δ_castSucc_succ j := by
    ext c : 2
    exact Subtype.ext <| pushforwardFun_comp_eq c.2 (isLocallyFiniteMap_homotopy_h H hH _)
      (isLocallyFiniteMap_simplicialMap _) (isLocallyFiniteMap_homotopy_h H hH _)
      (isLocallyFiniteMap_simplicialMap _) (hom_comp_eq_of_comp_eq_comp
        (H.toSSet.toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_succ j))
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    ext c : 2
    exact Subtype.ext <| pushforwardFun_comp_eq c.2 (isLocallyFiniteMap_homotopy_h H hH j.castSucc)
      (isLocallyFiniteMap_simplicialMap (X := Y) _) (isLocallyFiniteMap_simplicialMap (X := X) _)
      (isLocallyFiniteMap_homotopy_h H hH j) (hom_comp_eq_of_comp_eq_comp
        (H.toSSet.toSimplicialObjectHomotopy.h_castSucc_comp_δ_succ_of_lt i j hji))
  h_comp_σ_castSucc_of_le i j hij := by
    ext c : 2
    exact Subtype.ext <| pushforwardFun_comp_eq c.2 (isLocallyFiniteMap_homotopy_h H hH j)
      (isLocallyFiniteMap_simplicialMap (X := Y) _) (isLocallyFiniteMap_simplicialMap (X := X) _)
      (isLocallyFiniteMap_homotopy_h H hH j.succ) (hom_comp_eq_of_comp_eq_comp
        (H.toSSet.toSimplicialObjectHomotopy.h_comp_σ_castSucc_of_le i j hij))
  h_comp_σ_succ_of_lt i j hji := by
    ext c : 2
    exact Subtype.ext <| pushforwardFun_comp_eq c.2 (isLocallyFiniteMap_homotopy_h H hH j)
      (isLocallyFiniteMap_simplicialMap (X := Y) _) (isLocallyFiniteMap_simplicialMap (X := X) _)
      (isLocallyFiniteMap_homotopy_h H hH j.castSucc) (hom_comp_eq_of_comp_eq_comp
        (H.toSSet.toSimplicialObjectHomotopy.h_comp_σ_succ_of_lt i j hji))

end Singular

namespace borelMooreHomology

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y Z : TopCat.{u}}

/-- A proper homotopy between proper maps `f` and `g` gives a chain homotopy between the induced
maps of complexes of locally finite singular chains. -/
def chainMapHomotopy {f g : Y ⟶ Z} (hf : IsProperMap f) (hg : IsProperMap g)
    (H : TopCat.Homotopy f g) (hH : IsProperMap H) :
    Homotopy (chainMap R M f hf) (chainMap R M g hg) :=
  (locallyFiniteSingularChainsHomotopy R M hf hg H hH).toChainHomotopy

/-- **Proper homotopy invariance of Borel–Moore push-forward.** If `f g : Y → Z` are proper maps
joined by a homotopy `H : [0, 1] × Y → Z` which is itself a proper map, then
`f_* = g_* : H_k Y → H_k Z` in every degree `k`. -/
theorem pushforward_eq_of_properHomotopy {f g : Y ⟶ Z} (hf : IsProperMap f) (hg : IsProperMap g)
    (H : TopCat.Homotopy f g) (hH : IsProperMap H) (k : ℤ) :
    pushforward R M f hf k = pushforward R M g hg k :=
  ((chainMapHomotopy R M hf hg H hH).extend ComplexShape.embeddingDownNat).homologyMap_eq (-k)

/-- Each stage `y ↦ H (t, y)` of a proper homotopy `H` is a proper map. -/
lemma isProperMap_homotopy_apply {f g : Y ⟶ Z} (H : TopCat.Homotopy f g) (hH : IsProperMap H)
    (t : unitInterval) : IsProperMap fun y ↦ H (t, y) := by
  refine hH.comp (Topology.IsClosedEmbedding.isProperMap ⟨isEmbedding_prodMkRight t, ?_⟩)
  rw [show Set.range (fun y : Y ↦ (t, y)) = {t} ×ˢ Set.univ by ext ⟨s, y⟩; simp [eq_comm]]
  exact isClosed_singleton.prod isClosed_univ

/-- The starting map `f` of a proper homotopy `H` from `f` to `g` is proper. -/
lemma isProperMap_of_properHomotopy_left {f g : Y ⟶ Z} (H : TopCat.Homotopy f g)
    (hH : IsProperMap H) : IsProperMap f := by
  have : (f : Y → Z) = fun y ↦ H (0, y) := funext fun y ↦ (H.apply_zero y).symm
  exact this ▸ isProperMap_homotopy_apply H hH 0

/-- The final map `g` of a proper homotopy `H` from `f` to `g` is proper. -/
lemma isProperMap_of_properHomotopy_right {f g : Y ⟶ Z} (H : TopCat.Homotopy f g)
    (hH : IsProperMap H) : IsProperMap g := by
  have : (g : Y → Z) = fun y ↦ H (1, y) := funext fun y ↦ (H.apply_one y).symm
  exact this ▸ isProperMap_homotopy_apply H hH 1

end borelMooreHomology

end MMP
