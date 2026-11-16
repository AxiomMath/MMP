module

public import MMP.AlgebraicTopology.BorelMoore.LongExact
public import MMP.AlgebraicTopology.BorelMoore.ProperHomotopy
public import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
public import MMP.AlgebraicTopology.BorelMoore.DisjointUnion
public import MMP.AlgebraicTopology.CapProduct.Neighbourhood

/-!
# The deformation operator of the Borel–Moore long exact sequence

Let `X` be a closed subset of a Hausdorff space `Y`, `U = Y - X`, and let `G : N × [0, 1] → Y`
be a proper homotopy, on a closed set `N ⊇ X`, from the inclusion to a map into `X`, fixing `X`.
On `A = N - X` the homotopy `G` does not give a proper map into `U`, but its restriction to the
open set `W = G⁻¹(U) ⊆ [0, 1] × A` does. The operator
`H : C^lf_n(A) → C^lf_{n+1}(U)`, `H = G_{W*} ∘ (·)|_W ∘ P`, with `P` the prism operator of
`[0, 1] × A`, satisfies `ι_* c = ∂ H c + H ∂ c` for the inclusion `ι : A → U` (the end
`{1} × A` of the prism misses `W`, the end `{0} × A` lies in it). On a closed set `B ⊆ A` it is
the restriction to `U` of the chain homotopy of `G|_B` (`restrictChainMap_fillChainHomotopy`).

## Main definitions

* `MMP.borelMooreHomology.chainPart`: the part of a chain on a set of simplices.
* `MMP.borelMooreHomology.prismHomotopy`: the prism chain homotopy of `[0, 1] × P`.
* `MMP.borelMooreHomology.deformOp`: the operator `H`.
* `MMP.borelMooreHomology.fillChainHomotopy`: the chain homotopy of `G|_B`.

## Main results

* `MMP.borelMooreHomology.chainMapHomotopy_hom_natural`: naturality of the chain
  homotopy of a proper homotopy.
* `MMP.borelMooreHomology.restrictChainMap_apply_of_isSupportedIn`: restricting a
  chain supported in `V` keeps its coefficients.
* `MMP.borelMooreHomology.chainMap_deformDomain_eq_succ`, `chainMap_deformDomain_eq_zero`:
  `ι_* c = ∂ H c + H ∂ c`.
* `MMP.borelMooreHomology.restrictChainMap_fillChainHomotopy`: `(h_B β)|_U = H (β|_A)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial MonoidalCategory

universe u v

namespace MMP.SimplicialHomotopy

open CategoryTheory CategoryTheory.SimplicialObject CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] {X X' Y Y' : SimplicialObject C}
  {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- The chain homotopy of a simplicial homotopy is natural. -/
lemma toChainHomotopy_hom_natural (H : Homotopy f g) (H' : Homotopy f' g') (a : X' ⟶ X)
    (b : Y ⟶ Y') (h : ∀ n (i : Fin (n + 1)), a.app _ ≫ H.h i ≫ b.app _ = H'.h i) (p q : ℕ) :
    ((alternatingFaceMapComplex C).map a).f p ≫ H.toChainHomotopy.hom p q ≫
      ((alternatingFaceMapComplex C).map b).f q = H'.toChainHomotopy.hom p q := by
  simp only [toChainHomotopy, ToChainHomotopy.hom, alternatingFaceMapComplex_map_f]
  split_ifs with hpq
  · subst hpq
    simp [Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_neg,
      Preadditive.neg_comp, h]
  · simp

end MMP.SimplicialHomotopy

namespace MMP.SSetHomotopy

open SSet SSet.Homotopy

/-- The combinatorial homotopy of a homotopy of simplicial sets is natural. -/
lemma toSimplicialObjectHomotopy_h_natural {X X' Y Y' : SSet.{u}} {f g : X ⟶ Y}
    {f' g' : X' ⟶ Y'} (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g') (a : X' ⟶ X)
    (b : Y ⟶ Y') (h : H'.h = a ▷ Δ[1] ≫ H.h ≫ b) {n : ℕ} (i : Fin (n + 1)) (x : X' _⦋n⦌) :
    H'.toSimplicialObjectHomotopy.h i x =
      b.app _ (H.toSimplicialObjectHomotopy.h i (a.app _ x)) := by
  have key : SSet.yonedaEquiv.symm x ▷ Δ[1] ≫ H'.h =
      (SSet.yonedaEquiv.symm (a.app _ x) ▷ Δ[1] ≫ H.h) ≫ b := by
    rw [h, ← SSet.yonedaEquiv_symm_comp, comp_whiskerRight]
    simp only [Category.assoc]
  exact ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.app (op ⦋n + 1⦌)) key) _

end MMP.SSetHomotopy

namespace MMP.TopCatHomotopy

open TopCat TopCat.Homotopy

/-- The simplicial homotopy of a homotopy of spaces is natural. -/
lemma toSSet_h_natural {X X' Y Y' : TopCat.{u}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g') (a : X' ⟶ X) (b : Y ⟶ Y')
    (h : ∀ p, H' p = b (H (p.1, a p.2))) :
    H'.toSSet.h = TopCat.toSSet.map a ▷ Δ[1] ≫ H.toSSet.h ≫ TopCat.toSSet.map b := by
  have e : H'.h = a ▷ TopCat.I ≫ H.h ≫ b := by
    ext p
    exact h (TopCat.I.homeomorph p.2, p.1)
  simp only [TopCat.Homotopy.toSSet, e, Functor.map_comp, Category.assoc]
  rw [← whisker_exchange_assoc, Functor.LaxMonoidal.μ_natural_left_assoc]

end MMP.TopCatHomotopy

namespace MMP

open LocallyFiniteChain

section natural

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- If `H' = b ∘ H ∘ (1 × a)` for proper maps `a` and `b`, then the simplicial homotopy of locally
finite chains of `H'` is `b_* ∘ h_H ∘ a_*`. -/
lemma locallyFiniteSingularChainsHomotopy_h_natural {X X' Y Y' : TopCat.{u}} {f g : X ⟶ Y}
    {f' g' : X' ⟶ Y'} (hf : IsProperMap f) (hg : IsProperMap g) (hf' : IsProperMap f')
    (hg' : IsProperMap g') (H : TopCat.Homotopy f g) (hH : IsProperMap H)
    (H' : TopCat.Homotopy f' g') (hH' : IsProperMap H') {a : X' ⟶ X} (ha : IsProperMap a)
    {b : Y ⟶ Y'} (hb : IsProperMap b) (h : ∀ p, H' p = b (H (p.1, a p.2))) {n : ℕ}
    (i : Fin (n + 1)) :
    (locallyFiniteSingularChainsMap R M a ha).app _ ≫
        (locallyFiniteSingularChainsHomotopy R M hf hg H hH).h i ≫
          (locallyFiniteSingularChainsMap R M b hb).app _ =
      (locallyFiniteSingularChainsHomotopy R M hf' hg' H' hH').h i := by
  ext c : 2
  apply Subtype.ext
  change pushforwardFun ((TopCat.toSSet.map b).app _) (pushforwardFun
    (H.toSSet.toSimplicialObjectHomotopy.h i) (pushforwardFun ((TopCat.toSSet.map a).app _) c.1)) =
    pushforwardFun (H'.toSSet.toSimplicialObjectHomotopy.h i) c.1
  rw [pushforwardFun_comp_of_isLocallyFiniteMap c.2 (isLocallyFiniteMap_toSSet_map ha _)
      (isLocallyFiniteMap_homotopy_h H hH i),
    pushforwardFun_comp_of_isLocallyFiniteMap c.2
      ((isLocallyFiniteMap_homotopy_h H hH i).comp (isLocallyFiniteMap_toSSet_map ha _))
      (isLocallyFiniteMap_toSSet_map hb _)]
  congr 1
  funext x
  exact (SSetHomotopy.toSimplicialObjectHomotopy_h_natural _ _ _ _
    (TopCatHomotopy.toSSet_h_natural H H' a b h) i x).symm

namespace borelMooreHomology

/-- **Naturality of the chain homotopy of a proper homotopy.** If `H' = b ∘ H ∘ (1 × a)` for
proper maps `a` and `b`, then `h_{H'} = b_* ∘ h_H ∘ a_*`. -/
lemma chainMapHomotopy_hom_natural {X X' Y Y' : TopCat.{u}} {f g : X ⟶ Y}
    {f' g' : X' ⟶ Y'} (hf : IsProperMap f) (hg : IsProperMap g) (hf' : IsProperMap f')
    (hg' : IsProperMap g') (H : TopCat.Homotopy f g) (hH : IsProperMap H)
    (H' : TopCat.Homotopy f' g') (hH' : IsProperMap H') {a : X' ⟶ X} (ha : IsProperMap a)
    {b : Y ⟶ Y'} (hb : IsProperMap b) (h : ∀ p, H' p = b (H (p.1, a p.2))) (p q : ℕ) :
    (chainMap R M a ha).f p ≫ (chainMapHomotopy R M hf hg H hH).hom p q ≫
      (chainMap R M b hb).f q = (chainMapHomotopy R M hf' hg' H' hH').hom p q :=
  SimplicialHomotopy.toChainHomotopy_hom_natural _ _ _ _
    (fun _ i ↦ locallyFiniteSingularChainsHomotopy_h_natural R M hf hg hf' hg' H hH H' hH' ha hb
      h i) p q

end borelMooreHomology

end natural

namespace borelMooreHomology

section support

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- The `R`-linear map keeping the coefficients of a locally finite chain on the simplices in `s`
and zeroing the rest. -/
def lfPart {X : Type*} [TopologicalSpace X] {S : Type*} {car : S → Set X} (s : Set S) :
    lfChains R M car →ₗ[R] lfChains R M car where
  toFun c := ⟨s.indicator c.1, (show IsLocallyFiniteSet _ _ from c.2).mono
    (fun σ hσ h ↦ hσ (by simp [h]))⟩
  map_add' c d := Subtype.ext (Set.indicator_add s c.1 d.1)
  map_smul' r c := Subtype.ext (Set.indicator_const_smul s r c.1)

/-- The part of a locally finite chain on a set `s` of simplices. -/
def chainPart {P : TopCat.{u}} {n : ℕ} (s : Set ((TopCat.toSSet.obj P).obj (op ⦋n⦌))) :
    (borelMooreChainComplex R M P).X n ⟶ (borelMooreChainComplex R M P).X n :=
  ModuleCat.ofHom (lfPart R M s)

/-- The coefficients of the part of `c` on `s` are those of `c` on `s` and zero off `s`. -/
lemma chainPart_apply_coe {P : TopCat.{u}} {n : ℕ} (s : Set ((TopCat.toSSet.obj P).obj (op ⦋n⦌)))
    (c : (borelMooreChainComplex R M P).X n) :
    ((chainPart R M s).hom c).1 = s.indicator c.1 := rfl

/-- A chain is the sum of its parts on `s` and on the complement of `s`. -/
lemma chainPart_add_chainPart_compl {P : TopCat.{u}} {n : ℕ}
    (s : Set ((TopCat.toSSet.obj P).obj (op ⦋n⦌))) (c : (borelMooreChainComplex R M P).X n) :
    (chainPart R M s).hom c + (chainPart R M sᶜ).hom c = c :=
  Subtype.ext (Set.indicator_self_add_compl s c.1)

variable {R M}

/-- The coefficient of a simplex in a sum of chains is the sum of its coefficients. -/
lemma coe_add_apply {P : TopCat.{u}} {n : ℕ} (c d : (borelMooreChainComplex R M P).X n) (σ) :
    (c + d).1 σ = c.1 σ + d.1 σ := rfl

/-- The coefficient of a simplex in `-c` is the negative of its coefficient in `c`. -/
lemma coe_neg_apply {P : TopCat.{u}} {n : ℕ} (c : (borelMooreChainComplex R M P).X n) (σ) :
    (-c).1 σ = -c.1 σ := rfl

/-- The part of a chain on the simplices with image in `N` is supported in `N`. -/
lemma isSupportedIn_chainPart {P : TopCat.{u}} {n : ℕ} {N : Set P}
    (c : (borelMooreChainComplex R M P).X n) :
    IsSupportedIn R M N ((chainPart R M {σ | singularSimplexImage P σ ⊆ N}).hom c) := by
  intro σ hσ
  by_contra h
  rw [chainPart_apply_coe] at hσ
  exact hσ (Set.indicator_of_notMem h _)

/-- Every part of a chain supported in `N` is supported in `N`. -/
lemma IsSupportedIn.chainPart {P : TopCat.{u}} {n : ℕ} {N : Set P}
    {c : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M N c)
    (s : Set ((TopCat.toSSet.obj P).obj (op ⦋n⦌))) :
    IsSupportedIn R M N ((borelMooreHomology.chainPart R M s).hom c) := fun σ hσ ↦ by
  refine hc σ fun h ↦ hσ ?_
  rw [chainPart_apply_coe]
  classical
  by_cases hs : σ ∈ s
  · rwa [Set.indicator_of_mem hs]
  · exact Set.indicator_of_notMem hs _

/-- A chain supported in `N` is supported in every `N' ⊇ N`. -/
lemma IsSupportedIn.mono {P : TopCat.{u}} {n : ℕ} {N N' : Set P}
    {c : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M N c) (h : N ⊆ N') :
    IsSupportedIn R M N' c := fun σ hσ ↦ (hc σ hσ).trans h

/-- A sum of chains supported in `N` is supported in `N`. -/
lemma IsSupportedIn.add {P : TopCat.{u}} {n : ℕ} {N : Set P}
    {c d : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M N c)
    (hd : IsSupportedIn R M N d) : IsSupportedIn R M N (c + d) := fun σ hσ ↦ by
  rw [coe_add_apply] at hσ
  by_cases h : c.1 σ = 0
  · exact hd σ fun h' ↦ hσ (by rw [h, h', add_zero])
  · exact hc σ h

/-- The negative of a chain supported in `N` is supported in `N`. -/
lemma IsSupportedIn.neg {P : TopCat.{u}} {n : ℕ} {N : Set P}
    {c : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M N c) :
    IsSupportedIn R M N (-c) := fun σ hσ ↦ hc σ fun h ↦ hσ (by rw [coe_neg_apply, h, neg_zero])

/-- A difference of chains supported in `N` is supported in `N`. -/
lemma IsSupportedIn.sub {P : TopCat.{u}} {n : ℕ} {N : Set P}
    {c d : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M N c)
    (hd : IsSupportedIn R M N d) : IsSupportedIn R M N (c - d) := by
  rw [sub_eq_add_neg]
  exact hc.add hd.neg

/-- The zero chain is supported in every set. -/
lemma isSupportedIn_zero {P : TopCat.{u}} {n : ℕ} {N : Set P} :
    IsSupportedIn R M N (0 : (borelMooreChainComplex R M P).X n) := fun _ h ↦ absurd rfl h

end support

section restrict

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {P : TopCat.{u}} [T2Space P]

/-- **Restriction of a chain supported in an open set.** If every simplex of `c` lies in the open
set `V`, the coefficient of a simplex `τ` of `V` in `c|_V` is that of `τ` in `c`. -/
lemma restrictChainMap_apply_of_isSupportedIn (V : TopologicalSpace.Opens P) {n : ℕ}
    {c : (borelMooreChainComplex R M P).X n} (hc : IsSupportedIn R M (V : Set P) c)
    (τ : (TopCat.toSSet.obj (TopCat.of V)).obj (op ⦋n⦌)) :
    (((restrictChainMap R M V).f n).hom c).1 τ =
      c.1 ((TopCat.toSSet.map (clopenInclusion V)).app _ τ) := by
  change kernelFun (restrictKernel V n) c.1 τ = _
  rw [kernelFun, finsum_eq_single _ ((TopCat.toSSet.map (clopenInclusion V)).app _ τ)]
  · rw [restrictKernel, toSSetObjEquiv_map_clopenInclusion,
      restrCoeff_of_range_subset (range_inclSimplex_subset V τ), Finsupp.single_eq_same,
      one_smul]
  · intro σ hσ
    by_cases h0 : c.1 σ = 0
    · rw [h0, smul_zero]
    rw [restrictKernel, restrCoeff_of_range_subset ((range_simplexEquiv σ).le.trans (hc σ h0)),
      Finsupp.single_eq_of_ne,
      zero_smul]
    refine fun he ↦ hσ ((SingularCochain.simplexEquiv P _).injective ?_)
    rw [toSSetObjEquiv_map_clopenInclusion]
    exact he.symm

/-- **Restriction of a chain missing an open set** is zero. -/
lemma restrictChainMap_eq_zero_of_disjoint (V : TopologicalSpace.Opens P) {n : ℕ}
    {c : (borelMooreChainComplex R M P).X n}
    (hc : ∀ σ, c.1 σ ≠ 0 → Disjoint (singularSimplexImage P σ) (V : Set P)) :
    ((restrictChainMap R M V).f n).hom c = 0 := by
  apply Subtype.ext
  funext τ
  change kernelFun (restrictKernel V n) c.1 τ = 0
  refine finsum_eq_zero_of_forall_eq_zero fun σ ↦ ?_
  by_cases h0 : c.1 σ = 0
  · rw [h0, smul_zero]
  rw [restrictKernel, restrCoeff_of_disjoint (Disjoint.mono_left (range_simplexEquiv σ).le (hc σ h0)),
    zero_smul]

end restrict

section prism

variable (P : TopCat.{u})

/-- The inclusion `x ↦ (t, x)` of `P` into the prism `[0, 1] × P`. -/
def prismIncl (t : unitInterval) : P ⟶ TopCat.of (unitInterval × P) :=
  TopCat.ofHom ⟨fun x ↦ (t, x), by fun_prop⟩

/-- The inclusion `x ↦ (t, x)` of `P` into `[0, 1] × P` is proper. -/
lemma isProperMap_prismIncl (t : unitInterval) : IsProperMap (prismIncl P t) := by
  refine Topology.IsClosedEmbedding.isProperMap ⟨isEmbedding_prodMkRight _, ?_⟩
  change IsClosed (Set.range (fun y : P ↦ (t, y)))
  rw [show Set.range (fun y : P ↦ (t, y)) = {t} ×ˢ Set.univ by ext ⟨s, y⟩; simp [eq_comm]]
  exact isClosed_singleton.prod isClosed_univ

/-- The identity of the prism, as a homotopy from `prismIncl P 0` to `prismIncl P 1`. -/
def prismHomotopy : TopCat.Homotopy (prismIncl P 0) (prismIncl P 1) where
  toFun p := p
  continuous_toFun := continuous_id
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The prism homotopy is proper. -/
lemma isProperMap_prismHomotopy : IsProperMap (prismHomotopy P) := isProperMap_id

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- The prism operator `C^lf_n(P) → C^lf_{n+1}([0, 1] × P)`, a chain homotopy between the
inclusions of the two ends. -/
def prism : Homotopy (chainMap R M (prismIncl P 0) (isProperMap_prismIncl P 0))
    (chainMap R M (prismIncl P 1) (isProperMap_prismIncl P 1)) :=
  chainMapHomotopy R M _ _ (prismHomotopy P) (isProperMap_prismHomotopy P)

end prism

section deform

variable {Y : TopCat.{u}} {X : Set Y} (hX : IsClosed X) (N : Set Y)
  (G : C(N × unitInterval, Y))

/-- The part `A = N - X` of `N` off `X`, as a subset of `U = Y - X`. -/
abbrev deformDomain : Set (TopCat.of (complOpens hX)) := Subtype.val ⁻¹' N

/-- The homotopy `G` on `[0, 1] × A`. -/
def deformMap : TopCat.of (unitInterval × deformDomain hX N) ⟶ Y :=
  TopCat.ofHom ⟨fun p ↦ G (⟨p.2.1.1, p.2.2⟩, p.1), by fun_prop⟩

/-- The open set `W = G⁻¹(U) ⊆ [0, 1] × A`. -/
abbrev deformOpens : TopologicalSpace.Opens (TopCat.of (unitInterval × deformDomain hX N)) :=
  TopologicalSpace.Opens.comap (deformMap hX N G).hom (complOpens hX)

/-- `G|_W : W → U`. -/
abbrev deformRestrict : TopCat.of (deformOpens hX N G) ⟶ TopCat.of (complOpens hX) :=
  restrictPreimage (deformMap hX N G) (complOpens hX)

variable {N G}

/-- If `G` fixes `X`, then `W = G⁻¹(U)` in `[0, 1] × A` is homeomorphic to `G⁻¹(U)` in
`N × [0, 1]`. -/
def deformOpensHomeomorph (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y) :
    deformOpens hX N G ≃ₜ (G ⁻¹' Xᶜ) where
  toFun w := ⟨(⟨w.1.2.1.1, w.1.2.2⟩, w.1.1), w.2⟩
  invFun q := ⟨(q.1.2, ⟨⟨q.1.1.1, fun hq ↦ q.2 (by rw [hGX _ _ hq]; exact hq)⟩, q.1.1.2⟩), q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- If `G` is proper and fixes `X`, then `G|_W : W → U` is proper. -/
lemma isProperMap_deformRestrict (hG : IsProperMap G)
    (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y) :
    IsProperMap (deformRestrict hX N G) := by
  have : (deformRestrict hX N G : deformOpens hX N G → complOpens hX) =
      (Xᶜ.restrictPreimage G) ∘ (deformOpensHomeomorph hX hGX) := rfl
  rw [this]
  exact (hG.restrictPreimage _).comp (deformOpensHomeomorph hX hGX).isProperMap

end deform

section homotopyApply

variable {R : Type u} [CommRing R] {C D : ChainComplex (ModuleCat.{u} R) ℕ} {φ ψ : C ⟶ D}

/-- For a chain homotopy `h` from `φ` to `ψ` and `c` in degree `k + 1`,
`φ c - ψ c = h (∂ c) + ∂ (h c)`. -/
lemma _root_.MMP.ChainHomotopyAux.apply_succ (h : Homotopy φ ψ) (k : ℕ) (c : C.X (k + 1)) :
    (φ.f (k + 1)).hom c - (ψ.f (k + 1)).hom c =
      (h.hom k (k + 1)).hom ((C.d (k + 1) k).hom c) +
        (D.d (k + 2) (k + 1)).hom ((h.hom (k + 1) (k + 2)).hom c) := by
  have e := congrArg (fun f ↦ f.hom c) (h.comm (k + 1))
  simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at e
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply] at e
  rw [e]
  abel

/-- For a chain homotopy `h` from `φ` to `ψ` and `c` in degree `0`, `φ c - ψ c = ∂ (h c)`. -/
lemma _root_.MMP.ChainHomotopyAux.apply_zero (h : Homotopy φ ψ) (c : C.X 0) :
    (φ.f 0).hom c - (ψ.f 0).hom c = (D.d 1 0).hom ((h.hom 0 1).hom c) := by
  have e := congrArg (fun f ↦ f.hom c) (h.comm 0)
  simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at e
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, zero_add] at e
  rw [e]
  simp

end homotopyApply

/-- For injective `ψ`, the coefficient of `ψ τ` in the pushforward along `ψ ∘ φ` is that of `τ`
in the pushforward along `φ`. -/
lemma pushforwardFun_comp_apply_of_injective {S S' T : Type*} {M : Type*} [AddCommGroup M]
    {φ : S → S'} {ψ : S' → T} (hψ : Function.Injective ψ) (c : S → M) (τ : S') :
    pushforwardFun (ψ ∘ φ) c (ψ τ) = pushforwardFun φ c τ := by
  classical
  simp only [pushforwardFun, Function.comp_apply, hψ.eq_iff]

section deformOp

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}} [T2Space Y]
  {X : Set Y} (hX : IsClosed X) {N : Set Y} {G : C(N × unitInterval, Y)} (hG : IsProperMap G)
  (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y)

/-- **The deformation operator** `H : C^lf_n(A) → C^lf_{n+1}(U)` on the part `A = N - X`:
the prism, restricted to `W = G⁻¹(U)`, pushed forward along `G|_W`. -/
def deformOp (n : ℕ) :
    (borelMooreChainComplex R M (TopCat.of (deformDomain hX N))).X n ⟶
      (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X (n + 1) :=
  (prism (TopCat.of (deformDomain hX N)) R M).hom n (n + 1) ≫
    (restrictChainMap R M (deformOpens hX N G)).f (n + 1) ≫
      (chainMap R M (deformRestrict hX N G) (isProperMap_deformRestrict hX hG hGX)).f (n + 1)

variable {hX}

/-- The end `{0} × A` of the prism, inside `W`. -/
def deformIncl₀ (hG0 : ∀ y, G (y, 0) = y) :
    TopCat.of (deformDomain hX N) ⟶ TopCat.of (deformOpens hX N G) :=
  TopCat.ofHom ⟨fun x ↦ ⟨(0, x), show G (⟨x.1.1, x.2⟩, 0) ∈ Xᶜ by rw [hG0]; exact x.1.2⟩,
    by fun_prop⟩

omit [T2Space Y] in
/-- The inclusion of the end `{0} × A` into `W` is proper. -/
lemma isProperMap_deformIncl₀ (hG0 : ∀ y, G (y, 0) = y) :
    IsProperMap (deformIncl₀ (hX := hX) hG0) :=
  isProperMap_of_comp_of_inj (deformIncl₀ hG0).hom.continuous continuous_subtype_val
    (isProperMap_prismIncl _ 0) Subtype.val_injective

variable (hX)

omit [T2Space Y] in
/-- For closed `N`, the inclusion `A = N - X → U` is proper. -/
lemma isProperMap_deformDomainInclusion (hN : IsClosed N) :
    IsProperMap (subsetInclusion (deformDomain hX N)) :=
  isProperMap_subsetInclusion (hN.preimage continuous_subtype_val)

variable {R M}

/-- If `G(·, 1)` maps into `X`, a chain on the end `{1} × A` restricts to zero on `W`. -/
lemma restrictChainMap_chainMap_prismIncl_one (hG1 : ∀ y, G (y, 1) ∈ X) {n : ℕ}
    (c : (borelMooreChainComplex R M (TopCat.of (deformDomain hX N))).X n) :
    ((restrictChainMap R M (deformOpens hX N G)).f n).hom
      (((chainMap R M (prismIncl _ 1) (isProperMap_prismIncl _ 1)).f n).hom c) = 0 := by
  refine restrictChainMap_eq_zero_of_disjoint R M _ fun σ hσ ↦ ?_
  change pushforwardFun ((TopCat.toSSet.map (prismIncl _ 1)).app _) c.1 σ ≠ 0 at hσ
  obtain ⟨σ', -, rfl⟩ := support_pushforwardFun_subset _ c.1 hσ
  rw [singularSimplexImage_map]
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨x, -, rfl⟩ hx
  exact hx (hG1 _)

/-- If `G(·, 0)` is the identity, a chain on the end `{0} × A` restricted to `W` is its
pushforward along `deformIncl₀`. -/
lemma restrictChainMap_chainMap_prismIncl_zero (hG0 : ∀ y, G (y, 0) = y) {n : ℕ}
    (c : (borelMooreChainComplex R M (TopCat.of (deformDomain hX N))).X n) :
    ((restrictChainMap R M (deformOpens hX N G)).f n).hom
      (((chainMap R M (prismIncl _ 0) (isProperMap_prismIncl _ 0)).f n).hom c) =
      ((chainMap R M (deformIncl₀ hG0) (isProperMap_deformIncl₀ hG0)).f n).hom c := by
  have hsupp : IsSupportedIn R M ((deformOpens hX N G : Set _))
      (((chainMap R M (prismIncl _ 0) (isProperMap_prismIncl _ 0)).f n).hom c) := by
    intro σ hσ
    change pushforwardFun ((TopCat.toSSet.map (prismIncl _ 0)).app _) c.1 σ ≠ 0 at hσ
    obtain ⟨σ', -, rfl⟩ := support_pushforwardFun_subset _ c.1 hσ
    rw [singularSimplexImage_map]
    rintro _ ⟨x, -, rfl⟩
    exact (deformIncl₀ hG0 x).2
  apply Subtype.ext
  funext τ
  rw [restrictChainMap_apply_of_isSupportedIn R M _ hsupp]
  change pushforwardFun ((TopCat.toSSet.map (prismIncl _ 0)).app _) c.1 _ =
    pushforwardFun ((TopCat.toSSet.map (deformIncl₀ hG0)).app _) c.1 τ
  have e : prismIncl (TopCat.of (deformDomain hX N)) 0 =
      deformIncl₀ hG0 ≫ clopenInclusion (deformOpens hX N G) := rfl
  have e' : ⇑(ConcreteCategory.hom ((TopCat.toSSet.map (prismIncl _ 0)).app (op ⦋n⦌))) =
      ⇑(ConcreteCategory.hom ((TopCat.toSSet.map (clopenInclusion (deformOpens hX N G))).app
        (op ⦋n⦌))) ∘
        ⇑(ConcreteCategory.hom ((TopCat.toSSet.map (deformIncl₀ hG0)).app (op ⦋n⦌))) := by
    rw [e, Functor.map_comp]
    rfl
  rw [e', pushforwardFun_comp_apply_of_injective (map_clopenInclusion_injective _ n)]

variable (R M)

omit [T2Space Y] in
/-- If `G(·, 0)` is the identity, `G|_W` on the end `{0} × A` is the inclusion `A → U`. -/
lemma deformIncl₀_comp_deformRestrict (hG0 : ∀ y, G (y, 0) = y) :
    deformIncl₀ (hX := hX) hG0 ≫ deformRestrict hX N G = subsetInclusion (deformDomain hX N) := by
  ext x
  exact hG0 _

/-- **The deformation operator is a null-homotopy of the inclusion `ι : A → U`**, in positive
degrees: `ι_* c = ∂ H c + H ∂ c`. -/
theorem chainMap_deformDomain_eq_succ (hN : IsClosed N) (hG0 : ∀ y, G (y, 0) = y)
    (hG1 : ∀ y, G (y, 1) ∈ X) (k : ℕ)
    (c : (borelMooreChainComplex R M (TopCat.of (deformDomain hX N))).X (k + 1)) :
    ((chainMap R M (subsetInclusion (deformDomain hX N))
        (isProperMap_deformDomainInclusion hX hN)).f (k + 1)).hom c =
      ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (k + 2) (k + 1)).hom
          ((deformOp R M hX hG hGX (k + 1)).hom c) +
        (deformOp R M hX hG hGX k).hom
          (((borelMooreChainComplex R M (TopCat.of (deformDomain hX N))).d (k + 1) k).hom c) := by
  set L := (restrictChainMap R M (deformOpens hX N G)) ≫
    chainMap R M (deformRestrict hX N G) (isProperMap_deformRestrict hX hG hGX)
  have e := congrArg (L.f (k + 1)).hom
    (MMP.ChainHomotopyAux.apply_succ (prism (TopCat.of (deformDomain hX N)) R M) k c)
  rw [map_sub, map_add] at e
  have h0 : (L.f (k + 1)).hom (((chainMap R M (prismIncl _ 0) (isProperMap_prismIncl _ 0)).f
      (k + 1)).hom c) = ((chainMap R M (subsetInclusion (deformDomain hX N))
        (isProperMap_deformDomainInclusion hX hN)).f (k + 1)).hom c := by
    simp only [L, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [restrictChainMap_chainMap_prismIncl_zero hX hG0, ← LinearMap.comp_apply,
      ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, ← chainMap_comp]
    simp only [deformIncl₀_comp_deformRestrict hX hG0]
  have h1 : (L.f (k + 1)).hom (((chainMap R M (prismIncl _ 1) (isProperMap_prismIncl _ 1)).f
      (k + 1)).hom c) = 0 := by
    simp only [L, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [restrictChainMap_chainMap_prismIncl_one hX hG1, map_zero]
  have hd : (L.f (k + 1)).hom (((borelMooreChainComplex R M _).d (k + 2) (k + 1)).hom
      (((prism (TopCat.of (deformDomain hX N)) R M).hom (k + 1) (k + 2)).hom c)) =
      ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (k + 2) (k + 1)).hom
          ((deformOp R M hX hG hGX (k + 1)).hom c) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← L.comm]
    rfl
  rw [h0, h1, sub_zero, hd] at e
  rw [e]
  exact add_comm _ _

/-- `ι_* c = ∂ H c` in degree `0`. -/
theorem chainMap_deformDomain_eq_zero (hN : IsClosed N) (hG0 : ∀ y, G (y, 0) = y)
    (hG1 : ∀ y, G (y, 1) ∈ X)
    (c : (borelMooreChainComplex R M (TopCat.of (deformDomain hX N))).X 0) :
    ((chainMap R M (subsetInclusion (deformDomain hX N))
        (isProperMap_deformDomainInclusion hX hN)).f 0).hom c =
      ((borelMooreChainComplex R M (TopCat.of (complOpens hX))).d 1 0).hom
          ((deformOp R M hX hG hGX 0).hom c) := by
  set L := (restrictChainMap R M (deformOpens hX N G)) ≫
    chainMap R M (deformRestrict hX N G) (isProperMap_deformRestrict hX hG hGX)
  have e := congrArg (L.f 0).hom
    (MMP.ChainHomotopyAux.apply_zero (prism (TopCat.of (deformDomain hX N)) R M) c)
  rw [map_sub] at e
  have h0 : (L.f 0).hom (((chainMap R M (prismIncl _ 0) (isProperMap_prismIncl _ 0)).f
      0).hom c) = ((chainMap R M (subsetInclusion (deformDomain hX N))
        (isProperMap_deformDomainInclusion hX hN)).f 0).hom c := by
    simp only [L, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [restrictChainMap_chainMap_prismIncl_zero hX hG0, ← LinearMap.comp_apply,
      ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, ← chainMap_comp]
    simp only [deformIncl₀_comp_deformRestrict hX hG0]
  have h1 : (L.f 0).hom (((chainMap R M (prismIncl _ 1) (isProperMap_prismIncl _ 1)).f
      0).hom c) = 0 := by
    simp only [L, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [restrictChainMap_chainMap_prismIncl_one hX hG1, map_zero]
  rw [h0, h1, sub_zero, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← L.comm] at e
  exact e

end deformOp

section fill

variable {Y : TopCat.{u}} {X : Set Y} (hX : IsClosed X) {N : Set Y}
  {G : C(N × unitInterval, Y)} (hG : IsProperMap G) {B : Set Y} (hB : IsClosed B) (hBN : B ⊆ N)
  (hBX : B ⊆ Xᶜ)

/-- The inclusion of `B ⊆ N - X` into `A = N - X`. -/
def fillIncl : TopCat.of B ⟶ TopCat.of (deformDomain hX N) :=
  TopCat.ofHom ⟨fun y ↦ ⟨⟨y.1, hBX y.2⟩, hBN y.2⟩, by fun_prop⟩

include hB in
/-- For closed `B`, the inclusion `B → A` is proper. -/
lemma isProperMap_fillIncl : IsProperMap (fillIncl hX hBN hBX) :=
  isProperMap_of_comp_of_inj (fillIncl hX hBN hBX).hom.continuous
    (continuous_subtype_val.comp continuous_subtype_val) (isProperMap_subsetInclusion hB)
    (Subtype.val_injective.comp Subtype.val_injective)

/-- `1 × ι : [0, 1] × B → [0, 1] × A`. -/
def fillPrismIncl :
    TopCat.of (unitInterval × B) ⟶ TopCat.of (unitInterval × deformDomain hX N) :=
  TopCat.ofHom ((ContinuousMap.id _).prodMap (fillIncl hX hBN hBX).hom)

include hB in
/-- For closed `B`, the map `1 × ι : [0, 1] × B → [0, 1] × A` is proper. -/
lemma isProperMap_fillPrismIncl : IsProperMap (fillPrismIncl hX hBN hBX) :=
  isProperMap_id.prodMap (isProperMap_fillIncl hX hB hBN hBX)

/-- The prism of `B`, pushed into the prism of `A`. -/
def fillPrismHomotopy : TopCat.Homotopy (fillIncl hX hBN hBX ≫ prismIncl _ 0)
    (fillIncl hX hBN hBX ≫ prismIncl _ 1) where
  toFun p := (p.1, fillIncl hX hBN hBX p.2)
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

include hB in
/-- For closed `B`, the prism of `B` pushed into the prism of `A` is a proper homotopy. -/
lemma isProperMap_fillPrismHomotopy : IsProperMap (fillPrismHomotopy hX hBN hBX) :=
  isProperMap_fillPrismIncl hX hB hBN hBX

variable (G) in
/-- `G` on `[0, 1] × B`. -/
abbrev fillMap : TopCat.of (unitInterval × B) ⟶ Y := fillPrismIncl hX hBN hBX ≫ deformMap hX N G

/-- The end `G(·, 1) : B → X`. -/
def fillEnd (hG1 : ∀ y, G (y, 1) ∈ X) : TopCat.of B ⟶ TopCat.of X :=
  TopCat.ofHom ⟨fun y ↦ ⟨G (⟨y.1, hBN y.2⟩, 1), hG1 _⟩, by fun_prop⟩

/-- `G|_B` as a homotopy from the inclusion of `B` to `B → X → Y`. -/
def fillHomotopy (hG0 : ∀ y, G (y, 0) = y) (hG1 : ∀ y, G (y, 1) ∈ X) :
    TopCat.Homotopy (subsetInclusion B) (fillEnd hBN hG1 ≫ subspaceInclusion Y X) where
  toFun p := G (⟨p.2.1, hBN p.2.2⟩, p.1)
  continuous_toFun := by fun_prop
  map_zero_left y := hG0 _
  map_one_left _ := rfl

include hG hB in
/-- For proper `G` and closed `B`, the map `(t, y) ↦ G (y, t)` on `[0, 1] × B` is proper. -/
lemma isProperMap_fillFun :
    IsProperMap (fun p : unitInterval × B ↦ G (⟨p.2.1, hBN p.2.2⟩, p.1)) := by
  have hι : IsProperMap (fun y : B ↦ (⟨y.1, hBN y.2⟩ : N)) :=
    isProperMap_of_comp_of_inj (by fun_prop) continuous_subtype_val
      (isProperMap_subsetInclusion hB) Subtype.val_injective
  exact hG.comp ((Homeomorph.prodComm _ _).isProperMap.comp (isProperMap_id.prodMap hι))

include hG hB in
/-- For proper `G` and closed `B`, `G` on `[0, 1] × B` is proper. -/
lemma isProperMap_fillMap : IsProperMap (fillMap hX G hBN hBX) :=
  isProperMap_fillFun hG hB hBN

include hG hB in
/-- For proper `G` and closed `B`, the homotopy `G|_B` is proper. -/
lemma isProperMap_fillHomotopy (hG0 : ∀ y, G (y, 0) = y) (hG1 : ∀ y, G (y, 1) ∈ X) :
    IsProperMap (fillHomotopy hBN hG0 hG1) :=
  isProperMap_fillFun hG hB hBN

include hG hB in
/-- For proper `G` and closed `B`, the end `G(·, 1) : B → X` is proper. -/
lemma isProperMap_fillEnd (hG0 : ∀ y, G (y, 0) = y) (hG1 : ∀ y, G (y, 1) ∈ X) :
    IsProperMap (fillEnd hBN hG1) :=
  isProperMap_of_comp_of_inj (fillEnd hBN hG1).hom.continuous continuous_subtype_val
    (isProperMap_of_properHomotopy_right _ (isProperMap_fillHomotopy hG hB hBN hG0 hG1))
    Subtype.val_injective

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) [T2Space Y]

/-- The chain homotopy `h_B` of `G|_B`, from the inclusion of `B` to `B → X → Y`. -/
def fillChainHomotopy (hG0 : ∀ y, G (y, 0) = y) (hG1 : ∀ y, G (y, 1) ∈ X) :
    Homotopy (chainMap R M (subsetInclusion B) (isProperMap_subsetInclusion hB))
      (chainMap R M (fillEnd hBN hG1 ≫ subspaceInclusion Y X)
        (isProperMap_of_properHomotopy_right _ (isProperMap_fillHomotopy hG hB hBN hG0 hG1))) :=
  chainMapHomotopy R M _ _ (fillHomotopy hBN hG0 hG1) (isProperMap_fillHomotopy hG hB hBN hG0 hG1)

/-- The deformation operator on the image of a chain of `B` factors through the prism of `B`
followed by the restricted pushforward along the prism inclusion. -/
theorem deformOp_chainMap_fillIncl (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y) (n : ℕ)
    (β : (borelMooreChainComplex R M (TopCat.of B)).X n) :
    (deformOp R M hX hG hGX n).hom
        (((chainMap R M (fillIncl hX hBN hBX) (isProperMap_fillIncl hX hB hBN hBX)).f n).hom β) =
      ((chainMap R M (deformRestrict hX N G) (isProperMap_deformRestrict hX hG hGX)).f
        (n + 1)).hom (((chainMap R M _ (isProperMap_restrictPreimage _ (deformOpens hX N G)
          (isProperMap_fillPrismIncl hX hB hBN hBX))).f (n + 1)).hom
        (((restrictChainMap R M (TopologicalSpace.Opens.comap (fillPrismIncl hX hBN hBX).hom
          (deformOpens hX N G))).f (n + 1)).hom
            (((prism (TopCat.of B) R M).hom n (n + 1)).hom β))) := by
  have hp0 := isProperMap_prismIncl (TopCat.of B) 0
  have hp1 := isProperMap_prismIncl (TopCat.of B) 1
  have hr0 := isProperMap_of_properHomotopy_left _ (isProperMap_fillPrismHomotopy hX hB hBN hBX)
  have hr1 := isProperMap_of_properHomotopy_right _ (isProperMap_fillPrismHomotopy hX hB hBN hBX)
  have n2 := chainMapHomotopy_hom_natural R M (isProperMap_prismIncl _ 0)
    (isProperMap_prismIncl _ 1) hr0 hr1 (prismHomotopy (TopCat.of (deformDomain hX N)))
    (isProperMap_prismHomotopy _) (fillPrismHomotopy hX hBN hBX)
    (isProperMap_fillPrismHomotopy hX hB hBN hBX) (isProperMap_fillIncl hX hB hBN hBX)
    (b := 𝟙 _) (by simp [isProperMap_id]) (fun _ ↦ rfl) n (n + 1)
  have n3 := chainMapHomotopy_hom_natural R M hp0 hp1 hr0 hr1 (prismHomotopy (TopCat.of B))
    (isProperMap_prismHomotopy _) (fillPrismHomotopy hX hBN hBX)
    (isProperMap_fillPrismHomotopy hX hB hBN hBX) (a := 𝟙 _) (by simp [isProperMap_id])
    (isProperMap_fillPrismIncl hX hB hBN hBX) (fun _ ↦ rfl) n (n + 1)
  rw [chainMap_id, HomologicalComplex.id_f, Category.id_comp] at n3
  rw [chainMap_id, HomologicalComplex.id_f, Category.comp_id] at n2
  set x := ((prism (TopCat.of B) R M).hom n (n + 1)).hom β
  have e := congrArg (fun φ ↦ (φ.f (n + 1)).hom x)
    (chainMap_comp_restrictChainMap R M _ (isProperMap_fillPrismIncl hX hB hBN hBX)
      (deformOpens hX N G))
  have e2 : ((prism (TopCat.of (deformDomain hX N)) R M).hom n (n + 1)).hom
      (((chainMap R M (fillIncl hX hBN hBX) (isProperMap_fillIncl hX hB hBN hBX)).f n).hom β) =
      ((chainMap R M _ (isProperMap_fillPrismIncl hX hB hBN hBX)).f (n + 1)).hom x :=
    congrArg (fun φ ↦ φ.hom β) (n2.trans n3.symm)
  change ((chainMap R M (deformRestrict hX N G) (isProperMap_deformRestrict hX hG hGX)).f
    (n + 1)).hom (((restrictChainMap R M (deformOpens hX N G)).f (n + 1)).hom
      (((prism (TopCat.of (deformDomain hX N)) R M).hom n (n + 1)).hom
        (((chainMap R M (fillIncl hX hBN hBX) (isProperMap_fillIncl hX hB hBN hBX)).f n).hom β)))
            = _
  rw [e2]
  exact congrArg _ e

/-- **The chain homotopy of `G|_B` restricts to the deformation operator**:
`(h_B β)|_U = H (β|_A)` for a locally finite chain `β` of a closed set `B ⊆ N - X`. -/
theorem restrictChainMap_fillChainHomotopy (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y)
    (hG0 : ∀ y, G (y, 0) = y) (hG1 : ∀ y, G (y, 1) ∈ X) (n : ℕ)
    (β : (borelMooreChainComplex R M (TopCat.of B)).X n) :
    ((restrictChainMap R M (complOpens hX)).f (n + 1)).hom
        (((fillChainHomotopy hG hB hBN R M hG0 hG1).hom n (n + 1)).hom β) =
      (deformOp R M hX hG hGX n).hom
        (((chainMap R M (fillIncl hX hBN hBX) (isProperMap_fillIncl hX hB hBN hBX)).f n).hom
          β) := by
  have n1 := chainMapHomotopy_hom_natural R M (isProperMap_prismIncl _ 0)
    (isProperMap_prismIncl _ 1) (isProperMap_subsetInclusion hB)
    (isProperMap_of_properHomotopy_right _ (isProperMap_fillHomotopy hG hB hBN hG0 hG1))
    (prismHomotopy (TopCat.of B))
    (isProperMap_prismHomotopy _) (fillHomotopy hBN hG0 hG1)
    (isProperMap_fillHomotopy hG hB hBN hG0 hG1) (a := 𝟙 _) (by simp [isProperMap_id])
    (b := fillMap hX G hBN hBX) (isProperMap_fillMap hX hG hB hBN hBX) (fun _ ↦ rfl) n (n + 1)
  rw [chainMap_id, HomologicalComplex.id_f, Category.id_comp] at n1
  set x := ((prism (TopCat.of B) R M).hom n (n + 1)).hom β
  have hL : ((restrictChainMap R M (complOpens hX)).f (n + 1)).hom
      (((fillChainHomotopy hG hB hBN R M hG0 hG1).hom n (n + 1)).hom β) =
      ((chainMap R M _ (isProperMap_restrictPreimage _ (complOpens hX)
        (isProperMap_fillMap hX hG hB hBN hBX))).f (n + 1)).hom
        (((restrictChainMap R M (TopologicalSpace.Opens.comap (fillMap hX G hBN hBX).hom
          (complOpens hX))).f (n + 1)).hom x) :=
    (congrArg ((restrictChainMap R M (complOpens hX)).f (n + 1)).hom
      (congrArg (fun φ ↦ φ.hom β) n1)).symm.trans <| congrArg (fun φ ↦ (φ.f (n + 1)).hom x)
        (chainMap_comp_restrictChainMap R M _ (isProperMap_fillMap hX hG hB hBN hBX)
          (complOpens hX))
  rw [hL, deformOp_chainMap_fillIncl hX hG hB]
  exact congrArg (fun φ ↦ (φ.f (n + 1)).hom
      (((restrictChainMap R M (TopologicalSpace.Opens.comap (fillPrismIncl hX hBN hBX).hom
          (deformOpens hX N G))).f (n + 1)).hom x))
    (chainMap_comp R M _ _ (isProperMap_restrictPreimage _ (deformOpens hX N G)
      (isProperMap_fillPrismIncl hX hB hBN hBX)) (isProperMap_deformRestrict hX hG hGX))

end fill

end borelMooreHomology

end MMP
