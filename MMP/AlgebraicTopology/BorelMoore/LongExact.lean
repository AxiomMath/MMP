module

public import MMP.AlgebraicTopology.BorelMoore.Restriction
public import MMP.AlgebraicTopology.BorelMoore.Pushforward
public import MMP.AlgebraicTopology.BorelMoore.DisjointUnion
public import MMP.AlgebraicTopology.SingularCohomology.Relative
public import MMP.AlgebraicTopology.BorelMoore.LongExactCriterion
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# The long exact sequence of Borel–Moore homology: the algebraic reduction (Fulton, §19.1)

Let `Y` be a Hausdorff space, `X ⊆ Y` a closed subset with inclusion `i`, and `U = Y - X` with
inclusion `j`. On locally finite chains, `i_*` is injective and `j^* ∘ i_* = 0` (a simplex
inside `X` has no piece inside `U`). The short exact sequence of complexes
`0 → C^lf(X) → C^lf(Y) → C^lf(Y) / C^lf(X) → 0` gives a long exact homology sequence; the
restriction factors through the quotient, and **once the induced map
`C^lf(Y) / C^lf(X) → C^lf(U)` is a quasi-isomorphism**, the long exact sequence
`⋯ → H_{k+1} U → H_k X → H_k Y → H_k U → H_{k-1} X → ⋯` follows.

## Main definitions

* `MMP.borelMooreHomology.IsRelativeQuasiIso`: the restriction from the quotient
  `C^lf(Y) / C^lf(X)` to `C^lf(Y - X)` is a quasi-isomorphism.

## Main results

* `MMP.ModuleCatComplex.exists_exact_of_quasiIso_cokernelDesc`: the long exact sequence of a
  monomorphism `f` and a map `g` with `f ≫ g = 0` inducing a quasi-isomorphism on `coker f`.
* `MMP.borelMooreHomology.chainMap_subspaceInclusion_comp_restrictChainMap`:
  `j^* ∘ i_* = 0` on chains.
* `MMP.borelMooreHomology.isRelativeQuasiIso_of_forall`: the relative
  quasi-isomorphism from its two chain-level halves (S) and (I).
* `MMP.borelMooreHomology.exists_longExact_of_isRelativeQuasiIso`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, (3) and (5).
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Simplicial Topology

universe u

namespace MMP.ModuleCatComplex

open _root_.HomologicalComplex

/-- **The long exact sequence of a monomorphism with a quasi-isomorphic cokernel.** For a
monomorphism `f : A ⟶ B` of `ℤ`-graded complexes of modules and `g : B ⟶ D` with `f ≫ g = 0`
whose induced map `coker f ⟶ D` is a quasi-isomorphism, there are connecting maps
`δ : H^i D → H^j A` (`j = i + 1`) making `⋯ → H^i A → H^i B → H^i D → H^{i+1} A → ⋯` exact. -/
theorem exists_exact_of_quasiIso_cokernelDesc {R : Type u} [CommRing R]
    {A B D : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.up ℤ)}
    (f : A ⟶ B) (g : B ⟶ D) [Mono f] (w : f ≫ g = 0) [QuasiIso (cokernel.desc f g w)] :
    ∃ δ : ∀ i j : ℤ, i + 1 = j → (D.homology i ⟶ A.homology j),
      (∀ i j h, Function.Exact (δ i j h).hom (homologyMap f j).hom) ∧
      (∀ i, Function.Exact (homologyMap f i).hom (homologyMap g i).hom) ∧
      (∀ i j h, Function.Exact (homologyMap g i).hom (δ i j h).hom) := by
  let S : ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  set φ := cokernel.desc f g w
  have hφ : cokernel.π f ≫ φ = g := cokernel.π_desc f g w
  have hg : ∀ i, homologyMap g i = homologyMap (cokernel.π f) i ≫ homologyMap φ i :=
    fun i ↦ by rw [← homologyMap_comp, hφ]
  let e : ∀ i, (cokernel f).homology i ≅ D.homology i := fun i ↦ asIso (homologyMap φ i)
  have ex : ∀ {S' : ShortComplex (ModuleCat.{u} R)}, S'.Exact → Function.Exact S'.f.hom S'.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
  have hinv : ∀ i x, (e i).inv.hom ((e i).hom.hom x) = x := fun i x ↦ by
    rw [← ModuleCat.comp_apply, Iso.hom_inv_id]; rfl
  have hinv' : ∀ i x, (e i).hom.hom ((e i).inv.hom x) = x := fun i x ↦ by
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id]; rfl
  refine ⟨fun i j h ↦ (e i).inv ≫ hS.δ i j h, fun i j h ↦ ?_, fun i ↦ ?_, fun i j h ↦ ?_⟩
  · intro y
    refine (ex (hS.homology_exact₁ i j h) y).trans ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(e i).hom.hom x, by simp only [ModuleCat.hom_comp, LinearMap.coe_comp,
        Function.comp_apply, hinv]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  · rw [hg i, ModuleCat.hom_comp, LinearMap.coe_comp]
    exact (ex (hS.homology_exact₂ i)).comp_injective _ (Function.LeftInverse.injective (hinv i))
      (map_zero _)
  · intro y
    refine (ex (hS.homology_exact₃ i j h) ((e i).inv.hom y)).trans ⟨?_, ?_⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [hg i, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
      change (e i).hom.hom _ = y
      rw [show (homologyMap S.g i).hom x = _ from hx, hinv']
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      rw [hg i, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
      exact (hinv i _).symm

end MMP.ModuleCatComplex

namespace MMP

namespace borelMooreHomology

open LocallyFiniteChain

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}}

/-- The inclusion of a closed subset is a proper map. -/
lemma isProperMap_subspaceInclusion {X : Set Y} (hX : IsClosed X) :
    IsProperMap (subspaceInclusion Y X) :=
  hX.isClosedEmbedding_subtypeVal.isProperMap

/-- The complement `Y - X` of a closed subset, as an open subset. -/
def complOpens {X : Set Y} (hX : IsClosed X) : TopologicalSpace.Opens Y :=
  ⟨Xᶜ, hX.isOpen_compl⟩

/-- The inclusion of a subspace induces an injective map on singular simplices in each degree. -/
lemma injective_toSSet_map_subspaceInclusion (X : Set Y) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((TopCat.toSSet.map (subspaceInclusion Y X)).app n) := by
  have : Mono (subspaceInclusion Y X) :=
    (TopCat.mono_iff_injective _).2 Subtype.val_injective
  exact (mono_iff_injective _).1 inferInstance

/-- The push-forward `i_*` of locally finite chains along the inclusion of a closed subset is
injective in each degree. -/
lemma chainMap_subspaceInclusion_f_injective {X : Set Y} (hX : IsClosed X) (n : ℕ) :
    Function.Injective
      ((chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f n).hom := by
  intro c d h
  have h' := congrArg Subtype.val h
  apply Subtype.ext
  funext σ
  have := congrFun h' ((TopCat.toSSet.map (subspaceInclusion Y X)).app (op ⦋n⦌) σ)
  change pushforwardFun _ c.1 _ = pushforwardFun _ d.1 _ at this
  rwa [pushforwardFun_apply_of_injective (injective_toSSet_map_subspaceInclusion X _),
    pushforwardFun_apply_of_injective (injective_toSSet_map_subspaceInclusion X _)] at this

/-- The push-forward chain map `i_*` along the inclusion of a closed subset is a monomorphism. -/
instance mono_chainMap_subspaceInclusion {X : Set Y} (hX : IsClosed X) :
    Mono (chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)) :=
  HomologicalComplex.mono_of_mono_f _ fun n ↦
    (ModuleCat.mono_iff_injective _).2 (chainMap_subspaceInclusion_f_injective R M hX n)

variable [T2Space Y]

/-- **Restriction kills chains of the closed complement** (`j^* ∘ i_* = 0` on locally finite
chains): a simplex inside `X` has no piece inside `U = Y - X`. -/
lemma chainMap_subspaceInclusion_comp_restrictChainMap {X : Set Y} (hX : IsClosed X) :
    chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX) ≫
      restrictChainMap R M (complOpens hX) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  ext c : 2
  apply Subtype.ext
  funext τ
  change kernelFun (restrictKernel (complOpens hX) n) (pushforwardFun _ c.1) τ = 0
  refine finsum_eq_zero_of_forall_eq_zero fun σ ↦ ?_
  by_cases hk : restrictKernel (complOpens hX) n σ τ = 0
  · simp [hk]
  by_cases hc :
      pushforwardFun ((TopCat.toSSet.map (subspaceInclusion Y X)).app (op ⦋n⦌)) c.1 σ = 0
  · simp [hc]
  exfalso
  obtain ⟨σ', -, rfl⟩ := support_pushforwardFun_subset _ c.1 hc
  have hsub := (isAdmissibleKernel_restrictKernel (complOpens hX) n).image_subset _ τ hk
  rw [singularSimplexImage_map] at hsub
  obtain ⟨x, hx⟩ := nonempty_singularSimplexImage τ
  obtain ⟨y, -, hy⟩ := hsub ⟨x, hx, rfl⟩
  exact x.2 (hy ▸ y.2)

/-- The extended `ℤ`-graded push-forward chain map `i_*`. -/
abbrev extIncl {X : Set Y} (hX : IsClosed X) :=
  HomologicalComplex.extendMap
    (chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX))
    ComplexShape.embeddingDownNat

/-- The extended restriction chain map `j^*`. -/
abbrev extRestrict {X : Set Y} (hX : IsClosed X) :=
  HomologicalComplex.extendMap (restrictChainMap R M (complOpens hX)) ComplexShape.embeddingDownNat

/-- The extended push-forward chain map `i_*` is a monomorphism. -/
instance mono_extIncl {X : Set Y} (hX : IsClosed X) : Mono (extIncl R M hX) := by
  refine HomologicalComplex.mono_of_mono_f _ fun i ↦ ?_
  by_cases h : ∃ n, ComplexShape.embeddingDownNat.f n = i
  · obtain ⟨n, hn⟩ := h
    rw [HomologicalComplex.extendMap_f _ _ hn]
    have : Mono
        ((chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f n) :=
      (ModuleCat.mono_iff_injective _).2 (chainMap_subspaceInclusion_f_injective R M hX n)
    infer_instance
  · exact (HomologicalComplex.isZero_extend_X _ _ _ fun n hn ↦ h ⟨n, hn⟩).mono _

/-- On the extended `ℤ`-graded complexes, `j^* ∘ i_* = 0`. -/
lemma extIncl_comp_extRestrict {X : Set Y} (hX : IsClosed X) :
    extIncl R M hX ≫ extRestrict R M hX = 0 := by
  rw [← HomologicalComplex.extendMap_comp, chainMap_subspaceInclusion_comp_restrictChainMap]
  exact HomologicalComplex.extendMap_zero _ _ _

/-- The restriction `C^lf(Y) / C^lf(X) → C^lf(Y - X)` from the quotient by the chains of the
closed subset `X` is a quasi-isomorphism. This is the topological input of the Borel–Moore long
exact sequence; it fails for arbitrary closed subsets (the Warsaw circle in `ℝ²`). -/
def IsRelativeQuasiIso {X : Set Y} (hX : IsClosed X) : Prop :=
  QuasiIso
    (cokernel.desc (extIncl R M hX) (extRestrict R M hX) (extIncl_comp_extRestrict R M hX))

/-- **The relative quasi-isomorphism from its two chain-level halves.** `IsRelativeQuasiIso X`
holds once, in every degree `n`:
(S) every locally finite cycle `z` of `U = Y - X` is, up to a boundary of `U`, the restriction of
a locally finite chain `b` of `Y` whose boundary is a chain of `X`;
(I) a locally finite chain `b` of `Y` with boundary a chain of `X` whose restriction to `U` is a
boundary of `U` is a boundary of `Y` up to a chain of `X`. -/
theorem isRelativeQuasiIso_of_forall {X : Set Y} (hX : IsClosed X)
    (hS : ∀ n (z : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X n),
      (∀ m, m + 1 = n → (borelMooreChainComplex R M (TopCat.of (complOpens hX))).d n m z = 0) →
      ∃ b : (borelMooreChainComplex R M Y).X n,
        (∀ m, m + 1 = n → ∃ a : (borelMooreChainComplex R M (TopCat.of X)).X m,
          (borelMooreChainComplex R M Y).d n m b =
            (chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f m a) ∧
        ∃ e : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X (n + 1),
          (restrictChainMap R M (complOpens hX)).f n b - z =
            (borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (n + 1) n e)
    (hI : ∀ n (b : (borelMooreChainComplex R M Y).X n),
      (∀ m, m + 1 = n → ∃ a : (borelMooreChainComplex R M (TopCat.of X)).X m,
          (borelMooreChainComplex R M Y).d n m b =
            (chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f m a) →
      ∀ e : (borelMooreChainComplex R M (TopCat.of (complOpens hX))).X (n + 1),
        (restrictChainMap R M (complOpens hX)).f n b =
          (borelMooreChainComplex R M (TopCat.of (complOpens hX))).d (n + 1) n e →
      ∃ b' : (borelMooreChainComplex R M Y).X (n + 1),
        ∃ a' : (borelMooreChainComplex R M (TopCat.of X)).X n,
          b = (borelMooreChainComplex R M Y).d (n + 1) n b' +
            (chainMap R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX)).f n a') :
    IsRelativeQuasiIso R M hX := by
  have := mono_extIncl R M hX
  exact MMP.ModuleCatComplex.quasiIso_cokernelDesc_extendMap_of_forall _ _ _ hS hI

/-- **The Borel–Moore long exact sequence, from the relative quasi-isomorphism** (Fulton, §19.1,
(3)): for a closed subset `X` of a Hausdorff space `Y` with `U = Y - X` and
`IsRelativeQuasiIso X`, there are maps `∂ : H_{k+1} U → H_k X` making
`⋯ → H_{k+1} U → H_k X → H_k Y → H_k U → H_{k-1} X → ⋯` exact. -/
theorem exists_longExact_of_isRelativeQuasiIso {X : Set Y} (hX : IsClosed X)
    (h : IsRelativeQuasiIso R M hX) :
    ∃ δ : ∀ k : ℤ, borelMooreHomology R M (TopCat.of (complOpens hX)) (k + 1) ⟶
        borelMooreHomology R M (TopCat.of X) k,
      (∀ k, Function.Exact (δ k).hom
        (pushforward R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX) k).hom) ∧
      (∀ k, Function.Exact
        (pushforward R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX) k).hom
        (restrict R M (complOpens hX) k).hom) ∧
      (∀ k, Function.Exact (restrict R M (complOpens hX) (k + 1)).hom (δ k).hom) := by
  have : QuasiIso _ := h
  obtain ⟨δ, h1, h2, h3⟩ := MMP.ModuleCatComplex.exists_exact_of_quasiIso_cokernelDesc
    (extIncl R M hX) (extRestrict R M hX) (extIncl_comp_extRestrict R M hX)
  have hk : ∀ k : ℤ, -(k + 1) + 1 = -k := fun k ↦ by ring
  exact ⟨fun k ↦ δ (-(k + 1)) (-k) (hk k), fun k ↦ h1 _ _ (hk k), fun k ↦ h2 (-k),
    fun k ↦ h3 _ _ (hk k)⟩

end borelMooreHomology

end MMP
