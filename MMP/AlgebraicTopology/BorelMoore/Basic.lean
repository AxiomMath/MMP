module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Algebra.BigOperators.Finprod
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Comparison
/-!
# Borel–Moore homology (Fulton, §19.1)

For a topological space `X`, a *locally finite singular `n`-chain* on `X` with coefficients in a
module `M` is a possibly infinite formal sum `∑ a_σ σ` of singular `n`-simplices `σ` of `X`, with
`a_σ ∈ M`, such that every point of `X` has a neighbourhood meeting the images of only finitely
many `σ` with `a_σ ≠ 0`. The faces (and degeneracies) of a simplex have smaller image, and the
image of a simplex is compact and nonempty, so a simplicial operator pushes locally finite chains
forward to locally finite chains, by finite sums. The locally finite chains thus form a simplicial
module, and the *Borel–Moore homology* `H_i X` (homology with closed supports) is the `i`-th
homology of its alternating face map complex, extended by zero to all degrees `i : ℤ`.
The total Borel–Moore homology is `H_* X = ⨁ i, H_i X`. For a complex scheme `X` it is the
Borel–Moore homology of the underlying space `X(ℂ)`.

The construction is carried out for a type `S` of "simplices" with a *carrier* `car : S → Set X`
whose values are compact and nonempty: `MMP.LocallyFiniteChain.lfChains car` is the
module of locally finite `M`-valued functions on `S`, and a map `f : S → T` with
`car (f σ) ⊆ car σ` induces `MMP.LocallyFiniteChain.pushforward`, functorially.

## Main definitions

* `MMP.LocallyFiniteChain.lfChains car`: locally finite chains.
* `MMP.LocallyFiniteChain.pushforward`: push-forward along a carrier-decreasing map.
* `MMP.locallyFiniteSingularChains R M X`: the simplicial module of locally finite
  singular chains of `X`.
* `MMP.borelMooreChainComplex R M X`: its chain complex.
* `MMP.borelMooreHomology R M X i`: the Borel–Moore homology `H_i(X; M)`, `i : ℤ`.
* `MMP.totalBorelMooreHomology R M X`: `H_* X = ⨁ i, H_i X`.
* `MMP.IsComplexScheme.borelMooreHomology`: `H_i X` of a complex scheme `X`.

## Main results

* `MMP.LocallyFiniteChain.pushforward_id`, `pushforward_comp`: functoriality.
* `MMP.borelMooreHomologyIsoOfNat`: `H_n X` is the `n`-th homology of the complex
  of locally finite chains, for `n : ℕ`.
* `MMP.isZero_borelMooreHomology_of_neg`: `H_i X = 0` for `i < 0`.

## Implementation notes

Fulton's spaces are locally compact Hausdorff spaces admitting a closed imbedding into some `ℝ^N`;
the definition is made for every topological space, and with coefficients in any module `M` over
a commutative ring `R` (Fulton: `ℤ`, and `ℚ`). For locally compact Hausdorff spaces of this kind
it is Borel–Moore homology in the sense of Borel–Moore (Thm. 3.8 and §5).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and Example 19.1.1.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960].
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology

universe u

namespace MMP

namespace LocallyFiniteChain

open Classical

variable {X : Type*} [TopologicalSpace X] {S T U : Type*}

/-- A set `s` of simplices with carriers `car` is *locally finite*: every point has a
neighbourhood meeting the carriers of only finitely many members of `s`. -/
def IsLocallyFiniteSet (car : S → Set X) (s : Set S) : Prop :=
  ∀ x : X, ∃ V ∈ 𝓝 x, {σ | σ ∈ s ∧ (car σ ∩ V).Nonempty}.Finite

variable {car : S → Set X}

/-- A subset of a locally finite set of simplices is locally finite. -/
lemma IsLocallyFiniteSet.mono {s t : Set S} (ht : IsLocallyFiniteSet car t) (h : s ⊆ t) :
    IsLocallyFiniteSet car s := fun x ↦ by
  obtain ⟨V, hV, hfin⟩ := ht x
  exact ⟨V, hV, hfin.subset fun σ hσ ↦ ⟨h hσ.1, hσ.2⟩⟩

/-- The union of two locally finite sets of simplices is locally finite. -/
lemma IsLocallyFiniteSet.union {s t : Set S} (hs : IsLocallyFiniteSet car s)
    (ht : IsLocallyFiniteSet car t) : IsLocallyFiniteSet car (s ∪ t) := fun x ↦ by
  obtain ⟨V, hV, hfin⟩ := hs x
  obtain ⟨W, hW, hfin'⟩ := ht x
  refine ⟨V ∩ W, Filter.inter_mem hV hW, (hfin.union hfin').subset ?_⟩
  rintro σ ⟨hσ | hσ, y, hy⟩
  · exact Or.inl ⟨hσ, y, hy.1, hy.2.1⟩
  · exact Or.inr ⟨hσ, y, hy.1, hy.2.2⟩

/-- The empty set of simplices is locally finite. -/
lemma isLocallyFiniteSet_empty : IsLocallyFiniteSet car (∅ : Set S) := fun x ↦
  ⟨Set.univ, Filter.univ_mem, by simp⟩

/-- The image of a locally finite set of simplices under a map `f : S → T` with
`carT (f σ) ⊆ car σ` is locally finite. -/
lemma IsLocallyFiniteSet.image {s : Set S} (hs : IsLocallyFiniteSet car s) {carT : T → Set X}
    (f : S → T) (hf : ∀ σ, carT (f σ) ⊆ car σ) : IsLocallyFiniteSet carT (f '' s) := fun x ↦ by
  obtain ⟨V, hV, hfin⟩ := hs x
  refine ⟨V, hV, (hfin.image f).subset ?_⟩
  rintro _ ⟨⟨σ, hσ, rfl⟩, y, hy⟩
  exact ⟨σ, ⟨hσ, y, hf σ hy.1, hy.2⟩, rfl⟩

/-- A locally finite set meets only finitely many carriers inside a compact set. -/
lemma IsLocallyFiniteSet.finite_inter_compact {s : Set S} (hs : IsLocallyFiniteSet car s)
    {K : Set X} (hK : IsCompact K) : {σ | σ ∈ s ∧ (car σ ∩ K).Nonempty}.Finite := by
  have hlf : LocallyFinite fun σ : s ↦ car σ := fun x ↦ by
    obtain ⟨V, hV, hfin⟩ := hs x
    exact ⟨V, hV, hfin.preimage (Subtype.val_injective.injOn) |>.subset fun σ hσ ↦ ⟨σ.2, hσ⟩⟩
  have := (hlf.finite_nonempty_inter_compact hK).image Subtype.val
  refine this.subset ?_
  rintro σ ⟨hσ, hK⟩
  exact ⟨⟨σ, hσ⟩, hK, rfl⟩

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The `R`-module of *locally finite chains*: functions `c : S → M` whose support is a locally
finite set of simplices. -/
def lfChains (car : S → Set X) : Submodule R (S → M) where
  carrier := {c | IsLocallyFiniteSet car (Function.support c)}
  add_mem' {c d} hc hd := (IsLocallyFiniteSet.union hc hd).mono (Function.support_add c d)
  zero_mem' := isLocallyFiniteSet_empty.mono (by simp)
  smul_mem' r c hc := IsLocallyFiniteSet.mono hc (Function.support_const_smul_subset r c)

variable {R M}

/-- A function `c : S → M` is a locally finite chain if and only if its support is a locally
finite set of simplices. -/
lemma mem_lfChains {c : S → M} :
    c ∈ lfChains R M car ↔ IsLocallyFiniteSet car (Function.support c) := Iff.rfl

/-- The coefficient-level push-forward of `c : S → M` along `f : S → T`: the value at `τ` is the
(finite, for locally finite `c`) sum of the coefficients of the simplices `σ` with `f σ = τ`. -/
def pushforwardFun (f : S → T) (c : S → M) : T → M :=
  fun τ ↦ ∑ᶠ σ, if f σ = τ then c σ else 0

/-- The value of `pushforwardFun f c` at `τ` is the finite sum over any finset `F` containing
every `σ` with `c σ ≠ 0` and `f σ = τ`. -/
lemma pushforwardFun_apply_eq_sum (f : S → T) (c : S → M) (τ : T) (F : Finset S)
    (hF : ∀ σ, c σ ≠ 0 → f σ = τ → σ ∈ F) :
    pushforwardFun f c τ = ∑ σ ∈ F, if f σ = τ then c σ else 0 := by
  refine finsum_eq_sum_of_support_subset _ fun σ hσ ↦ ?_
  simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hσ
  exact hF σ hσ.2 hσ.1

/-- The support of `pushforwardFun f c` is contained in the image under `f` of the support
of `c`. -/
lemma support_pushforwardFun_subset (f : S → T) (c : S → M) :
    Function.support (pushforwardFun f c) ⊆ f '' Function.support c := by
  intro τ hτ
  by_contra h
  refine hτ (finsum_eq_zero_of_forall_eq_zero fun σ ↦ ?_)
  split_ifs with hσ
  · exact not_not.1 fun hc ↦ h ⟨σ, hc, hσ⟩
  · rfl

variable {carT : T → Set X}

/-- The simplices of a locally finite chain sent to a simplex with compact nonempty carrier, by
a carrier-decreasing map, are finitely many. -/
lemma finite_fiber {c : S → M} (hc : c ∈ lfChains R M car) (f : S → T)
    (hf : ∀ σ, carT (f σ) ⊆ car σ) (τ : T) (hτ : IsCompact (carT τ)) (hτ' : (carT τ).Nonempty) :
    {σ | c σ ≠ 0 ∧ f σ = τ}.Finite :=
  (hc.finite_inter_compact hτ).subset fun σ ⟨h1, h2⟩ ↦
    ⟨h1, hτ'.mono fun y hy ↦ ⟨hf σ (h2 ▸ hy), hy⟩⟩

/-- The push-forward of locally finite chains along a map `f : S → T` decreasing the carriers,
when the carriers of `T` are compact and nonempty. -/
def pushforward (f : S → T) (hf : ∀ σ, carT (f σ) ⊆ car σ)
    (hT : ∀ τ, IsCompact (carT τ) ∧ (carT τ).Nonempty) :
    lfChains R M car →ₗ[R] lfChains R M carT where
  toFun c := ⟨pushforwardFun f c.1,
    ((c.2.image f hf).mono (support_pushforwardFun_subset f c.1))⟩
  map_add' c d := by
    ext τ
    let F := (finite_fiber c.2 f hf τ (hT τ).1 (hT τ).2).toFinset ∪
      (finite_fiber d.2 f hf τ (hT τ).1 (hT τ).2).toFinset
    have hcF : ∀ σ, c.1 σ ≠ 0 → f σ = τ → σ ∈ F := fun σ h1 h2 ↦
      Finset.mem_union_left _ (by simpa using And.intro h1 h2)
    have hdF : ∀ σ, d.1 σ ≠ 0 → f σ = τ → σ ∈ F := fun σ h1 h2 ↦
      Finset.mem_union_right _ (by simpa using And.intro h1 h2)
    have hcdF : ∀ σ, (c + d).1 σ ≠ 0 → f σ = τ → σ ∈ F := fun σ h1 h2 ↦ by
      by_cases hc : c.1 σ = 0
      · exact hdF σ (fun hd ↦ h1 (by simp [hc, hd])) h2
      · exact hcF σ hc h2
    change pushforwardFun f (c + d).1 τ = pushforwardFun f c.1 τ + pushforwardFun f d.1 τ
    rw [pushforwardFun_apply_eq_sum f _ τ F hcdF, pushforwardFun_apply_eq_sum f _ τ F hcF,
      pushforwardFun_apply_eq_sum f _ τ F hdF, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    split_ifs <;> simp
  map_smul' r c := by
    ext τ
    let F := (finite_fiber c.2 f hf τ (hT τ).1 (hT τ).2).toFinset
    have hcF : ∀ σ, c.1 σ ≠ 0 → f σ = τ → σ ∈ F := fun σ h1 h2 ↦ by
      simpa [F] using And.intro h1 h2
    have hrF : ∀ σ, (r • c).1 σ ≠ 0 → f σ = τ → σ ∈ F := fun σ h1 h2 ↦
      hcF σ (fun h ↦ h1 (by simp [h])) h2
    change pushforwardFun f (r • c).1 τ = r • pushforwardFun f c.1 τ
    rw [pushforwardFun_apply_eq_sum f _ τ F hrF, pushforwardFun_apply_eq_sum f _ τ F hcF,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    split_ifs <;> simp

/-- The underlying function of `pushforward f hf hT c` is `pushforwardFun f c`. -/
lemma pushforward_apply_coe (f : S → T) (hf : ∀ σ, carT (f σ) ⊆ car σ)
    (hT : ∀ τ, IsCompact (carT τ) ∧ (carT τ).Nonempty) (c : lfChains R M car) :
    (pushforward f hf hT c : T → M) = pushforwardFun f c.1 := rfl

/-- The push-forward along the identity is the identity. -/
lemma pushforward_id (hS : ∀ σ, IsCompact (car σ) ∧ (car σ).Nonempty) :
    pushforward (R := R) (M := M) (car := car) id (fun _ ↦ subset_rfl) hS = LinearMap.id := by
  ext c σ
  change pushforwardFun id c.1 σ = c.1 σ
  rw [pushforwardFun_apply_eq_sum id c.1 σ {σ} (fun σ' _ h ↦ by simp [← h])]
  simp

/-- The push-forward along `g ∘ f` is the composite of the push-forwards along `f` and `g`. -/
lemma pushforward_comp {carU : U → Set X} (f : S → T) (g : T → U)
    (hf : ∀ σ, carT (f σ) ⊆ car σ) (hg : ∀ τ, carU (g τ) ⊆ carT τ)
    (hT : ∀ τ, IsCompact (carT τ) ∧ (carT τ).Nonempty)
    (hU : ∀ υ, IsCompact (carU υ) ∧ (carU υ).Nonempty) :
    pushforward (R := R) (M := M) (g ∘ f) (fun σ ↦ (hg (f σ)).trans (hf σ)) hU =
      (pushforward g hg hU).comp (pushforward f hf hT) := by
  ext c υ
  change pushforwardFun (g ∘ f) c.1 υ = pushforwardFun g (pushforwardFun f c.1) υ
  let F := (c.2.finite_inter_compact (hU υ).1).toFinset
  have hmemF : ∀ σ, c.1 σ ≠ 0 → carU υ ⊆ car σ → σ ∈ F := fun σ h1 h2 ↦ by
    have hne : (car σ ∩ carU υ).Nonempty := (hU υ).2.mono fun y hy ↦ ⟨h2 hy, hy⟩
    simpa [F] using And.intro h1 hne
  have h1 : ∀ σ, c.1 σ ≠ 0 → (g ∘ f) σ = υ → σ ∈ F := fun σ h1 h2 ↦
    hmemF σ h1 fun y hy ↦ hf σ (hg (f σ) (by rwa [show g (f σ) = υ from h2]))
  have h2 : ∀ τ, pushforwardFun f c.1 τ ≠ 0 → g τ = υ → τ ∈ F.image f := fun τ h h' ↦ by
    obtain ⟨σ, hσ, rfl⟩ := support_pushforwardFun_subset f c.1 h
    exact Finset.mem_image_of_mem f (h1 σ hσ h')
  rw [pushforwardFun_apply_eq_sum _ c.1 υ F h1,
    pushforwardFun_apply_eq_sum g _ υ (F.image f) h2]
  have : ∀ τ ∈ F.image f, (if g τ = υ then pushforwardFun f c.1 τ else 0) =
      ∑ σ ∈ F, if f σ = τ then (if g τ = υ then c.1 σ else 0) else 0 := fun τ _ ↦ by
    split_ifs with hτ
    · rw [pushforwardFun_apply_eq_sum f c.1 τ F fun σ h h' ↦ h1 σ h (by simp [h', hτ])]
    · simp
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  rw [Finset.sum_ite_eq (F.image f) (f σ), if_pos (Finset.mem_image_of_mem f hσ)]
  rfl

end LocallyFiniteChain

open LocallyFiniteChain

section Singular

variable (X : TopCat.{u})

/-- The image `σ(Δⁿ) ⊆ X` of a singular simplex `σ` of `X`. -/
def singularSimplexImage {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj X).obj n) : Set X :=
  Set.range (X.toSSetObjEquiv n σ)

variable {X}

/-- The image of a singular simplex is compact. -/
lemma isCompact_singularSimplexImage {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj X).obj n) :
    IsCompact (singularSimplexImage X σ) :=
  isCompact_range (X.toSSetObjEquiv n σ).continuous

/-- The image of a singular simplex is nonempty. -/
lemma nonempty_singularSimplexImage {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj X).obj n) :
    (singularSimplexImage X σ).Nonempty :=
  Set.range_nonempty _

/-- The image of a simplicial operator applied to a singular simplex `σ` is contained in the
image of `σ`. -/
lemma singularSimplexImage_map_subset {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (σ : (TopCat.toSSet.obj X).obj n) :
    singularSimplexImage X ((TopCat.toSSet.obj X).map θ σ) ⊆ singularSimplexImage X σ := by
  rintro _ ⟨y, rfl⟩
  exact ⟨_, rfl⟩

open Simplicial in
/-- The range of the continuous map of a singular simplex is its image. -/
lemma range_simplexEquiv {n : ℕ} (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    Set.range (SingularCochain.simplexEquiv X n σ) = singularSimplexImage X σ :=
  (SingularChain.stdSimplexHomeo (Fin (n + 1))).surjective.range_comp (X.toSSetObjEquiv (op ⦋n⦌) σ)

end Singular

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- The simplicial `R`-module of *locally finite singular chains* of `X` with coefficients in `M`:
in degree `n`, the locally finite formal sums of singular `n`-simplices; a simplicial operator
acts by pushing chains forward along its action on simplices. -/
def locallyFiniteSingularChains (X : TopCat.{u}) : SimplicialObject (ModuleCat.{u} R) where
  obj n := ModuleCat.of R (lfChains R M (singularSimplexImage X (n := n)))
  map θ := ModuleCat.ofHom (pushforward ((TopCat.toSSet.obj X).map θ)
    (singularSimplexImage_map_subset θ)
    (fun σ ↦ ⟨isCompact_singularSimplexImage σ, nonempty_singularSimplexImage σ⟩))
  map_id n := by
    ext1
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id]
    convert pushforward_id (R := R) (M := M)
      (fun σ ↦ ⟨isCompact_singularSimplexImage σ, nonempty_singularSimplexImage σ⟩) using 2
    funext σ
    simp
  map_comp θ θ' := by
    ext1
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    rw [← pushforward_comp _ _ _ _
      (fun σ ↦ ⟨isCompact_singularSimplexImage σ, nonempty_singularSimplexImage σ⟩)]
    congr 1
    funext σ
    simp

/-- The complex of locally finite singular chains of `X`, with the alternating sum of the face
maps as differential. -/
def borelMooreChainComplex (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} R) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{u} R)).obj (locallyFiniteSingularChains R M X)

/-- The *Borel–Moore homology* `H_i(X; M)` of a space `X` (Fulton, §19.1): the `i`-th homology of
the complex of locally finite singular chains on `X`, for `i : ℤ` (zero for `i < 0`). -/
def borelMooreHomology (X : TopCat.{u}) (i : ℤ) : ModuleCat.{u} R :=
  ((borelMooreChainComplex R M X).extend ComplexShape.embeddingDownNat).homology (-i)

/-- The total Borel–Moore homology `H_* X = ⨁ i, H_i X`. -/
def totalBorelMooreHomology (X : TopCat.{u}) : ModuleCat.{u} R :=
  ModuleCat.of R (DirectSum ℤ fun i ↦ borelMooreHomology R M X i)

/-- For `n : ℕ`, the Borel–Moore homology `H_n X` is the `n`-th homology of the complex of locally
finite singular chains. -/
def borelMooreHomologyIsoOfNat (X : TopCat.{u}) (n : ℕ) :
    borelMooreHomology R M X n ≅ (borelMooreChainComplex R M X).homology n :=
  (borelMooreChainComplex R M X).extendHomologyIso ComplexShape.embeddingDownNat (by simp)

/-- Borel–Moore homology vanishes in negative degrees. -/
lemma isZero_borelMooreHomology_of_neg (X : TopCat.{u}) {i : ℤ} (hi : i < 0) :
    IsZero (borelMooreHomology R M X i) :=
  ((borelMooreChainComplex R M X).extend_exactAt ComplexShape.embeddingDownNat (-i)
    (fun n hn ↦ by simp at hn; lia)).isZero_homology

/-- The Borel–Moore homology `H_i X` of a complex scheme `X` (Fulton, §19.1): that of its
underlying space `X(ℂ)` with the classical topology. -/
abbrev IsComplexScheme.borelMooreHomology (R : Type) [CommRing R] (M : ModuleCat.{0} R)
    (X : AlgebraicGeometry.Scheme.{0}) [X.Over (AlgebraicGeometry.Spec (.of ℂ))] (i : ℤ) :
    ModuleCat.{0} R :=
  MMP.borelMooreHomology R M (TopCat.of (UnderlyingSpace ℂ X)) i

end MMP
