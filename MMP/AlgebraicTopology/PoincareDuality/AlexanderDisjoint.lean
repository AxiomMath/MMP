module

public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.BorelMoore.DisjointUnion
public import MMP.AlgebraicTopology.CapProduct.Neighbourhood
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductNatural

/-!
# Poincaré duality for a disjoint union of open sets

Let a Hausdorff space `Y` be the union of pairwise disjoint open subsets `V i`, indexed by an
arbitrary type. Each `V i` is then open and closed, and every singular simplex of `Y` lies in
exactly one `V i` (its image is connected). Hence:

* a cochain of `Y` is the same as a family of cochains of the `V i` (`glueCochain`), compatibly
  with the coboundary;
* a locally finite chain of `Y` is the same as a family of locally finite chains of the `V i`
  (`glueChain`; the family is locally finite because the `V i` are open and disjoint),
  compatibly with the boundary; the restriction to `V i` is `c ↦ (τ ↦ c (ι_i ∘ τ))`;
* the restriction of `φ ∩ c` to `V i` is `ι_i^* φ ∩ c|_{V i}`.

Consequently, for a locally finite `n`-cycle `z` of `Y`, if the duality maps
`H^p(V i) → H_q(V i)`, `[φ] ↦ [φ ∩ z|_{V i}]` (`p + q = n`) are bijective for every `i`, so is
`H^p Y → H_q Y`, `[φ] ↦ [φ ∩ z]`; and the vanishing of `H^p` and of `H_q` passes from the `V i`
to `Y`.

## Main definitions

* `MMP.PoincareAlexander.glueCochain`, `MMP.PoincareAlexander.glueChain`.

## Main results

* `MMP.PoincareAlexander.restrict_capChain`: restriction of the cap product.
* `MMP.PoincareAlexander.bijective_capHomQ_of_disjoint`: duality for a disjoint
  union.

## References

* [G. Bredon, *Topology and Geometry*][bredon1993], VI.7.9.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Opposite Simplicial Function

universe u

namespace MMP

open MMP

namespace PoincareAlexander

open MMP.PoincareAlexander

open SingularCross BorelMooreCross SingularCochain SingularChain LocallyFiniteChain
  borelMooreHomology BorelMooreCap

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} {ι : Type*}
  {V : ι → TopologicalSpace.Opens Y}

section pieces

/-- In a disjoint open cover, each member is closed (any index type). -/
lemma isClopen_of_pairwise_disjoint (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) (l : ι) : IsClopen (V l : Set Y) := by
  classical
  refine ⟨?_, (V l).isOpen⟩
  have : (V l : Set Y)ᶜ = ⋃ m ∈ ({l}ᶜ : Set ι), (V m : Set Y) := by
    ext y
    simp only [mem_compl_iff, mem_iUnion, exists_prop]
    constructor
    · intro hy
      obtain ⟨m, hm⟩ := hcov y
      exact ⟨m, fun h ↦ hy (h ▸ hm), hm⟩
    · rintro ⟨m, hm, hym⟩ hyl
      exact Set.disjoint_left.1 (hdisj hm) hym hyl
  rw [← isOpen_compl_iff, this]
  exact isOpen_biUnion fun m _ ↦ (V m).isOpen

/-- A connected nonempty set lies in exactly one member of a disjoint open cover. -/
lemma exists_subset_of_isPreconnected (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {S : Set Y} (hS : IsPreconnected S) (hne : S.Nonempty) :
    ∃ l, S ⊆ V l := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨l, hl⟩ := hcov y
  exact ⟨l, hS.subset_isClopen (isClopen_of_pairwise_disjoint hdisj hcov l) ⟨y, hy, hl⟩⟩

/-- A nonempty set contained in two members of a disjoint open cover forces the indices to
agree. -/
lemma eq_of_subset_of_subset (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    {S : Set Y} (hne : S.Nonempty) {l m : ι} (hl : S ⊆ V l) (hm : S ⊆ V m) : l = m := by
  by_contra h
  obtain ⟨y, hy⟩ := hne
  exact Set.disjoint_left.1 (hdisj h) (hl hy) (hm hy)

/-- The image of a singular simplex is nonempty. -/
lemma range_simplex_nonempty {n : ℕ} (σ : Simplex Y n) : (range σ).Nonempty :=
  range_nonempty_iff_nonempty.2 ⟨stdSimplex.vertex 0⟩

end pieces

section cochains

variable (V) in
/-- The simplex `σ` of `Y` lying in `V l`, as a simplex of `V l`. -/
def coSimplex {n : ℕ} (l : ι) (σ : Simplex Y n) (h : range σ ⊆ V l) :
    Simplex (TopCat.of (V l)) n :=
  ⟨fun t ↦ ⟨σ t, h ⟨t, rfl⟩⟩, σ.continuous.subtype_mk _⟩

/-- Composing `coSimplex V l σ h` with the inclusion of `V l` recovers `σ`. -/
lemma comp_coSimplex {n : ℕ} (l : ι) (σ : Simplex Y n) (h : range σ ⊆ V l) :
    (clopenInclusion (V l)).hom.comp (coSimplex V l σ h) = σ :=
  rfl

/-- A simplex of `V l`, viewed as a simplex of `Y`, has image in `V l`. -/
lemma range_comp_subset {n : ℕ} (l : ι) (τ : Simplex (TopCat.of (V l)) n) :
    range ((clopenInclusion (V l)).hom.comp τ) ⊆ V l := by
  rintro _ ⟨t, rfl⟩
  exact (τ t).2

open Classical in
variable (V) in
/-- Gluing cochains of the members of a disjoint open cover to a cochain of `Y`. -/
def glueCochain {n : ℕ} (φ : ∀ l, Simplex (TopCat.of (V l)) n → R) : Simplex Y n → R :=
  fun σ ↦ ∑ᶠ l, if h : range σ ⊆ V l then φ l (coSimplex V l σ h) else 0

/-- The glued cochain takes the value `φ l τ` on a simplex `τ` of `V l` viewed in `Y`. -/
lemma glueCochain_comp (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y))) {n : ℕ}
    (φ : ∀ l, Simplex (TopCat.of (V l)) n → R) (l : ι) (τ : Simplex (TopCat.of (V l)) n) :
    glueCochain V φ ((clopenInclusion (V l)).hom.comp τ) = φ l τ := by
  classical
  have hsub := range_comp_subset l τ
  rw [glueCochain, finsum_eq_single _ l (fun m hm ↦ dite_eq_right fun h ↦ hm
    (eq_of_subset_of_subset hdisj (range_simplex_nonempty _) h hsub)), dif_pos hsub]
  rfl

/-- The pull-back of the glued cochain to `V l` is `φ l`. -/
lemma cochainPullback_glueCochain (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    {n : ℕ} (φ : ∀ l, Simplex (TopCat.of (V l)) n → R) (l : ι) :
    cochainPullback R (clopenInclusion (V l)) n (glueCochain V φ) = φ l :=
  funext fun τ ↦ glueCochain_comp hdisj φ l τ

/-- Cochains of `Y` are determined by their pull-backs to the members of a disjoint open
cover. -/
lemma cochain_ext (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {n : ℕ} {ψ ψ' : Simplex Y n → R}
    (h : ∀ l, cochainPullback R (clopenInclusion (V l)) n ψ =
      cochainPullback R (clopenInclusion (V l)) n ψ') : ψ = ψ' := by
  funext σ
  obtain ⟨l, hl⟩ := exists_subset_of_isPreconnected hdisj hcov
    (isPreconnected_range σ.continuous) (range_simplex_nonempty σ)
  have := congrFun (h l) (coSimplex V l σ hl)
  rwa [cochainPullback_apply, cochainPullback_apply, comp_coSimplex] at this

/-- The coboundary of a glued cochain is the gluing of the coboundaries. -/
lemma coboundary_glueCochain (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {n : ℕ} (φ : ∀ l, Simplex (TopCat.of (V l)) n → R) :
    coboundary R n (glueCochain V φ) = glueCochain V fun l ↦ coboundary R n (φ l) :=
  cochain_ext hdisj hcov fun l ↦ by
    rw [← coboundary_cochainPullback, cochainPullback_glueCochain hdisj,
      cochainPullback_glueCochain hdisj]

end cochains

section chains

variable [T2Space Y]

variable (V) in
/-- The simplices of `V l` as simplices of `Y`. -/
abbrev sMap (l : ι) (n : ℕ) : Simp (TopCat.of (V l)) n → Simp Y n :=
  (TopCat.toSSet.map (clopenInclusion (V l))).app (op ⦋n⦌)

variable (R V) in
/-- The restriction of locally finite chains to `V l`. -/
abbrev res (l : ι) (n : ℕ) : (BM R Y).X n →ₗ[R] (BM R (TopCat.of (V l))).X n :=
  ((restrictChainMap R (ModuleCat.of R R) (V l)).f n).hom

/-- The inclusion of a member of a disjoint open cover is a proper map. -/
lemma isProperMap_inclusion (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) (l : ι) : IsProperMap (clopenInclusion (V l)) :=
  (isClopen_of_pairwise_disjoint hdisj hcov l).isClosed.isClosedEmbedding_subtypeVal.isProperMap

/-- The coefficient of the restriction `c|_{V l}` at `τ` is the coefficient of `c` at `τ`
viewed as a simplex of `Y`. -/
lemma res_apply (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {n : ℕ} (l : ι) (c : (BM R Y).X n)
    (τ : Simp (TopCat.of (V l)) n) : (res R V l n c).1 τ = c.1 (sMap V l n τ) := by
  rw [restrictChainMap_f_apply_coe,
    kernelFun_restrictKernel_of_isClopen (V l) (isClopen_of_pairwise_disjoint hdisj hcov l)]

/-- A simplex of `V l`, viewed as a simplex of `Y`, has image in `V l`. -/
lemma image_sMap_subset {n : ℕ} (l : ι) (τ : Simp (TopCat.of (V l)) n) :
    singularSimplexImage Y (sMap V l n τ) ⊆ V l :=
  (range_simplexEquiv _).symm.subset.trans (range_toSSetObjEquiv_map_clopenInclusion_subset (V l) τ)

/-- Every simplex of `Y` comes from a simplex of some member of a disjoint open cover. -/
lemma exists_eq_sMap (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {n : ℕ} (σ : Simp Y n) :
    ∃ l τ, sMap V l n τ = σ := by
  obtain ⟨l, hl⟩ := exists_subset_of_isPreconnected hdisj hcov
    (isPreconnected_range (SingularCochain.simplexEquiv Y _ σ : Simplex Y n).continuous)
    ((nonempty_singularSimplexImage σ).mono (range_simplexEquiv σ).symm.subset)
  obtain ⟨τ, hτ⟩ := mem_range_map_clopenInclusion (V l) hl
  exact ⟨l, τ, hτ⟩

/-- For `l ≠ m`, a simplex of `V l` does not come from a simplex of `V m`. -/
lemma sMap_notMem_range (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y))) {n : ℕ}
    {l m : ι} (hlm : l ≠ m) (τ : Simp (TopCat.of (V l)) n) :
    sMap V l n τ ∉ range (sMap V m n) :=
  notMem_range_map_clopenInclusion (V m) fun h ↦ hlm
    (eq_of_subset_of_subset hdisj (nonempty_singularSimplexImage _) (image_sMap_subset l τ) ((range_simplexEquiv _).symm.subset.trans h))

/-- Locally finite chains of `Y` are determined by their restrictions to the members of a
disjoint open cover. -/
lemma chain_ext (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {n : ℕ} {c c' : (BM R Y).X n}
    (h : ∀ l, res R V l n c = res R V l n c') : c = c' := by
  apply Subtype.ext
  funext σ
  obtain ⟨l, τ, rfl⟩ := exists_eq_sMap hdisj hcov σ
  simpa only [res_apply hdisj hcov] using congrArg (fun x ↦ x.1 τ) (h l)

variable (V) in
/-- The coefficients of the glued chain. -/
def glueFun {n : ℕ} (c : ∀ l, (BM R (TopCat.of (V l))).X n) : Simp Y n → R :=
  fun σ ↦ ∑ᶠ l, pushforwardFun (sMap V l n) (c l).1 σ

/-- The glued coefficient function takes the value `(c l) τ` on a simplex `τ` of `V l`. -/
lemma glueFun_sMap (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y))) {n : ℕ}
    (c : ∀ l, (BM R (TopCat.of (V l))).X n) (l : ι) (τ : Simp (TopCat.of (V l)) n) :
    glueFun V c (sMap V l n τ) = (c l).1 τ := by
  rw [glueFun, finsum_eq_single _ l (fun m hm ↦ pushforwardFun_apply_of_notMem_range _
    (sMap_notMem_range hdisj (Ne.symm hm) τ))]
  exact pushforwardFun_apply_of_injective (map_clopenInclusion_injective (V l) n) _ τ

/-- The glued coefficient function is a locally finite chain of `Y`. -/
lemma glueFun_mem (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {n : ℕ} (c : ∀ l, (BM R (TopCat.of (V l))).X n) :
    glueFun V c ∈ lfChains R (ModuleCat.of R R) (singularSimplexImage Y (n := op ⦋n⦌)) := by
  intro y
  obtain ⟨l, hl⟩ := hcov y
  obtain ⟨N, hN, hfin⟩ := (c l).2 ⟨y, hl⟩
  refine ⟨Subtype.val '' N, ?_, (hfin.image (sMap V l n)).subset ?_⟩
  · exact (V l).isOpen.isOpenEmbedding_subtypeVal.image_mem_nhds.2 hN
  · rintro σ ⟨hσ, x, hxσ, hxN⟩
    obtain ⟨m, τ, rfl⟩ := exists_eq_sMap hdisj hcov σ
    obtain ⟨x', hx'N, rfl⟩ := hxN
    have hml : m = l := by
      by_contra h
      exact Set.disjoint_left.1 (hdisj h) (image_sMap_subset m τ hxσ) x'.2
    subst hml
    refine ⟨τ, ⟨?_, ?_⟩, rfl⟩
    · rwa [Function.mem_support, ← glueFun_sMap hdisj c]
    · rw [singularSimplexImage_map] at hxσ
      obtain ⟨w, hw, hwx⟩ := hxσ
      exact ⟨w, hw, (Subtype.val_injective hwx) ▸ hx'N⟩

variable (V) in
/-- Gluing locally finite chains of the members of a disjoint open cover to a locally finite
chain of `Y`. -/
def glueChain (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {n : ℕ} (c : ∀ l, (BM R (TopCat.of (V l))).X n) :
    (BM R Y).X n :=
  (⟨glueFun V c, glueFun_mem hdisj hcov c⟩ :
    lfChains R (ModuleCat.of R R) (singularSimplexImage Y (n := op ⦋n⦌)))

/-- The restriction of the glued chain to `V l` is `c l`. -/
lemma res_glueChain (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {n : ℕ} (c : ∀ l, (BM R (TopCat.of (V l))).X n) (l : ι) :
    res R V l n (glueChain V hdisj hcov c) = c l :=
  Subtype.ext <| funext fun τ ↦ (res_apply hdisj hcov l _ τ).trans (glueFun_sMap hdisj c l τ)

/-- Restriction to `V l` commutes with the boundary. -/
lemma res_d {n : ℕ} (l : ι) (c : (BM R Y).X (n + 1)) :
    res R V l n (((BM R Y).d (n + 1) n).hom c) =
      ((BM R (TopCat.of (V l))).d (n + 1) n).hom (res R V l (n + 1) c) := by
  have := congrArg (fun f ↦ f.hom c) ((restrictChainMap R (ModuleCat.of R R) (V l)).comm (n + 1) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this.symm

/-- The boundary of a glued chain is the gluing of the boundaries. -/
lemma d_glueChain (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {n : ℕ} (c : ∀ l, (BM R (TopCat.of (V l))).X (n + 1)) :
    ((BM R Y).d (n + 1) n).hom (glueChain V hdisj hcov c) =
      glueChain V hdisj hcov fun l ↦ ((BM R (TopCat.of (V l))).d (n + 1) n).hom (c l) :=
  chain_ext hdisj hcov fun l ↦ by rw [res_d, res_glueChain, res_glueChain]

/-- **Restriction of the cap product to a member of a disjoint open cover:**
`(φ ∩ c)|_{V l} = ι_l^* φ ∩ c|_{V l}`. -/
theorem restrict_capChain (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R)
    (c : (BM R Y).X n) (l : ι) :
    res R V l q (capChain R p q n h φ c) =
      capChain R p q n h (cochainPullback R (clopenInclusion (V l)) p φ) (res R V l n c) := by
  set hf := isProperMap_inclusion hdisj hcov l
  set ι₁ := fun m ↦ ((chainMap R (ModuleCat.of R R) (clopenInclusion (V l)) hf).f m).hom
  have hid : ∀ m (x : (BM R (TopCat.of (V l))).X m), res R V l m (ι₁ m x) = x := fun m x ↦ by
    have := congrArg (fun f ↦ (f.f m).hom x) (chainMap_comp_restrictChainMap_self R
      (ModuleCat.of R R) (V l) (isClopen_of_pairwise_disjoint hdisj hcov l) hf)
    simpa using this
  set c₁ := ι₁ n (res R V l n c)
  have hc₁ : ∀ τ, c₁.1 (sMap V l n τ) = (res R V l n c).1 τ := fun τ ↦
    pushforwardFun_apply_of_injective (map_clopenInclusion_injective (V l) n) _ τ
  have hsplit : c = c₁ + (c - c₁) := by abel
  have h1 : res R V l q (capChain R p q n h φ c₁) =
      capChain R p q n h (cochainPullback R (clopenInclusion (V l)) p φ) (res R V l n c) := by
    rw [← chainMap_capChain (clopenInclusion (V l)) hf]
    exact hid q _
  have h2 : res R V l q (capChain R p q n h φ (c - c₁)) = 0 := by
    apply Subtype.ext
    funext τ
    rw [res_apply hdisj hcov]
    by_contra hne
    have hsub := singularSimplexImage_subset_of_coeff_capChain_ne_zero (A := ∅)
      (V := (V l : Set Y)ᶜ) p q n h (φ := φ) (fun _ hσ ↦ ?_) (c - c₁) ?_ hne
    · obtain ⟨y, hy⟩ := nonempty_singularSimplexImage (sMap V l q τ)
      exact hsub hy (image_sMap_subset l τ hy)
    · exact ((range_simplex_nonempty _).ne_empty (subset_empty_iff.1 hσ)).elim
    · intro σ hσ
      right
      obtain ⟨m, τ', rfl⟩ := exists_eq_sMap hdisj hcov σ
      by_cases hml : m = l
      · subst hml
        refine absurd ?_ hσ
        have e : coeff R (c - c₁) (sMap V m n τ') = c.1 (sMap V m n τ') - c₁.1 (sMap V m n τ') :=
          rfl
        rw [e, hc₁, res_apply hdisj hcov, sub_self]
      · exact (image_sMap_subset m τ').trans fun y hy hyl ↦
          Set.disjoint_left.1 (hdisj hml) hy hyl
  conv_lhs => rw [hsplit, map_add, map_add, h1, h2, add_zero]

end chains

section duality

variable [T2Space Y]

/-- Every cochain vanishes on the simplices lying in the empty set. -/
lemma mem_vanishing_empty {Z : TopCat.{u}} {n : ℕ} (φ : Simplex Z n → R) :
    φ ∈ vanishing R n (∅ : Set Z) := fun σ hσ ↦
  ((range_simplex_nonempty σ).ne_empty (subset_empty_iff.1 hσ)).elim

variable (V) in
/-- The restriction of a cycle to `V l`. -/
def resCyc (l : ι) {n : ℕ} (z : Cyc (R := R) Y n) : Cyc (R := R) (TopCat.of (V l)) n :=
  ⟨res R V l n z.1, chainMap_mem_cyc R (restrictChainMap R (ModuleCat.of R R) (V l)) z⟩

variable (V) in
/-- The pull-back of a cocycle to `V l`. -/
def pullCocycle (l : ι) {p : ℕ} (φ : relCocycles R (∅ : Set Y) p) :
    relCocycles R (∅ : Set (TopCat.of (V l))) p :=
  ⟨cochainPullback R (clopenInclusion (V l)) p φ.1,
    cochainPullback_mem_relCocycles _ (empty_subset _) φ.2⟩

/-- The class of a locally finite cycle vanishes if and only if the cycle is a boundary. -/
lemma mk_eq_zero_iff_exists {Z : TopCat.{u}} {q : ℕ} (w : Cyc (R := R) Z q) :
    (Submodule.Quotient.mk w : HomQ (R := R) Z q) = 0 ↔
      ∃ u : (BM R Z).X (q + 1), ((BM R Z).d (q + 1) q).hom u = w.1 :=
  (Submodule.Quotient.mk_eq_zero _).trans
    ⟨fun hw ↦ exists_of_mem_bdry hw, fun ⟨u, hu⟩ ↦ mem_bdry_of w u hu⟩

/-- Two locally finite cycles have the same class if and only if their difference is a
boundary. -/
lemma mk_eq_mk_iff_exists {Z : TopCat.{u}} {q : ℕ} (w w' : Cyc (R := R) Z q) :
    (Submodule.Quotient.mk w : HomQ (R := R) Z q) = Submodule.Quotient.mk w' ↔
      ∃ u : (BM R Z).X (q + 1), ((BM R Z).d (q + 1) q).hom u = w.1 - w'.1 :=
  (Submodule.Quotient.eq _).trans
    ⟨fun hw ↦ exists_of_mem_bdry hw, fun ⟨u, hu⟩ ↦ mem_bdry_of (w - w') u hu⟩

/-- A cycle of `Y` whose restrictions to all `V l` are boundaries is a boundary. -/
theorem mk_eq_zero_of_forall_resCyc (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {q : ℕ} (w : Cyc (R := R) Y q)
    (hw : ∀ l, (Submodule.Quotient.mk (resCyc V l w) : HomQ (R := R) (TopCat.of (V l)) q) = 0) :
    (Submodule.Quotient.mk w : HomQ (R := R) Y q) = 0 := by
  choose u hu using fun l ↦ (mk_eq_zero_iff_exists _).1 (hw l)
  refine (mk_eq_zero_iff_exists w).2 ⟨glueChain V hdisj hcov u, ?_⟩
  refine chain_ext hdisj hcov fun l ↦ ?_
  rw [res_d, res_glueChain]
  exact hu l

/-- A cocycle of `Y` whose pull-backs to all `V l` are coboundaries is a coboundary. -/
theorem mk_eq_zero_of_forall_pullCocycle (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {p : ℕ} (φ : relCocycles R (∅ : Set Y) p)
    (hφ : ∀ l, (Submodule.Quotient.mk (pullCocycle V l φ) :
      relCohomology R (∅ : Set (TopCat.of (V l))) p) = 0) :
    (Submodule.Quotient.mk φ : relCohomology R (∅ : Set Y) p) = 0 := by
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  change φ.1 ∈ relCoboundaries R ∅ p
  have hφ' : ∀ l, cochainPullback R (clopenInclusion (V l)) p φ.1 ∈
      relCoboundaries R (∅ : Set (TopCat.of (V l))) p := fun l ↦
    (Submodule.Quotient.mk_eq_zero ((relCoboundaries R (∅ : Set (TopCat.of (V l))) p).comap
      (relCocycles R (∅ : Set (TopCat.of (V l))) p).subtype)).1 (hφ l)
  cases p with
  | zero =>
    have : φ.1 = 0 := cochain_ext hdisj hcov fun l ↦ by
      rw [map_zero]
      exact (Submodule.mem_bot R).1 (hφ' l)
    exact this ▸ Submodule.zero_mem _
  | succ p =>
    choose ψ hψv hψ using hφ'
    refine ⟨glueCochain V ψ, mem_vanishing_empty _, ?_⟩
    rw [coboundary_glueCochain hdisj hcov]
    refine cochain_ext hdisj hcov fun l ↦ ?_
    rw [cochainPullback_glueCochain hdisj]
    exact hψ l

/-- Injectivity half of Poincaré duality for a disjoint union. -/
theorem injective_capHomQ_of_disjoint (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) (p q n : ℕ) (h : p + q = n) (z : Cyc (R := R) Y n)
    (hV : ∀ l, Injective fun c ↦ capHomQ R (∅ : Set (TopCat.of (V l))) p q n h c
      (Submodule.Quotient.mk (resCyc V l z))) :
    Injective fun c ↦ capHomQ R (∅ : Set Y) p q n h c (Submodule.Quotient.mk z) := by
  change Injective ((capHomQ R (∅ : Set Y) p q n h).flip (Submodule.Quotient.mk z))
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  change capHomQ R ∅ p q n h (Submodule.Quotient.mk φ) (Submodule.Quotient.mk z) = 0 at hc
  rw [capHomQ_mk] at hc
  obtain ⟨u, hu⟩ := (mk_eq_zero_iff_exists _).1 hc
  refine mk_eq_zero_of_forall_pullCocycle hdisj hcov φ fun l ↦ ?_
  have hinj : Injective ((capHomQ R (∅ : Set (TopCat.of (V l))) p q n h).flip
      (Submodule.Quotient.mk (resCyc V l z))) := hV l
  refine (injective_iff_map_eq_zero _).1 hinj _ ?_
  change capHomQ R ∅ p q n h (Submodule.Quotient.mk _) (Submodule.Quotient.mk _) = 0
  rw [capHomQ_mk]
  refine (mk_eq_zero_iff_exists _).2 ⟨res R V l (q + 1) u, ?_⟩
  rw [← res_d, hu]
  exact restrict_capChain hdisj hcov p q n h φ.1 z.1 l

/-- Surjectivity half of Poincaré duality for a disjoint union. -/
theorem surjective_capHomQ_of_disjoint (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) (p q n : ℕ) (h : p + q = n) (z : Cyc (R := R) Y n)
    (hV : ∀ l, Surjective fun c ↦ capHomQ R (∅ : Set (TopCat.of (V l))) p q n h c
      (Submodule.Quotient.mk (resCyc V l z))) :
    Surjective fun c ↦ capHomQ R (∅ : Set Y) p q n h c (Submodule.Quotient.mk z) := by
  intro w
  obtain ⟨w', rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hl : ∀ l, ∃ φ : relCocycles R (∅ : Set (TopCat.of (V l))) p,
      ∃ u : (BM R (TopCat.of (V l))).X (q + 1),
        ((BM R (TopCat.of (V l))).d (q + 1) q).hom u =
          capChain R p q n h φ.1 (resCyc V l z).1 - (resCyc V l w').1 := by
    intro l
    obtain ⟨c, hc⟩ := hV l (Submodule.Quotient.mk (resCyc V l w'))
    obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    change capHomQ R ∅ p q n h (Submodule.Quotient.mk φ) (Submodule.Quotient.mk _) = _ at hc
    rw [capHomQ_mk] at hc
    exact ⟨φ, (mk_eq_mk_iff_exists _ _).1 hc⟩
  choose φ u hu using hl
  have hglue : glueCochain V (fun l ↦ (φ l).1) ∈ relCocycles R (∅ : Set Y) p := by
    refine ⟨mem_vanishing_empty _, ?_⟩
    change coboundary R p _ = 0
    rw [coboundary_glueCochain hdisj hcov]
    refine cochain_ext hdisj hcov fun l ↦ ?_
    rw [cochainPullback_glueCochain hdisj, map_zero]
    exact (φ l).2.2
  refine ⟨Submodule.Quotient.mk ⟨_, hglue⟩, ?_⟩
  change capHomQ R ∅ p q n h (Submodule.Quotient.mk _) (Submodule.Quotient.mk z) = _
  rw [capHomQ_mk]
  refine (mk_eq_mk_iff_exists _ _).2 ⟨glueChain V hdisj hcov u, chain_ext hdisj hcov fun l ↦ ?_⟩
  rw [res_d, res_glueChain, hu l, map_sub]
  have := restrict_capChain hdisj hcov p q n h (glueCochain V fun l ↦ (φ l).1) z.1 l
  rw [cochainPullback_glueCochain hdisj] at this
  rw [this]
  rfl

/-- **Poincaré duality for a disjoint union.** Let `Y` be the union of the pairwise disjoint open
sets `V l` and `z` a locally finite `n`-cycle of `Y`. If `[φ] ↦ [φ ∩ z|_{V l}]`,
`H^p(V l) → H_q(V l)`, is bijective for every `l`, then `[φ] ↦ [φ ∩ z]`, `H^p Y → H_q Y`, is
bijective. -/
theorem bijective_capHomQ_of_disjoint (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) (p q n : ℕ) (h : p + q = n) (z : Cyc (R := R) Y n)
    (hV : ∀ l, Bijective fun c ↦ capHomQ R (∅ : Set (TopCat.of (V l))) p q n h c
      (Submodule.Quotient.mk (resCyc V l z))) :
    Bijective fun c ↦ capHomQ R (∅ : Set Y) p q n h c (Submodule.Quotient.mk z) :=
  ⟨injective_capHomQ_of_disjoint hdisj hcov p q n h z fun l ↦ (hV l).1,
    surjective_capHomQ_of_disjoint hdisj hcov p q n h z fun l ↦ (hV l).2⟩

end duality

end PoincareAlexander

end MMP
