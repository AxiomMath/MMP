module

public import MMP.AlgebraicTopology.PoincareDuality.AlexanderDisjoint

/-!
# Transport of Poincaré duality along homeomorphisms

Let `f : Z → Z'` be a homeomorphism (a map of `TopCat` with a two-sided inverse `g`) and `w` a
locally finite `n`-cycle of `Z`. The cap product is natural on chains:
`f_♯ (f^♯ φ ∩ w) = φ ∩ f_♯ w` (`BorelMooreCap.chainMap_capChain`), and `f^♯`, `f_♯` are invertible
with inverses `g^♯`, `g_♯`. Hence if `[φ] ↦ [φ ∩ f_♯ w]`, `H^p Z' → H_q Z'`, is bijective, so is
`[φ] ↦ [φ ∩ w]`, `H^p Z → H_q Z`. The same holds for the vanishing of `H^p` and of `H_q`.

## Main results

* `MMP.PoincareAlexander.bijective_capHomQ_of_homeomorph`: if capping with `f_♯ w` is bijective
  on `Z'`, then capping with `w` is bijective on `Z`.
* `MMP.PoincareAlexander.subsingleton_relCohomology_of_homeomorph`: vanishing of `H^p` transports
  along a homeomorphism.
* `MMP.PoincareAlexander.subsingleton_homQ_of_homeomorph`: vanishing of `H_q` transports along a
  homeomorphism.
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

variable {R : Type u} [CommRing R] {Z Z' : TopCat.{u}}

section maps

variable (R) in
/-- Push-forward of locally finite chains along a proper map, in degree `m`. -/
abbrev pushChain (f : Z ⟶ Z') (hf : IsProperMap f) (m : ℕ) : (BM R Z).X m →ₗ[R] (BM R Z').X m :=
  ((chainMap R (ModuleCat.of R R) f hf).f m).hom

/-- If `f ≫ g = 𝟙 Z`, then `g_♯ (f_♯ c) = c` for every locally finite chain `c` of `Z`. -/
lemma pushChain_pushChain_of_comp_eq_id (f : Z ⟶ Z') (g : Z' ⟶ Z) (hf : IsProperMap f)
    (hg : IsProperMap g) (hfg : f ≫ g = 𝟙 Z) (m : ℕ) (c : (BM R Z).X m) :
    pushChain R g hg m (pushChain R f hf m c) = c := by
  have key : ∀ (k : Z ⟶ Z) (hk : IsProperMap k), k = 𝟙 Z →
      chainMap R (ModuleCat.of R R) k hk = 𝟙 _ := by
    rintro k hk rfl
    exact chainMap_id R (ModuleCat.of R R)
  simpa using congrArg (fun φ ↦ (φ.f m).hom c)
    ((chainMap_comp R (ModuleCat.of R R) f g hf hg).symm.trans (key _ _ hfg))

/-- Push-forward of locally finite chains commutes with the boundary. -/
lemma pushChain_d (f : Z ⟶ Z') (hf : IsProperMap f) (m : ℕ) (c : (BM R Z).X (m + 1)) :
    pushChain R f hf m (((BM R Z).d (m + 1) m).hom c) =
      ((BM R Z').d (m + 1) m).hom (pushChain R f hf (m + 1) c) := by
  have := congrArg (fun φ ↦ φ.hom c) ((chainMap R (ModuleCat.of R R) f hf).comm (m + 1) m)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this.symm

/-- If `f ≫ g = 𝟙 Z`, then `f^♯ (g^♯ φ) = φ` for every cochain `φ` of `Z`. -/
lemma cochainPullback_cochainPullback_of_comp_eq_id (f : Z ⟶ Z') (g : Z' ⟶ Z)
    (hfg : f ≫ g = 𝟙 Z) {p : ℕ} (φ : Simplex Z p → R) :
    cochainPullback R f p (cochainPullback R g p φ) = φ := by
  funext τ
  rw [cochainPullback_apply, cochainPullback_apply]
  congr 1
  ext t
  change (f ≫ g).hom (τ t) = τ t
  rw [hfg]
  rfl

variable (R) in
/-- The push-forward of a cycle. -/
def pushCyc (f : Z ⟶ Z') (hf : IsProperMap f) {m : ℕ} (w : Cyc (R := R) Z m) :
    Cyc (R := R) Z' m :=
  ⟨pushChain R f hf m w.1, chainMap_mem_cyc R _ w⟩

variable (R) in
/-- The pull-back of an absolute cocycle. -/
def pullCoc (f : Z ⟶ Z') {p : ℕ} (φ : relCocycles R (∅ : Set Z') p) :
    relCocycles R (∅ : Set Z) p :=
  ⟨cochainPullback R f p φ.1, cochainPullback_mem_relCocycles _ (empty_subset _) φ.2⟩

/-- If `f ≫ g = 𝟙 Z`, then `f^♯ (g^♯ φ) = φ` for every absolute cocycle `φ` of `Z`. -/
lemma pullCoc_pullCoc_of_comp_eq_id (f : Z ⟶ Z') (g : Z' ⟶ Z) (hfg : f ≫ g = 𝟙 Z) {p : ℕ}
    (φ : relCocycles R (∅ : Set Z) p) : pullCoc R f (pullCoc R g φ) = φ :=
  Subtype.ext (cochainPullback_cochainPullback_of_comp_eq_id f g hfg φ.1)

/-- Naturality of the cap product: `f_♯ (f^♯ φ ∩ w) = φ ∩ f_♯ w`. -/
lemma pushChain_capChain_pullCoc (f : Z ⟶ Z') (hf : IsProperMap f) (p q n : ℕ) (h : p + q = n)
    (φ : relCocycles R (∅ : Set Z') p) (w : Cyc (R := R) Z n) :
    pushChain R f hf q (capChain R p q n h (pullCoc R f φ).1 w.1) =
      capChain R p q n h φ.1 (pushCyc R f hf w).1 :=
  chainMap_capChain f hf p q n h φ.1 w.1

/-- The pull-back of a cocycle whose cohomology class vanishes has vanishing cohomology class. -/
lemma mk_pullCoc_eq_zero (f : Z ⟶ Z') {p : ℕ} (φ : relCocycles R (∅ : Set Z') p)
    (hφ : (Submodule.Quotient.mk φ : relCohomology R (∅ : Set Z') p) = 0) :
    (Submodule.Quotient.mk (pullCoc R f φ) : relCohomology R (∅ : Set Z) p) = 0 := by
  have hφ' : φ.1 ∈ relCoboundaries R (∅ : Set Z') p :=
    (Submodule.Quotient.mk_eq_zero ((relCoboundaries R (∅ : Set Z') p).comap
      (relCocycles R (∅ : Set Z') p).subtype)).1 hφ
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  change cochainPullback R f p φ.1 ∈ relCoboundaries R ∅ p
  cases p with
  | zero =>
    rw [(Submodule.mem_bot R).1 hφ', map_zero]
    exact Submodule.zero_mem _
  | succ p =>
    obtain ⟨ψ, -, hψ⟩ := hφ'
    exact ⟨cochainPullback R f p ψ, mem_vanishing_empty _, by
      rw [coboundary_cochainPullback, hψ]⟩

end maps

variable (f : Z ⟶ Z') (g : Z' ⟶ Z) (hf : IsProperMap f) (hg : IsProperMap g)
  (hfg : f ≫ g = 𝟙 Z) (hgf : g ≫ f = 𝟙 Z')

include hfg in
/-- If capping with `f_♯ w` is injective on `Z'`, then capping with `w` is injective on `Z`. -/
theorem injective_capHomQ_of_homeomorph (p q n : ℕ) (h : p + q = n) (w : Cyc (R := R) Z n)
    (hw : Injective fun c ↦ capHomQ R (∅ : Set Z') p q n h c
      (Submodule.Quotient.mk (pushCyc R f hf w))) :
    Injective fun c ↦ capHomQ R (∅ : Set Z) p q n h c (Submodule.Quotient.mk w) := by
  change Injective ((capHomQ R (∅ : Set Z) p q n h).flip (Submodule.Quotient.mk w))
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  change capHomQ R ∅ p q n h (Submodule.Quotient.mk φ) (Submodule.Quotient.mk w) = 0 at hc
  rw [capHomQ_mk] at hc
  obtain ⟨u, hu⟩ := (mk_eq_zero_iff_exists _).1 hc
  have h₀ := (injective_iff_map_eq_zero ((capHomQ R (∅ : Set Z') p q n h).flip
      (Submodule.Quotient.mk (pushCyc R f hf w)))).1 hw
    (Submodule.Quotient.mk (pullCoc R g φ)) (by
      change capHomQ R ∅ p q n h (Submodule.Quotient.mk _) (Submodule.Quotient.mk _) = 0
      rw [capHomQ_mk]
      refine (mk_eq_zero_iff_exists _).2 ⟨pushChain R f hf (q + 1) u, ?_⟩
      rw [← pushChain_d, hu]
      change _ = capChain R p q n h (pullCoc R g φ).1 (pushCyc R f hf w).1
      rw [← pushChain_capChain_pullCoc f hf p q n h (pullCoc R g φ) w,
        pullCoc_pullCoc_of_comp_eq_id f g hfg])
  rw [← pullCoc_pullCoc_of_comp_eq_id f g hfg φ]
  exact mk_pullCoc_eq_zero f _ h₀

include hg hfg in
/-- If capping with `f_♯ w` is surjective on `Z'`, then capping with `w` is surjective on `Z`. -/
theorem surjective_capHomQ_of_homeomorph (p q n : ℕ) (h : p + q = n) (w : Cyc (R := R) Z n)
    (hw : Surjective fun c ↦ capHomQ R (∅ : Set Z') p q n h c
      (Submodule.Quotient.mk (pushCyc R f hf w))) :
    Surjective fun c ↦ capHomQ R (∅ : Set Z) p q n h c (Submodule.Quotient.mk w) := by
  intro x
  obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨c, hc⟩ := hw (Submodule.Quotient.mk (pushCyc R f hf x'))
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  change capHomQ R ∅ p q n h (Submodule.Quotient.mk φ) (Submodule.Quotient.mk _) = _ at hc
  rw [capHomQ_mk] at hc
  obtain ⟨u, hu⟩ := (mk_eq_mk_iff_exists _ _).1 hc
  refine ⟨Submodule.Quotient.mk (pullCoc R f φ), ?_⟩
  change capHomQ R ∅ p q n h (Submodule.Quotient.mk _) (Submodule.Quotient.mk w) = _
  rw [capHomQ_mk]
  refine (mk_eq_mk_iff_exists _ _).2 ⟨pushChain R g hg (q + 1) u, ?_⟩
  rw [← pushChain_d, hu, map_sub]
  change pushChain R g hg q (capChain R p q n h φ.1 (pushCyc R f hf w).1) -
      pushChain R g hg q (pushChain R f hf q x'.1) =
    capChain R p q n h (pullCoc R f φ).1 w.1 - (show (BM R Z).X q from x'.1)
  rw [← pushChain_capChain_pullCoc f hf p q n h φ w,
    pushChain_pushChain_of_comp_eq_id f g hf hg hfg]
  congr 1
  exact pushChain_pushChain_of_comp_eq_id f g hf hg hfg q x'.1

include hg hfg in
/-- **Transport of duality along a homeomorphism.** -/
theorem bijective_capHomQ_of_homeomorph (p q n : ℕ) (h : p + q = n) (w : Cyc (R := R) Z n)
    (hw : Bijective fun c ↦ capHomQ R (∅ : Set Z') p q n h c
      (Submodule.Quotient.mk (pushCyc R f hf w))) :
    Bijective fun c ↦ capHomQ R (∅ : Set Z) p q n h c (Submodule.Quotient.mk w) :=
  ⟨injective_capHomQ_of_homeomorph f g hf hfg p q n h w hw.1,
    surjective_capHomQ_of_homeomorph f g hf hg hfg p q n h w hw.2⟩

include hfg in
/-- Vanishing of cohomology is invariant under homeomorphisms. -/
theorem subsingleton_relCohomology_of_homeomorph {p : ℕ}
    (h : Subsingleton (relCohomology R (∅ : Set Z') p)) :
    Subsingleton (relCohomology R (∅ : Set Z) p) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [← pullCoc_pullCoc_of_comp_eq_id f g hfg φ]
  exact mk_pullCoc_eq_zero f _ (Subsingleton.elim _ _)

include hf hg hfg in
/-- Vanishing of Borel–Moore homology is invariant under homeomorphisms. -/
theorem subsingleton_homQ_of_homeomorph {q : ℕ} (h : Subsingleton (HomQ (R := R) Z' q)) :
    Subsingleton (HomQ (R := R) Z q) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨u, hu⟩ := (mk_eq_zero_iff_exists (pushCyc R f hf x)).1 (h.allEq _ _)
  refine (mk_eq_zero_iff_exists x).2 ⟨pushChain R g hg (q + 1) u, ?_⟩
  rw [← pushChain_d, hu]
  exact pushChain_pushChain_of_comp_eq_id f g hf hg hfg q x.1

end PoincareAlexander

end MMP
