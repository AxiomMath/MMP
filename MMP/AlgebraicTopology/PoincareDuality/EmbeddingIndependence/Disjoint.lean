module

public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.ConvexOpen
public import MMP.AlgebraicTopology.BorelMoore.RestrictionFunctorial

/-!
# The disjoint-union step of Bredon's induction, at a restricted cycle

For a Hausdorff space `Y` and a locally finite `n`-cycle `z` of `Y`, the property of Bredon's
induction on open sets `U ⊆ Y` is `DualityAt U n z|_U` (`resCycOpen`). This file shows:

* `DualityAt` depends only on the homology class of the cycle (`DualityAt.of_mk_eq`) and is
  invariant under homeomorphisms (`DualityAt.of_homeomorph`);
* for open `U' ⊆ U`, the iterated restriction `(z|_U)|_{U'}` is homologous to `z|_{U'}`, read in
  the preimage of `U'` in `U` (`mk_resCycOpen_subOpens`, from the functoriality of restriction
  `borelMooreHomology.restrict_restrict_apply`), so `DualityAt U' z|_{U'}` gives `DualityAt` on
  the preimage (`dualityAt_subOpens`);
* `DualityAt` passes to disjoint unions of open sets, any index type (`dualityAt_of_disjoint`,
  from `bijective_capHomQ_of_disjoint`), hence to `⨆ U i` for pairwise disjoint opens `U i` of
  `Y` (`dualityAt_resCycOpen_iSup`): the disjoint-union hypothesis of `isOpen_induction`.
## Main results

* `MMP.PoincareAlexander.dualityAt_of_disjoint`
* `MMP.PoincareAlexander.dualityAt_resCycOpen_iSup`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Set Topology Function

universe u

namespace MMP

open MMP

namespace PoincareAlexander

open MMP.PoincareAlexander

open SingularCross SingularChain SingularCochain LocallyFiniteChain BorelMooreCross BorelMooreCap
  borelMooreHomology

variable {R : Type u} [CommRing R]

section transport

variable {Z Z' : TopCat.{u}}

/-- `DualityAt` depends only on the homology class of the cycle. -/
lemma DualityAt.of_mk_eq {n : ℕ} {w w' : Cyc (R := R) Z n}
    (hw : (Submodule.Quotient.mk w : HomQ (R := R) Z n) = Submodule.Quotient.mk w')
    (h : DualityAt Z n w) : DualityAt Z n w' := by
  refine ⟨fun p q hpq ↦ ?_, h.2.1, h.2.2⟩
  have := h.1 p q hpq
  rwa [hw] at this

/-- Push-forward preserves homology of cycles. -/
lemma mk_pushCyc_eq (f : Z ⟶ Z') (hf : IsProperMap f) {m : ℕ} {w w' : Cyc (R := R) Z m}
    (hw : (Submodule.Quotient.mk w : HomQ (R := R) Z m) = Submodule.Quotient.mk w') :
    (Submodule.Quotient.mk (pushCyc R f hf w) : HomQ (R := R) Z' m) =
      Submodule.Quotient.mk (pushCyc R f hf w') := by
  obtain ⟨u, hu⟩ := (mk_eq_mk_iff_exists _ _).1 hw
  refine (mk_eq_mk_iff_exists _ _).2 ⟨pushChain R f hf (m + 1) u, ?_⟩
  rw [← pushChain_d, hu, map_sub]
  rfl

/-- **`DualityAt` is invariant under homeomorphisms.** -/
theorem DualityAt.of_homeomorph (f : Z ⟶ Z') (g : Z' ⟶ Z) (hf : IsProperMap f)
    (hg : IsProperMap g) (hfg : f ≫ g = 𝟙 Z) (hgf : g ≫ f = 𝟙 Z') {n : ℕ}
    (w : Cyc (R := R) Z n) (h : DualityAt Z' n (pushCyc R f hf w)) : DualityAt Z n w :=
  ⟨fun p q hpq ↦ bijective_capHomQ_of_homeomorph f g hf hg hfg p q n hpq w (h.1 p q hpq),
    fun p hp ↦ subsingleton_relCohomology_of_homeomorph f g hfg (h.2.1 p hp),
    fun q hq ↦ subsingleton_homQ_of_homeomorph f g hf hg hfg (h.2.2 q hq)⟩

end transport

section restrict

variable {Y : TopCat.{u}} [T2Space Y]

/-- For open `U' ⊆ U ⊆ Y`, `(z|_U)|_{U'}` is homologous to `z|_{U'}`, read in the preimage of
`U'` in `U`. -/
lemma mk_resCycOpen_subOpens (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}
    (h : U' ≤ U) {n : ℕ} (z : Cyc (R := R) Y n) :
    (Submodule.Quotient.mk (resCycOpen R (subOpens U U') (resCycOpen R U z)) :
        HomQ (R := R) (TopCat.of (subOpens U U')) n) =
      Submodule.Quotient.mk (pushCyc R (subOpensMap U h) (isProperMap_subOpensMap U h)
        (resCycOpen R U' z)) := by
  set μ := (homologyEquiv R Y n).symm (Submodule.Quotient.mk z)
  have hμ : homologyEquiv R Y n μ = Submodule.Quotient.mk z := LinearEquiv.apply_symm_apply _ _
  have hU := homologyEquiv_restrict U μ z hμ
  have hUU' := homologyEquiv_restrict (subOpens U U') _ _ hU
  have hU' := homologyEquiv_restrict U' μ z hμ
  have key := restrict_restrict_apply R (ModuleCat.of R R) U h n μ
  refine hUU'.symm.trans ?_
  rw [key]
  set ν := (restrict R (ModuleCat.of R R) U' n).hom μ
  obtain ⟨y, hy⟩ : ∃ y, (homologyEquiv R (TopCat.of U') n).symm y = ν :=
    ⟨_, LinearEquiv.symm_apply_apply _ _⟩
  rw [← hy, LinearEquiv.apply_symm_apply] at hU'
  subst hU'
  rw [← hy, pushforward_eq_homologyMap]
  exact (LinearEquiv.eq_symm_apply _).1 (homologyMap_homologyEquiv_symm_mk R _ n _)

/-- `DualityAt U' z|_{U'}` gives `DualityAt` on the preimage of `U'` in `U ⊇ U'`, at
`(z|_U)|_{U'}`. -/
theorem dualityAt_subOpens (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}
    (h : U' ≤ U) {n : ℕ} (z : Cyc (R := R) Y n)
    (hU' : DualityAt (TopCat.of U') n (resCycOpen R U' z)) :
    DualityAt (TopCat.of (subOpens U U')) n (resCycOpen R (subOpens U U') (resCycOpen R U z)) := by
  have hfg : subOpensInv U h ≫ subOpensMap U h = 𝟙 _ := rfl
  have hgf : subOpensMap U h ≫ subOpensInv U h = 𝟙 _ := rfl
  have hInv : IsProperMap (subOpensInv U h) := by
    change IsProperMap (subOpensHomeo U h).symm
    exact (subOpensHomeo U h).symm.isProperMap
  refine DualityAt.of_homeomorph (subOpensInv U h) (subOpensMap U h) hInv
    (isProperMap_subOpensMap U h) hfg hgf _ ?_
  refine DualityAt.of_mk_eq (Eq.trans ?_
    (mk_pushCyc_eq (subOpensInv U h) hInv (mk_resCycOpen_subOpens U h z)).symm) hU'
  congr 1
  exact Subtype.ext (pushChain_pushChain_of_comp_eq_id _ _ _ _ hgf n _).symm

end restrict

section disjoint

variable {Y : TopCat.{u}} [T2Space Y] {ι : Type*} {V : ι → TopologicalSpace.Opens Y}

/-- **`DualityAt` for a disjoint union of open sets** (any index type). -/
theorem dualityAt_of_disjoint (hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)))
    (hcov : ∀ y, ∃ l, y ∈ V l) {n : ℕ} (z : Cyc (R := R) Y n)
    (hV : ∀ l, DualityAt (TopCat.of (V l)) n (resCyc V l z)) : DualityAt Y n z := by
  refine ⟨fun p q h ↦ bijective_capHomQ_of_disjoint hdisj hcov p q n h z fun l ↦ (hV l).1 p q h,
    fun p hp ↦ ⟨fun a b ↦ ?_⟩, fun q hq ↦ ⟨fun a b ↦ ?_⟩⟩
  · suffices ∀ c : relCohomology R (∅ : Set Y) p, c = 0 by rw [this a, this b]
    intro c
    obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    exact mk_eq_zero_of_forall_pullCocycle hdisj hcov φ fun l ↦
      ((hV l).2.1 p hp).elim _ _
  · suffices ∀ c : HomQ (R := R) Y q, c = 0 by rw [this a, this b]
    intro c
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    exact mk_eq_zero_of_forall_resCyc hdisj hcov w fun l ↦ ((hV l).2.2 q hq).elim _ _

/-- **The disjoint-union step of Bredon's induction at a restricted cycle**: for pairwise
disjoint open `U i ⊆ Y` with `DualityAt (U i) n z|_{U i}`, `DualityAt (⨆ U i) n z|_{⨆ U i}`. -/
theorem dualityAt_resCycOpen_iSup (U : ι → TopologicalSpace.Opens Y)
    (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set Y))) {n : ℕ} (z : Cyc (R := R) Y n)
    (hU : ∀ l, DualityAt (TopCat.of (U l)) n (resCycOpen R (U l) z)) :
    DualityAt (TopCat.of (iSup U : TopologicalSpace.Opens Y)) n
      (resCycOpen R (iSup U : TopologicalSpace.Opens Y) z) := by
  refine dualityAt_of_disjoint (V := fun l ↦ subOpens (iSup U) (U l)) ?_ ?_ _ fun l ↦
    dualityAt_subOpens (iSup U) (le_iSup U l) z (hU l)
  · intro l m hlm
    exact Set.disjoint_left.2 fun x hxl hxm ↦ Set.disjoint_left.1 (hdisj hlm) hxl hxm
  · intro y
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 y.2
    exact ⟨l, hl⟩

end disjoint

end PoincareAlexander

end MMP
