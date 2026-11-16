module

public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Convex
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderTransport
public import MMP.AlgebraicTopology.FundamentalClass.Restriction
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Poincaré duality for bounded open convex subsets of `ℝⁿ`

The base case of Bredon's induction for Poincaré duality on the open subsets of `ℝⁿ`
(`isOpen_induction`), with the family `𝔅` of bounded open convex sets: it is stable under
intersection, contains `∅`, and is a neighbourhood basis at every point.

Fix a locally finite `n`-cycle `z` of `ℝⁿ` representing a fundamental class `μ`. For an open
`U ⊆ ℝⁿ` let `z|_U` be its restriction (`resCycOpen`); it represents `μ|_U`
(`homologyEquiv_restrict`), a fundamental class of `U` (`IsFundamentalClass.restrict`).
For a nonempty bounded open convex `U`:

* `U ≃ₜ ℝⁿ` (`convexOpenHomeomorph`: Mathlib's gauge rescaling sends `U` onto the unit ball,
  which is homeomorphic to `ℝⁿ`); hence `H^p U = 0` for `p > 0` and `H_q U = 0` for `q ≠ n`
  (`subsingleton_relCohomology_of_homeomorph`, `subsingleton_homQ_of_homeomorph`);
* `U` is contractible (the straight-line contraction to a point of `U`) and connected, so by
  top-degree Poincaré duality on the manifold `U`, `r ↦ r [z|_U]` is a bijection `R ≃ H_n U`, and
  the degree-`0` duality holds (`bijective_capHomQ_zero_of_homotopy_const`).

For `U = ∅` every group vanishes.

## Main definitions

* `MMP.PoincareAlexander.resCycOpen`: restriction of a cycle to an open set.
* `MMP.PoincareAlexander.convexOpenHomeomorph`: `U ≃ₜ ℝⁿ`.
* `MMP.PoincareAlexander.convexContraction`: the straight-line contraction of a convex set onto
  one of its points.

## Main results

* `MMP.PoincareAlexander.dualityAt_resCycOpen_of_convex`: `DualityAt` for a bounded open
  convex `U ⊆ ℝⁿ` at the restriction of a fundamental cycle.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Metric

universe u

namespace MMP

namespace PoincareAlexander

open SingularCross SingularChain SingularCochain LocallyFiniteChain BorelMooreCross BorelMooreCap
  borelMooreHomology

section restrict

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} [T2Space Y]

variable (R) in
/-- The restriction `z|_U` of a locally finite cycle of `Y` to an open subset `U`. -/
def resCycOpen (U : TopologicalSpace.Opens Y) {n : ℕ} (z : Cyc (R := R) Y n) :
    Cyc (R := R) (TopCat.of U) n :=
  ⟨((restrictChainMap R (ModuleCat.of R R) U).f n).hom z.1,
    chainMap_mem_cyc R (restrictChainMap R (ModuleCat.of R R) U) z⟩

/-- The underlying chain of `z|_U` is the image of `z` under the restriction chain map. -/
lemma resCycOpen_coe (U : TopologicalSpace.Opens Y) {n : ℕ} (z : Cyc (R := R) Y n) :
    (resCycOpen R U z).1 = ((restrictChainMap R (ModuleCat.of R R) U).f n).hom z.1 :=
  rfl

/-- If `z` represents `μ`, then `z|_U` represents `μ|_U`. -/
lemma homologyEquiv_restrict (U : TopologicalSpace.Opens Y) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) Y n) (z : Cyc (R := R) Y n)
    (hzμ : homologyEquiv R Y n μ = Submodule.Quotient.mk z) :
    homologyEquiv R (TopCat.of U) n ((restrict R (ModuleCat.of R R) U n).hom μ) =
      Submodule.Quotient.mk (resCycOpen R U z) := by
  obtain ⟨w, rfl⟩ : ∃ w, (homologyEquiv R Y n).symm w = μ :=
    ⟨_, (homologyEquiv R Y n).symm_apply_apply μ⟩
  rw [LinearEquiv.apply_symm_apply] at hzμ
  subst hzμ
  exact (LinearEquiv.eq_symm_apply _).1
    (homologyMap_homologyEquiv_symm_mk R (restrictChainMap R (ModuleCat.of R R) U) n z)

end restrict

section empty

variable {R : Type u} [CommRing R] {Z : TopCat.{u}}

/-- The singular cohomology of an empty space vanishes in every degree. -/
lemma subsingleton_relCohomology_of_isEmpty [IsEmpty Z] (p : ℕ) :
    Subsingleton (relCohomology R (∅ : Set Z) p) := by
  have : IsEmpty (Simplex Z p) := ⟨fun σ ↦ IsEmpty.false (σ (Classical.arbitrary _))⟩
  have : Subsingleton (relCocycles R (∅ : Set Z) p) :=
    ⟨fun a b ↦ Subtype.ext (Subsingleton.elim _ _)⟩
  exact Quotient.instSubsingletonQuotient _

/-- The Borel–Moore homology of an empty space vanishes in every degree. -/
lemma subsingleton_homQ_of_isEmpty [IsEmpty Z] (q : ℕ) :
    Subsingleton (HomQ (R := R) Z q) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have hS : IsEmpty (Simp Z q) := ⟨fun σ ↦ by
    obtain ⟨y, -⟩ := nonempty_singularSimplexImage σ
    exact IsEmpty.false y⟩
  have : x = y := Subtype.ext (Subtype.ext (funext fun σ ↦ (hS.false σ).elim))
  rw [this]

/-- **`DualityAt` for the empty space**: every group vanishes. -/
theorem dualityAt_of_isEmpty [IsEmpty Z] (n : ℕ) (z : Cyc (R := R) Z n) : DualityAt Z n z := by
  refine ⟨fun p q _ ↦ ?_, fun p _ ↦ subsingleton_relCohomology_of_isEmpty p,
    fun q _ ↦ subsingleton_homQ_of_isEmpty q⟩
  have := subsingleton_relCohomology_of_isEmpty (R := R) (Z := Z) p
  have := subsingleton_homQ_of_isEmpty (R := R) (Z := Z) q
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end empty

section convex

variable {n : ℕ}

/-- A nonempty bounded open convex subset of `ℝⁿ` is carried onto the open unit ball by a
self-homeomorphism of `ℝⁿ`. -/
lemma exists_homeomorph_image_eq_ball {U : Set (Fin n → ℝ)} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hUne : U.Nonempty) (hUb : Bornology.IsBounded U) :
    ∃ h : (Fin n → ℝ) ≃ₜ (Fin n → ℝ), h '' U = ball 0 1 := by
  obtain ⟨h, hh, -⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hUc
    (by rwa [hUo.interior_eq]) hUb
  exact ⟨h, by rwa [hUo.interior_eq] at hh⟩

/-- A nonempty bounded open convex subset of `ℝⁿ` is homeomorphic to `ℝⁿ`. -/
def convexOpenHomeomorph {U : Set (Fin n → ℝ)} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hUne : U.Nonempty) (hUb : Bornology.IsBounded U) : U ≃ₜ (Fin n → ℝ) :=
  (((exists_homeomorph_image_eq_ball hUo hUc hUne hUb).choose.image U).trans
    (Homeomorph.setCongr (exists_homeomorph_image_eq_ball hUo hUc hUne hUb).choose_spec)).trans
    Homeomorph.unitBall.symm

/-- The straight-line contraction of a convex set onto one of its points. -/
def convexContraction {U : Set (Fin n → ℝ)} (hUc : Convex ℝ U) (x₀ : U) :
    TopCat.Homotopy (𝟙 (TopCat.of U)) (TopCat.ofHom (ContinuousMap.const (TopCat.of U) x₀)) where
  toFun p := ⟨(1 - (p.1 : ℝ)) • (p.2 : Fin n → ℝ) + (p.1 : ℝ) • (x₀ : Fin n → ℝ),
    hUc p.2.2 x₀.2 (by simp [p.1.2.2]) p.1.2.1 (by ring)⟩
  continuous_toFun := by fun_prop
  map_zero_left x := by ext; simp
  map_one_left x := by ext; simp

variable {R : Type} [CommRing R]

/-- **Poincaré duality for a bounded open convex `U ⊆ ℝⁿ`** at the restriction `z|_U` of a cycle
`z` representing a fundamental class `μ` of `ℝⁿ`. -/
theorem dualityAt_resCycOpen_of_convex
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (Fin n → ℝ)) n)
    (hμ : letI : ChartedSpace (Fin n → ℝ) (Fin n → ℝ) := chartedSpaceSelf _
      IsFundamentalClass R (Pi.basisFun ℝ (Fin n)) μ)
    (z : Cyc (R := R) (TopCat.of (Fin n → ℝ)) n)
    (hzμ : homologyEquiv R (TopCat.of (Fin n → ℝ)) n μ = Submodule.Quotient.mk z)
    (U : TopologicalSpace.Opens (TopCat.of (Fin n → ℝ))) (hUc : Convex ℝ (U : Set (Fin n → ℝ)))
    (hUb : Bornology.IsBounded (U : Set (Fin n → ℝ))) :
    DualityAt (TopCat.of U) n (resCycOpen R U z) := by
  rcases (U : Set (Fin n → ℝ)).eq_empty_or_nonempty with hUe | hUne
  · have : IsEmpty (TopCat.of U) := Set.isEmpty_coe_sort.2 hUe
    exact dualityAt_of_isEmpty n _
  let e := convexOpenHomeomorph U.isOpen hUc hUne hUb
  let f : TopCat.of U ⟶ TopCat.of (Fin n → ℝ) := TopCat.ofHom (e : C(U, Fin n → ℝ))
  let g : TopCat.of (Fin n → ℝ) ⟶ TopCat.of U := TopCat.ofHom (e.symm : C(Fin n → ℝ, U))
  have hfg : f ≫ g = 𝟙 _ := TopCat.ext fun x ↦ e.symm_apply_apply x
  have hcoh : ∀ p, 0 < p → Subsingleton (relCohomology R (∅ : Set (TopCat.of U)) p) :=
    fun p hp ↦ subsingleton_relCohomology_of_homeomorph f g hfg
      (subsingleton_relCohomology_euclidean n hp)
  have hhom : ∀ q, q ≠ n → Subsingleton (HomQ (R := R) (TopCat.of U) q) :=
    fun q hq ↦ subsingleton_homQ_of_homeomorph f g e.isProperMap e.symm.isProperMap hfg
      (subsingleton_homQ_euclidean hq)
  refine ⟨fun p q h ↦ ?_, fun p hp ↦ hcoh p (by omega), fun q hq ↦ hhom q (by omega)⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain rfl : n = q := by omega
    let x₀ : U := ⟨hUne.choose, hUne.choose_spec⟩
    refine bijective_capHomQ_zero_of_homotopy_const (x₀ : TopCat.of U) (convexContraction hUc x₀)
      n h _ ?_
    let : ChartedSpace (Fin n → ℝ) (Fin n → ℝ) := chartedSpaceSelf _
    have : ConnectedSpace U :=
      Subtype.connectedSpace ⟨hUne, hUc.isPreconnected⟩
    have hb := PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold (R := R)
      (Y := U) (Pi.basisFun ℝ (Fin n)) _ (hμ.restrict U)
    have : (fun r : R ↦ r • (Submodule.Quotient.mk (resCycOpen R U z) :
        HomQ (R := R) (TopCat.of U) n)) = homologyEquiv R (TopCat.of U) n ∘
          fun r : R ↦ r • (restrict R (ModuleCat.of R R) U n).hom μ := by
      funext r
      simp only [Function.comp_apply, map_smul, homologyEquiv_restrict U μ z hzμ]
      rfl
    rw [this]
    exact (homologyEquiv R (TopCat.of U) n).bijective.comp hb
  · have := hcoh p hp
    have := hhom q (by omega)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end convex

end PoincareAlexander

end MMP
