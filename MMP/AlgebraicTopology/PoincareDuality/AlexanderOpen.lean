module

public import MMP.AlgebraicTopology.PoincareDuality.AlexanderMayerVietoris
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderInduction
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderEuclidean

/-!
# Poincaré duality on the open subsets of a manifold

Bredon's induction (`isOpen_induction_chartedSpace`) run with the property
`U ↦ DualityAt U n z|_U`, for a fundamental class `μ` of a real `n`-manifold `Y` (Hausdorff,
second countable, modelled on a real normed space `H` with a basis of `n` vectors) represented by
the locally finite cycle `z`:

* bounded convex chart pieces are homeomorphic to `ℝⁿ` (`nonempty_homeomorph_euclidean_of_chart`),
  and `μ|_U` freely generates `H_n U` (top-degree Poincaré duality for the connected manifold `U`),
  so `DualityAt` holds there (`dualityAt_of_homeomorph_euclidean`,
  `dualityAt_resCycOpen_of_chart`);
* Mayer–Vietoris: `dualityAt_resCycOpen_sup` (from `dualityAt_of_mayerVietoris`, the open subsets
  of `Y` being normal);
* disjoint unions: `dualityAt_resCycOpen_iSup`.

Hence `DualityAt U n z|_U` for every open `U ⊆ Y` (`dualityAt_resCycOpen_of_isFundamentalClass`),
in particular `DualityAt Y n z` (`dualityAt_of_isFundamentalClass`): Poincaré duality
`H^p Y ≅ H_{n-p} Y`, `[φ] ↦ [φ ∩ μ]`, in the cocycle/cycle model, with no connectedness or
compactness hypothesis, for `R`, `Y : Type u` and `H : Type v` in arbitrary universes (the
comparison with `ℝⁿ` goes through `ULift.{u} (Fin n → ℝ)`, `dualityAt_ulift_euclidean`).

## Main results

* `MMP.PoincareAlexander.dualityAt_resCycOpen_of_isFundamentalClass`.
* `MMP.PoincareAlexander.dualityAt_of_isFundamentalClass`.

## References

* [G. Bredon, *Topology and Geometry*][bredon1993], VI.7.9, VI.8.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.36.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Set Function

universe u v

namespace MMP

namespace PoincareAlexander

open SingularChain SingularCochain BorelMooreCross BorelMooreCap borelMooreHomology

section euclidean

variable {R : Type u} [CommRing R]

/-- Pushing a cycle forward along a proper map commutes with scalar multiplication. -/
lemma pushCyc_smul {Z Z' : TopCat.{u}} (f : Z ⟶ Z') (hf : IsProperMap f) {m : ℕ} (r : R)
    (w : Cyc (R := R) Z m) : pushCyc R f hf (r • w) = r • pushCyc R f hf w :=
  Subtype.ext (map_smul _ _ _)

/-- If `f ≫ g = 𝟙 Z`, pushing a cycle forward along `f` and then along `g` returns it. -/
lemma pushCyc_pushCyc {Z Z' : TopCat.{u}} (f : Z ⟶ Z') (g : Z' ⟶ Z) (hf : IsProperMap f)
    (hg : IsProperMap g) (hfg : f ≫ g = 𝟙 Z) {m : ℕ} (w : Cyc (R := R) Z m) :
    pushCyc R g hg (pushCyc R f hf w) = w :=
  Subtype.ext (pushChain_pushChain_of_comp_eq_id f g hf hg hfg m w.1)

/-- The homology class of `r • w` is `r` times the homology class of the cycle `w`. -/
lemma mk_smul_cyc {Z : TopCat.{u}} {m : ℕ} (r : R) (w : Cyc (R := R) Z m) :
    (Submodule.Quotient.mk (r • w) : HomQ (R := R) Z m) =
      r • (Submodule.Quotient.mk w : HomQ (R := R) Z m) :=
  rfl

/-- The homology class of the pushforward of `r • w` along a proper map is `r` times the class
of the pushforward of `w`. -/
lemma mk_pushCyc_smul {Z Z' : TopCat.{u}} (f : Z ⟶ Z') (hf : IsProperMap f) {m : ℕ} (r : R)
    (w : Cyc (R := R) Z m) :
    (Submodule.Quotient.mk (pushCyc R f hf (r • w)) : HomQ (R := R) Z' m) =
      r • (Submodule.Quotient.mk (pushCyc R f hf w) : HomQ (R := R) Z' m) := by
  rw [pushCyc_smul]
  rfl

/-- **Poincaré duality for a space homeomorphic to `ℝⁿ`**, at every cycle `z` such that
`r ↦ r [z]` is a bijection `R ≃ H_n Z`. -/
theorem dualityAt_of_homeomorph_euclidean {Z : TopCat.{u}} {n : ℕ} (f : Z ≃ₜ ULiftEuclidean.{u} n)
    (z : Cyc (R := R) Z n)
    (hz : Bijective fun r : R ↦ r • (Submodule.Quotient.mk z : HomQ (R := R) Z n)) :
    DualityAt Z n z := by
  let F : Z ⟶ TopCat.of (ULiftEuclidean.{u} n) := TopCat.ofHom ⟨f, f.continuous⟩
  let G : TopCat.of (ULiftEuclidean.{u} n) ⟶ Z := TopCat.ofHom ⟨f.symm, f.symm.continuous⟩
  have hF : IsProperMap F := f.isProperMap
  have hG : IsProperMap G := f.symm.isProperMap
  have hFG : F ≫ G = 𝟙 Z := TopCat.ext fun x ↦ f.symm_apply_apply x
  have hGF : G ≫ F = 𝟙 _ := TopCat.ext fun x ↦ f.apply_symm_apply x
  refine DualityAt.of_homeomorph F G hF hG hFG hGF z (dualityAt_ulift_euclidean n _ ⟨?_, ?_⟩)
  · intro r r' hrr'
    refine hz.1 ?_
    have h := mk_pushCyc_eq G hG
      ((mk_pushCyc_smul F hF r z).trans (hrr'.trans (mk_pushCyc_smul F hF r' z).symm))
    rw [pushCyc_pushCyc F G hF hG hFG, pushCyc_pushCyc F G hF hG hFG] at h
    exact (mk_smul_cyc r z).symm.trans (h.trans (mk_smul_cyc r' z))
  · intro y
    obtain ⟨y', rfl⟩ : ∃ y' : Cyc (R := R) (TopCat.of (ULiftEuclidean.{u} n)) n,
        Submodule.Quotient.mk y' = y := Submodule.Quotient.mk_surjective _ y
    obtain ⟨r, hr⟩ := hz.2 (Submodule.Quotient.mk (pushCyc R G hG y'))
    refine ⟨r, ?_⟩
    have h := mk_pushCyc_eq F hF ((mk_smul_cyc r z).trans hr)
    rw [pushCyc_pushCyc G F hG hF hGF] at h
    exact (mk_pushCyc_smul F hF r z).symm.trans h

end euclidean

section chart

variable {R : Type u} [CommRing R] {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Y : Type u} [TopologicalSpace Y]

/-- A nonempty open set inside a chart domain with bounded convex image is homeomorphic to
`ℝⁿ`. -/
theorem nonempty_homeomorph_euclidean_of_chart {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (e : OpenPartialHomeomorph Y H) {U : Set Y} (hU : IsOpen U) (hUe : U ⊆ e.source)
    (hc : Convex ℝ (e '' U)) (hb : Bornology.IsBounded (e '' U)) (hne : U.Nonempty) :
    Nonempty (U ≃ₜ (Fin n → ℝ)) := by
  have : FiniteDimensional ℝ H := Module.Basis.finiteDimensional_of_finite b
  let L : H ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  exact ⟨(e.homeomorphOfImageSubsetSource hUe rfl).trans ((L.toHomeomorph.image _).trans
    (convexOpenHomeomorph (L.toHomeomorph.isOpenMap _ (e.isOpen_image_of_subset_source hU hUe))
      (hc.linear_image (L : H →ₗ[ℝ] (Fin n → ℝ))) ((hne.image _).image _)
      ((L : H →L[ℝ] (Fin n → ℝ)).lipschitzWith.isBounded_image hb)))⟩

variable [T2Space Y] [SecondCountableTopology Y] [ChartedSpace H Y]

/-- **The convex case of Bredon's induction on a manifold.** For a fundamental class `μ`
(represented by the cycle `z`) of a manifold `Y` and an open set `U` inside a chart domain with
bounded convex image, `DualityAt U n z|_U`. -/
theorem dualityAt_resCycOpen_of_chart {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) n) (hμ : IsFundamentalClass R b μ)
    (z : Cyc (R := R) (TopCat.of Y) n)
    (hzμ : homologyEquiv R (TopCat.of Y) n μ = Submodule.Quotient.mk z)
    (e : OpenPartialHomeomorph Y H) (U : TopologicalSpace.Opens (TopCat.of Y))
    (hUe : (U : Set Y) ⊆ e.source) (hc : Convex ℝ (e '' U)) (hb : Bornology.IsBounded (e '' U)) :
    DualityAt (TopCat.of U) n (resCycOpen R U z) := by
  rcases (U : Set Y).eq_empty_or_nonempty with hUe' | hne
  · have : IsEmpty (TopCat.of U) := by
      change IsEmpty (U : Set Y)
      rw [hUe']
      infer_instance
    exact dualityAt_of_isEmpty n _
  obtain ⟨f⟩ := nonempty_homeomorph_euclidean_of_chart b e U.isOpen hUe hc hb hne
  refine dualityAt_of_homeomorph_euclidean (Z := TopCat.of U) (f.trans Homeomorph.ulift.symm) _ ?_
  have : ConnectedSpace U := f.symm.surjective.connectedSpace f.symm.continuous
  have hres := homologyEquiv_restrict U μ z hzμ
  have : (fun r : R ↦ r • (Submodule.Quotient.mk (resCycOpen R U z) :
      HomQ (R := R) (TopCat.of U) n)) =
      homologyEquiv R (TopCat.of U) n ∘ fun r : R ↦
        r • (restrict R (ModuleCat.of R R) U n).hom μ := by
    funext r
    simp only [Function.comp_apply, map_smul, hres]
    rfl
  rw [this]
  exact (homologyEquiv R (TopCat.of U) n).bijective.comp
    (PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold (R := R) (Y := U) b _
      (hμ.restrict U))

end chart

section induction

variable {R : Type u} [CommRing R] {Y : Type u} [TopologicalSpace Y] [T2Space Y]

/-- **The Mayer–Vietoris step of Bredon's induction at a restricted cycle**: `DualityAt` on
`U`, `V`, `U ⊓ V` at the restrictions of `z` gives it on `U ⊔ V`. -/
theorem dualityAt_resCycOpen_sup [RegularSpace Y] [SecondCountableTopology Y] {n : ℕ}
    (z : Cyc (R := R) (TopCat.of Y) n) (U V : TopologicalSpace.Opens (TopCat.of Y))
    (hU : DualityAt (TopCat.of U) n (resCycOpen R U z))
    (hV : DualityAt (TopCat.of V) n (resCycOpen R V z))
    (hUV : DualityAt (TopCat.of ↥(U ⊓ V)) n (resCycOpen R (U ⊓ V) z)) :
    DualityAt (TopCat.of ↥(U ⊔ V)) n (resCycOpen R (U ⊔ V) z) := by
  refine dualityAt_of_mayerVietoris (Y := TopCat.of ↥(U ⊔ V)) (A := subOpens (U ⊔ V) U)
    (B := subOpens (U ⊔ V) V) ?_ _ (dualityAt_subOpens (U ⊔ V) le_sup_left z hU)
    (dualityAt_subOpens (U ⊔ V) le_sup_right z hV)
    (dualityAt_subOpens (U ⊔ V) (inf_le_left.trans le_sup_left) z hUV)
  ext x
  simp only [mem_union, mem_univ, iff_true]
  exact x.2

variable {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [SecondCountableTopology Y]
  [ChartedSpace H Y]

/-- **Poincaré duality on every open subset of a manifold**, in the cocycle/cycle model: for a
fundamental class `μ` of `Y`, represented by the locally finite cycle `z`, and every open
`U ⊆ Y`, `[φ] ↦ [φ ∩ z|_U]` is bijective `H^p U → H_{n-p} U`, and `H^p U = 0 = H_p U` for
`p > n`. Bredon's induction (`isOpen_induction_chartedSpace`) from the bounded convex chart
pieces (`dualityAt_resCycOpen_of_chart`), through Mayer–Vietoris (`dualityAt_resCycOpen_sup`)
and disjoint unions (`dualityAt_resCycOpen_iSup`). -/
theorem dualityAt_resCycOpen_of_isFundamentalClass {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) n) (hμ : IsFundamentalClass R b μ)
    (z : Cyc (R := R) (TopCat.of Y) n)
    (hzμ : homologyEquiv R (TopCat.of Y) n μ = Submodule.Quotient.mk z)
    (U : TopologicalSpace.Opens (TopCat.of Y)) :
    DualityAt (TopCat.of U) n (resCycOpen R U z) := by
  have : FiniteDimensional ℝ H := Module.Basis.finiteDimensional_of_finite b
  have : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace H Y
  refine isOpen_induction_chartedSpace (H := H) (P := fun s ↦ ∀ hs : IsOpen s,
    DualityAt (TopCat.of (⟨s, hs⟩ : TopologicalSpace.Opens (TopCat.of Y))) n
      (resCycOpen R ⟨s, hs⟩ z)) ?_ ?_ ?_ ?_ U.isOpen U.isOpen
  · intro e _ s _ hse hc hb hs'
    exact dualityAt_resCycOpen_of_chart b μ hμ z hzμ e ⟨s, hs'⟩ hse hc hb
  · intro hs
    have : IsEmpty (TopCat.of (⟨∅, hs⟩ : TopologicalSpace.Opens (TopCat.of Y))) := by
      change IsEmpty (∅ : Set Y)
      infer_instance
    exact dualityAt_of_isEmpty n _
  · intro s t hs ht hPs hPt hPst _
    exact dualityAt_resCycOpen_sup z ⟨s, hs⟩ ⟨t, ht⟩ (hPs hs) (hPt ht) (hPst (hs.inter ht))
  · intro s hs hdisj hP hs'
    have heq : (⟨⋃ i, s i, hs'⟩ : TopologicalSpace.Opens (TopCat.of Y)) =
        ⨆ i, (⟨s i, hs i⟩ : TopologicalSpace.Opens (TopCat.of Y)) := by
      ext x
      simp
    rw [heq]
    exact dualityAt_resCycOpen_iSup (fun i ↦ (⟨s i, hs i⟩ : TopologicalSpace.Opens _))
      hdisj z fun i ↦ hP i (hs i)

/-- **Poincaré duality for a manifold**, in the cocycle/cycle model: for a fundamental class `μ`
of `Y` represented by the locally finite cycle `z`, `DualityAt Y n z`. -/
theorem dualityAt_of_isFundamentalClass {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) n) (hμ : IsFundamentalClass R b μ)
    (z : Cyc (R := R) (TopCat.of Y) n)
    (hzμ : homologyEquiv R (TopCat.of Y) n μ = Submodule.Quotient.mk z) :
    DualityAt (TopCat.of Y) n z := by
  have : FiniteDimensional ℝ H := Module.Basis.finiteDimensional_of_finite b
  have : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace H Y
  have h := dualityAt_resCycOpen_of_isFundamentalClass b μ hμ z hzμ ⊤
  exact dualityAt_of_mayerVietoris (A := ⊤) (B := ⊤) (by simp) z h h
    (dualityAt_resCycOpen_of_isFundamentalClass b μ hμ z hzμ (⊤ ⊓ ⊤))

end induction

end PoincareAlexander

end MMP
