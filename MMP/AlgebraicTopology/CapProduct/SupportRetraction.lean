module

public import MMP.AlgebraicTopology.CapProduct.Support
public import MMP.AlgebraicTopology.BorelMoore.ProperHomotopy
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ProperNeighbourhoodRetractHomotopy
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ProperNeighbourhoodRetract
/-!
# The cap product with values in `H_{k-j} X` (Fulton, §19.1)

Let `X` be a closed subset of a space `Y`. For a closed neighbourhood `N` of `X` with a proper
retraction `r : N → X`, the cap product `H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} X` of [BT] 3.1.7 is
`c ∩ a = r_* (c ∩_N a)`, with `c ∩_N a ∈ H_{k-j} N` the neighbourhood cap product. It is
independent of `(N, r)` when `X` has arbitrarily small proper neighbourhood deformations: given
two retractions `r`, `r'`, take a deformation `G : L × [0, 1] → N ∩ N'` from the inclusion to a
retraction `s`; then `r ∘ G` and `r' ∘ G` are proper homotopies `r|_L ≃ s ≃ r'|_L`, and Borel–Moore
push-forward is invariant under proper homotopy; shrinking `N` to `L` does not change the cap
product. The same `G` shows that the push-forward of `c ∩ a` to `Y` is the cap product of `Y`.

Some hypothesis on `X` is forced: for the Warsaw circle `W ⊆ ℝ²`, `H^1(ℝ², ℝ² - W) = ℤ` while
`H_1 W = 0` for locally finite singular chains, so no cap product into `H_* W` satisfies
Poincaré–Alexander duality.

## Main definitions

* `MMP.HasProperNeighbourhoodDeformations`: the setting of Fulton §19.1.
* `MMP.borelMooreHomology.capProductSupport`:
  `∩ : H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} X`.
* `MMP.borelMooreHomology.capProductSupportPullback`:
  `c ∩ a = f^* c ∩ a ∈ H_{k-j}(f⁻¹ X)`.

## Main results

* `MMP.hasProperNeighbourhoodDeformations_of_isClosedEmbedding`,
  `MMP.UnderlyingSpace.hasProperNeighbourhoodDeformations`: Fulton's setting.
* `MMP.borelMooreHomology.capProductAlong_retraction_eq`: independence of the
  retraction.
* `MMP.borelMooreHomology.capProductSupport_eq_capProductAlong`.
* `MMP.borelMooreHomology.pushforward_subsetInclusion_capProductSupport`:
  forgetting the support.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* W. Fulton, R. MacPherson, *Categorical framework for the study of singular spaces*, 3.1.7.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology unitInterval

universe u

namespace MMP

open MMP

namespace borelMooreHomology

variable (R : Type u) [CommRing R]

/-- A proper homotopy `G : L × [0, 1] → Y` with values in `N`, from the inclusion of `L ⊆ N` to
a map `s : L → X`, followed by a retraction `r : N → X`, joins `r|_L` to `s`; so they induce
the same push-forward. -/
lemma pushforward_retraction_eq_of_homotopy {Y : TopCat.{u}} {X N L : Set Y} (hL : IsClosed L)
    (hLN : L ⊆ N) (r : C(N, X)) (hr : IsProperMap r)
    (hrX : ∀ y : N, (y : Y) ∈ X → (r y : Y) = y) (s : C(L, X)) (hs : IsProperMap s)
    (G : C(L × I, Y)) (hG : IsProperMap G) (hG0 : ∀ y, G (y, 0) = y) (hG1 : ∀ y, G (y, 1) = s y)
    (hGN : ∀ q, G q ∈ N) (j : ℤ) :
    pushforward R (ModuleCat.of R R) (subsetInclusionOfSubset hLN ≫ TopCat.ofHom r)
        (hr.comp (isProperMap_subsetInclusionOfSubset hL hLN)) j =
      pushforward R (ModuleCat.of R R) (TopCat.ofHom s) hs j := by
  let GN : C(L × I, N) := ⟨fun q ↦ ⟨G q, hGN q⟩, G.continuous.subtype_mk _⟩
  let H : TopCat.Homotopy (subsetInclusionOfSubset hLN ≫ TopCat.ofHom r) (TopCat.ofHom s) :=
    { toFun := fun p ↦ r (GN (p.2, p.1))
      continuous_toFun := r.continuous.comp (GN.continuous.comp continuous_swap)
      map_zero_left := fun y ↦ by
        change r (GN (y, 0)) = r ⟨y, hLN y.2⟩
        congr 1
        exact Subtype.ext (hG0 y)
      map_one_left := fun y ↦ by
        change r (GN (y, 1)) = s y
        have e : GN (y, 1) = ⟨s y, hG1 y ▸ hGN (y, 1)⟩ := Subtype.ext (hG1 y)
        rw [e]
        exact Subtype.ext (hrX _ (s y).2) }
  exact pushforward_eq_of_properHomotopy R _ _ hs H
    (hr.comp ((isProperMap_of_comp_of_inj GN.continuous continuous_subtype_val hG
      Subtype.val_injective).comp (Homeomorph.prodComm I L).isProperMap)) j

/-- The inclusion `L ⊆ Y` is properly homotopic to `ι_X ∘ s` for a proper homotopy
`G : L × [0, 1] → Y` from the inclusion to `s : L → X`; so they push forward alike. -/
lemma pushforward_subsetInclusion_eq_of_homotopy {Y : TopCat.{u}} {X L : Set Y} (hX : IsClosed X)
    (hL : IsClosed L) (s : C(L, X)) (hs : IsProperMap s) (G : C(L × I, Y)) (hG : IsProperMap G)
    (hG0 : ∀ y, G (y, 0) = y) (hG1 : ∀ y, G (y, 1) = s y) (j : ℤ) :
    pushforward R (ModuleCat.of R R) (subsetInclusion L) (isProperMap_subsetInclusion hL) j =
      pushforward R (ModuleCat.of R R) (TopCat.ofHom s ≫ subsetInclusion X)
        ((isProperMap_subsetInclusion hX).comp hs) j := by
  let H : TopCat.Homotopy (subsetInclusion L) (TopCat.ofHom s ≫ subsetInclusion X) :=
    { toFun := fun p ↦ G (p.2, p.1)
      continuous_toFun := G.continuous.comp continuous_swap
      map_zero_left := hG0
      map_one_left := hG1 }
  exact pushforward_eq_of_properHomotopy R _ _ _ H
    (hG.comp (Homeomorph.prodComm I L).isProperMap) j

end borelMooreHomology

/-- A subset `X` of a space `Y` has *arbitrarily small proper neighbourhood deformations* if
inside every neighbourhood `M` of `X` there are a closed neighbourhood `N` of `X`, a proper
retraction `r : N → X`, and a proper homotopy `G : N × [0, 1] → Y` with values in `M` from the
inclusion of `N` to `r`, fixing `X` at every time (a deformation retraction of `N` onto `X`
inside `M`). This is the setting of Fulton §19.1 ([BT] 3.1.7): it holds for closed
locally contractible subsets of locally contractible spaces with a closed imbedding in some
`ℝᴺ` (`hasProperNeighbourhoodDeformations_of_isClosedEmbedding`), in particular in complex
schemes. -/
def HasProperNeighbourhoodDeformations {Y : Type*} [TopologicalSpace Y] (X : Set Y) : Prop :=
  ∀ M ∈ 𝓝ˢ X, ∃ N : Set Y, IsClosed N ∧ X ⊆ interior N ∧ N ⊆ M ∧
    ∃ r : C(N, X), IsProperMap r ∧ (∀ y : N, (y : Y) ∈ X → (r y : Y) = y) ∧
      ∃ G : C(N × I, Y), IsProperMap G ∧ (∀ y, G (y, 0) = y) ∧ (∀ y, G (y, 1) = r y) ∧
        (∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y) ∧ ∀ q, G q ∈ M

/-- **Fulton's setting.** A closed, locally contractible subset `X` of a locally contractible
space `Y` with a closed imbedding in some `ℝᴺ` has arbitrarily small proper neighbourhood
deformations. -/
theorem hasProperNeighbourhoodDeformations_of_isClosedEmbedding {Y : Type*} [TopologicalSpace Y]
    {n : ℕ} {F : Y → EuclideanSpace ℝ (Fin n)} (hF : IsClosedEmbedding F) {X : Set Y}
    (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id)
    (hYc : ∀ y : Y, (𝓝 y).HasBasis (fun V : Set Y ↦ IsOpen V ∧ y ∈ V ∧ ContractibleSpace V) id) :
    HasProperNeighbourhoodDeformations X := fun _ hM ↦
  exists_isClosed_isProperMap_retraction_homotopy hF hX hXc hYc hM

namespace UnderlyingSpace

open AlgebraicGeometry in
/-- A closed, locally contractible subset of the underlying space of a complex scheme has
arbitrarily small proper neighbourhood deformations. -/
theorem hasProperNeighbourhoodDeformations (S : Scheme.{0}) [S.Over (Spec (.of ℂ))]
    [IsComplexScheme S] {X : Set (UnderlyingSpace ℂ S)} (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id) :
    HasProperNeighbourhoodDeformations X := by
  obtain ⟨hYc, _, _, hF⟩ := hasBasis_contractible_and_exists_isClosedEmbedding S
  exact hasProperNeighbourhoodDeformations_of_isClosedEmbedding hF hX hXc hYc

end UnderlyingSpace

/-- A subset `X` with arbitrarily small proper neighbourhood deformations has a closed
neighbourhood `N` with a proper retraction `r : N → X`. -/
lemma HasProperNeighbourhoodDeformations.exists_retraction {Y : Type*} [TopologicalSpace Y]
    {X : Set Y} (h : HasProperNeighbourhoodDeformations X) :
    ∃ N : Set Y, IsClosed N ∧ X ⊆ interior N ∧
      ∃ r : C(N, X), IsProperMap r ∧ ∀ y : N, (y : Y) ∈ X → (r y : Y) = y := by
  obtain ⟨N, hN, hXN, -, r, hr, hrX, -⟩ := h univ Filter.univ_mem
  exact ⟨N, hN, hXN, r, hr, hrX⟩

namespace borelMooreHomology

variable (R : Type u) [CommRing R]

/-- **Independence of the retraction.** If `X` has arbitrarily small proper neighbourhood
deformations, the cap products along any two proper retractions `r : N → X`, `r' : N' → X` of
closed neighbourhoods agree. -/
theorem capProductAlong_retraction_eq (Y : TopCat.{u}) {X N N' : Set Y} (hX : IsClosed X)
    (hXd : HasProperNeighbourhoodDeformations X) (hN : IsClosed N) (hXN : X ⊆ interior N)
    (r : C(N, X)) (hr : IsProperMap r) (hrX : ∀ y : N, (y : Y) ∈ X → (r y : Y) = y)
    (hN' : IsClosed N') (hXN' : X ⊆ interior N') (r' : C(N', X)) (hr' : IsProperMap r')
    (hrX' : ∀ y : N', (y : Y) ∈ X → (r' y : Y) = y) (j k : ℤ) :
    capProductAlong R Y hX hN hXN (TopCat.ofHom r) hr j k =
      capProductAlong R Y hX hN' hXN' (TopCat.ofHom r') hr' j k := by
  have hM : N ∩ N' ∈ 𝓝ˢ X := Filter.inter_mem (subset_interior_iff_mem_nhdsSet.1 hXN)
    (subset_interior_iff_mem_nhdsSet.1 hXN')
  obtain ⟨L, hL, hXL, hLM, s, hs, -, G, hG, hG0, hG1, -, hGM⟩ := hXd _ hM
  have key : ∀ {N : Set Y} (hN : IsClosed N) (hXN : X ⊆ interior N) (r : C(N, X))
      (hr : IsProperMap r) (hrX : ∀ y : N, (y : Y) ∈ X → (r y : Y) = y) (hLN : L ⊆ N)
      (hGN : ∀ q, G q ∈ N),
      capProductAlong R Y hX hN hXN (TopCat.ofHom r) hr j k =
        capProductAlong R Y hX hL hXL (TopCat.ofHom s) hs j k := by
    intro N hN hXN r hr hrX hLN hGN
    rw [← capProductAlong_comp_subsetInclusionOfSubset R Y hX hN hXN hL hXL hLN
      (TopCat.ofHom r) hr]
    simp only [capProductAlong]
    rw [pushforward_retraction_eq_of_homotopy R hL hLN r hr hrX s hs G hG hG0 hG1 hGN]
  exact (key hN hXN r hr hrX (hLM.trans inter_subset_left) fun q ↦ (hGM q).1).trans
    (key hN' hXN' r' hr' hrX' (hLM.trans inter_subset_right) fun q ↦ (hGM q).2).symm

/-- The **cap product** `∩ : H^j(Y, Y - X) ⊗ H_k Y → H_{k-j} X` of [BT] 3.1.7 (Fulton §19.1), for
a closed subset `X` of a space `Y` with arbitrarily small proper neighbourhood deformations (for
instance `X` closed and locally contractible in a locally contractible `Y ⊆ ℝᴺ` closed, or in a
complex scheme): `c ∩ a = r_* (c ∩_N a)` for a closed neighbourhood `N` of `X` with a proper
retraction `r : N → X`, where `c ∩_N a ∈ H_{k-j} N` is the class of the cycle `φ ∩ ρ z` of `N`
(`capProductNbhd`). It does not depend on `(N, r)` (`capProductSupport_eq_capProductAlong`), and
its push-forward to `Y` is `capProduct` (`pushforward_subsetInclusion_capProductSupport`); for
`X = Y` it is the cap product `H^j Y ⊗ H_k Y → H_{k-j} Y`. -/
def capProductSupport (Y : TopCat.{u}) {X : Set Y} (hX : IsClosed X)
    (hXd : HasProperNeighbourhoodDeformations X) (j k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y X j →ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) Y k →ₗ[R]
        borelMooreHomology R (ModuleCat.of R R) (TopCat.of X) (k - j) :=
  capProductAlong R Y hX hXd.exists_retraction.choose_spec.1
    hXd.exists_retraction.choose_spec.2.1
    (TopCat.ofHom hXd.exists_retraction.choose_spec.2.2.choose)
    hXd.exists_retraction.choose_spec.2.2.choose_spec.1 j k

/-- The cap product with supports is the push-forward `r_* (c ∩_N a)` along ANY proper retraction
`r : N → X` of a closed neighbourhood `N` of `X`. -/
theorem capProductSupport_eq_capProductAlong (Y : TopCat.{u}) {X N : Set Y} (hX : IsClosed X)
    (hXd : HasProperNeighbourhoodDeformations X) (hN : IsClosed N) (hXN : X ⊆ interior N)
    (r : C(N, X)) (hr : IsProperMap r) (hrX : ∀ y : N, (y : Y) ∈ X → (r y : Y) = y) (j k : ℤ) :
    capProductSupport R Y hX hXd j k = capProductAlong R Y hX hN hXN (TopCat.ofHom r) hr j k :=
  capProductAlong_retraction_eq R Y hX hXd _ _ _ _
    hXd.exists_retraction.choose_spec.2.2.choose_spec.2 hN hXN r hr hrX j k

/-- **Forgetting the support.** The push-forward along `X ⊆ Y` of `c ∩ a ∈ H_{k-j} X` is the cap
product `c ∩ a ∈ H_{k-j} Y`. -/
theorem pushforward_subsetInclusion_capProductSupport (Y : TopCat.{u}) {X : Set Y}
    (hX : IsClosed X) (hXd : HasProperNeighbourhoodDeformations X) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (subsetInclusion X) (isProperMap_subsetInclusion hX)
        (k - j)).hom (capProductSupport R Y hX hXd j k c a) = capProduct R Y X j k c a := by
  obtain ⟨L, hL, hXL, -, s, hs, hsX, G, hG, hG0, hG1, -⟩ := hXd univ Filter.univ_mem
  rw [capProductSupport_eq_capProductAlong R Y hX hXd hL hXL s hs hsX, capProductAlong,
    LinearMap.compr₂_apply, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← pushforward_comp,
    ← pushforward_subsetInclusion_eq_of_homotopy R hX hL s hs G hG hG0 hG1,
    pushforward_subsetInclusion_capProductNbhd]

/-- Fulton's notation `c ∩ a := f^* c ∩ a ∈ H_{k-j}(f^{-1} X)` for a continuous `f : Y' → Y`,
`c ∈ H^j(Y, Y - X)` and `a ∈ H_k Y'` (Example 19.1.10), when `f^{-1} X` has arbitrarily small
proper neighbourhood deformations in `Y'`. -/
def capProductSupportPullback {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {X : Set Y} (hX : IsClosed X)
    (hXd : HasProperNeighbourhoodDeformations (f ⁻¹' X)) (j k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y X j →ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) Y' k →ₗ[R]
        borelMooreHomology R (ModuleCat.of R R) (TopCat.of (f ⁻¹' X)) (k - j) :=
  (capProductSupport R Y' (hX.preimage f.hom.continuous) hXd j k).comp
    (cohomologyWithSupports.pullback R _ f X j).hom

/-- `c ∩ a = f^* c ∩ a` for `c ∈ H^j(Y, Y - X)` and `a ∈ H_k Y'`. -/
lemma capProductSupportPullback_apply {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {X : Set Y}
    (hX : IsClosed X) (hXd : HasProperNeighbourhoodDeformations (f ⁻¹' X)) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    capProductSupportPullback R f hX hXd j k c a =
      capProductSupport R Y' (hX.preimage f.hom.continuous) hXd j k
        ((cohomologyWithSupports.pullback R _ f X j).hom c) a :=
  rfl

end borelMooreHomology

end MMP
