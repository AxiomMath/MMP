module

public import MMP.AlgebraicTopology.OrientationClass.Point
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
/-!
# The cap product with the orientation class of a point of a curve (Fulton, Lemma 19.2(c))

Let `T` be a connected non-singular complex curve, `X` a space, `pr : X × T → T` the projection
and `a ∈ H_k(X × T)`. Then `pr^*(u_{t,T}) ∩ a ∈ H_{k-2}(X × {t}) = H_{k-2} X` does not depend on
`t ∈ T`.

**Proof.** Near a point `t₀`, in a chart `e` at `t₀`, a map `h : T → T` which is a translation
`z ↦ z + w` near `e t₁` and the identity far away is properly homotopic to the identity through
maps of the same kind (`MMP.Moving.moveOn`), and `h⁻¹(t₂) = {t₁}` for
`w = e t₂ - e t₁`. It carries the local orientation class at `t₂` to the local orientation class
at `t₁` (a chart simplex around `e t₁` is translated into one around `e t₂`). The map
`g = id × h` of `X × T` is properly homotopic to the identity, so `g_* a = a`; by the projection
formula, `g'_* (g^* pr^* u_{t₂} ∩ a) = pr^* u_{t₂} ∩ a` for `g' : X × {t₁} → X × {t₂}`, and
`g^* pr^* u_{t₂} = pr^* h^* u_{t₂} = pr^* u_{t₁}`. As `g'` commutes with the projections to `X`,
the class in `H_{k-2} X` is locally constant in `t`, hence constant on the connected `T`.

## Main results

* `MMP.borelMooreHomology.pushforward_fibreProj_capProductSupportPullback_map`:
  transport of the cap product along `id × h` for `h` properly homotopic to the identity.
* `borelMooreHomology.pushforward_fibreProj_capProductSupportPullback_eq_of_isLocalOrientationClass`
  is the same statement for local orientation classes on a manifold with an oriented atlas.
* `MMP.borelMooreHomology.pushforward_fibreProj_capProductSupportPullback_eq_of_isOrientationClass`:
  Fulton's Lemma 19.2(c).
* `MMP.borelMooreHomology.hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton`:
  the fibres `X × {t}` have arbitrarily small proper neighbourhood deformations.

## Implementation notes

The statement is proved for a connected Hausdorff complex manifold `T` (`IsManifold 𝓘(ℂ, E) 1`)
modelled on any non-zero finite-dimensional `E`, a curve being `E = ℂ`, and any coefficient ring
`R`. `X` is metrizable (Fulton's standing convention in §19.1: closed subspaces of some `ℝᴺ`);
this makes the fibres `X × {s}` have arbitrarily small proper neighbourhood deformations
(`hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton`), which the cap products into
`H_*(X × {s})` (`capProductSupportPullback`) require to be defined.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Lemma 19.2(c).
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology

universe u

namespace MMP

namespace borelMooreHomology

variable (X T : TopCat.{u})

/-- The projection `pr : X × T → T`, as a morphism of `TopCat`. -/
def prodSnd : TopCat.of (X × T) ⟶ T :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

/-- A point `p` of `X × T` lies in the fibre `pr⁻¹ t` if and only if `p.2 = t`. -/
lemma mem_prodSnd_preimage_singleton {t : T} (p : X × T) :
    p ∈ prodSnd X T ⁻¹' {t} ↔ p.2 = t :=
  Iff.rfl

variable {T}

/-- The identification `X ≅ X × {t} = pr⁻¹ t`. -/
def fibreHomeomorph (t : T) : X ≃ₜ (prodSnd X T ⁻¹' {t}) where
  toFun x := ⟨(x, t), rfl⟩
  invFun p := p.1.1
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl ((mem_prodSnd_preimage_singleton X T p.1).1 p.2).symm)
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

/-- The projection `X × {t} → X`, as a morphism of `TopCat`. -/
def fibreProj (t : T) : TopCat.of (prodSnd X T ⁻¹' {t}) ⟶ X :=
  TopCat.ofHom ⟨fun p ↦ p.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- The projection `X × {t} → X` is a proper map. -/
lemma isProperMap_fibreProj (t : T) : IsProperMap (fibreProj X t) :=
  (fibreHomeomorph X t).symm.isProperMap

/-- For `T` a `T₁` space, the fibre `X × {t} = pr⁻¹ t` is closed in `X × T`. -/
lemma isClosed_prodSnd_preimage_singleton [T1Space T] (t : T) :
    IsClosed (prodSnd X T ⁻¹' {t}) :=
  isClosed_singleton.preimage (prodSnd X T).hom.continuous

variable (R : Type u) [CommRing R]

/-- Equal proper maps `f = g` induce equal pushforwards on Borel–Moore homology, whatever the
properness proofs. -/
lemma pushforward_congr' {Y Z : TopCat.{u}} {f g : Y ⟶ Z} (hfg : f = g) (hf : IsProperMap f)
    (hg : IsProperMap g) (i : ℤ) :
    pushforward R (ModuleCat.of R R) f hf i = pushforward R (ModuleCat.of R R) g hg i := by
  subst hfg
  rfl

/-- For proper maps `f` and `g`, `g_* (f_* x) = (g ∘ f)_* x` in Borel–Moore homology. -/
lemma pushforward_pushforward_apply {Y Z W : TopCat.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
    (hf : IsProperMap f) (hg : IsProperMap g) (i : ℤ)
    (x : borelMooreHomology R (ModuleCat.of R R) Y i) :
    (pushforward R (ModuleCat.of R R) g hg i).hom
        ((pushforward R (ModuleCat.of R R) f hf i).hom x) =
      (pushforward R (ModuleCat.of R R) (f ≫ g) (hg.comp hf) i).hom x := by
  rw [pushforward_comp]
  rfl

/-- Equal maps `f = g : (Y', A') → (Y, A)` of pairs induce equal maps on relative singular
cohomology, whatever the proofs that they are maps of pairs. -/
lemma _root_.MMP.relativeSingularCohomology.map_congr_of_eq {Y' Y : TopCat.{u}}
    {f g : Y' ⟶ Y} (hfg : f = g)
    {A' : Set Y'} {A : Set Y} (hf : A' ⊆ f ⁻¹' A) (hg : A' ⊆ g ⁻¹' A) (j : ℤ) :
    relativeSingularCohomology.map R (ModuleCat.of R R) f hf j =
      relativeSingularCohomology.map R (ModuleCat.of R R) g hg j := by
  subst hfg
  rfl

/-- If `h⁻¹(t₂) = {t₁}`, then `h` maps `T - t₁` into `T - t₂`. -/
lemma compl_singleton_subset_of_preimage_eq {h : T ⟶ T} {t₁ t₂ : T}
    (hpre : h ⁻¹' {t₂} = {t₁}) : ({t₁}ᶜ : Set T) ⊆ h ⁻¹' {t₂}ᶜ := by
  rw [preimage_compl, hpre]

variable {X}

/-- If `h : T → T` is properly homotopic to the identity, then `id × h : X × T → X × T` acts as
the identity on Borel–Moore homology. -/
lemma pushforward_prodMap_id_apply_of_properHomotopy (h : T ⟶ T)
    (F : TopCat.Homotopy (𝟙 T) h) (hF : IsProperMap F) (k : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (X × T)) k) :
    (pushforward R (ModuleCat.of R R)
      (TopCat.ofHom ⟨Prod.map id h, continuous_id.prodMap h.hom.continuous⟩ :
        TopCat.of (X × T) ⟶ TopCat.of (X × T))
      (isProperMap_id.prodMap (isProperMap_of_properHomotopy_right F hF)) k).hom a = a := by
  have hh := isProperMap_of_properHomotopy_right F hF
  let e : unitInterval × (X × T) ≃ₜ X × (unitInterval × T) :=
    { toFun := fun q ↦ (q.2.1, (q.1, q.2.2))
      invFun := fun q ↦ (q.2.1, (q.1, q.2.2))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let G : TopCat.Homotopy (𝟙 (TopCat.of (X × T)))
      (TopCat.ofHom ⟨Prod.map id h, continuous_id.prodMap h.hom.continuous⟩) :=
    { toFun := fun q : unitInterval × (X × T) ↦ (q.2.1, F (q.1, q.2.2))
      continuous_toFun := by
        have := F.continuous
        fun_prop
      map_zero_left := fun q : X × T ↦ by
        change (q.1, F (0, q.2)) = q
        rw [F.apply_zero]
        rfl
      map_one_left := fun q : X × T ↦ by
        change (q.1, F (1, q.2)) = (q.1, h q.2)
        rw [F.apply_one] }
  have hG : IsProperMap G := by
    have : (G : unitInterval × (X × T) → X × T) = Prod.map id F ∘ e := rfl
    rw [this]
    exact (isProperMap_id.prodMap hF).comp e.isProperMap
  have hid : IsProperMap (𝟙 (TopCat.of (X × T))) := by simp [isProperMap_id]
  rw [← pushforward_eq_of_properHomotopy R (ModuleCat.of R R) hid (isProperMap_id.prodMap hh) G hG
    k, pushforward_id]
  rfl

/-- For `g` lifting `h` along `pr : X × T → T` with `h⁻¹(t₂) = {t₁}`, forgetting the supports of
`g^* pr^* c` from `g⁻¹(X × {t₂})` to `X × {t₁}` gives `pr^* (h^* c)`. -/
lemma forget_pullback_pullback_prodSnd {g : TopCat.of (X × T) ⟶ TopCat.of (X × T)} {h : T ⟶ T}
    (hgh : g ≫ prodSnd X T = prodSnd X T ≫ h) {t₁ t₂ : T} (hpre : h ⁻¹' {t₂} = {t₁})
    (hW : g ⁻¹' (prodSnd X T ⁻¹' {t₂}) ⊆ prodSnd X T ⁻¹' {t₁}) (j : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) T {t₂} j) :
    (cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of (X × T)) hW j).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g (prodSnd X T ⁻¹' {t₂}) j).hom
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prodSnd X T) {t₂} j).hom c)) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (prodSnd X T) {t₁} j).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) h
          (compl_singleton_subset_of_preimage_eq hpre) j).hom c) := by
  have hg1 : (prodSnd X T ⁻¹' {t₁})ᶜ ⊆
      (𝟙 (TopCat.of (X × T))) ⁻¹' (g ⁻¹' (prodSnd X T ⁻¹' {t₂}))ᶜ :=
    compl_subset_compl.mpr hW
  have hf1 : (g ⁻¹' (prodSnd X T ⁻¹' {t₂}))ᶜ ⊆ g ⁻¹' (prodSnd X T ⁻¹' {t₂})ᶜ := fun _ hx ↦ hx
  have hpr : (prodSnd X T ⁻¹' {t₂})ᶜ ⊆ prodSnd X T ⁻¹' ({t₂}ᶜ : Set T) := fun _ hx ↦ hx
  have hpr1 : (prodSnd X T ⁻¹' {t₁})ᶜ ⊆ prodSnd X T ⁻¹' ({t₁}ᶜ : Set T) := fun _ hx ↦ hx
  have hh1 := compl_singleton_subset_of_preimage_eq hpre
  have e := relativeSingularCohomology.map_congr_of_eq R
    (f := 𝟙 (TopCat.of (X × T)) ≫ g ≫ prodSnd X T) (g := prodSnd X T ≫ h)
    ((Category.id_comp _).trans hgh) (fun _ hx ↦ hpr (hf1 (hg1 hx))) (fun _ hx ↦ hh1 (hpr1 hx)) j
  rw [relativeSingularCohomology.map_comp R (ModuleCat.of R R) (𝟙 (TopCat.of (X × T)))
      (g ≫ prodSnd X T) hg1 (fun _ hx' ↦ hpr (hf1 hx')),
    relativeSingularCohomology.map_comp R (ModuleCat.of R R) g (prodSnd X T) hf1 hpr,
    relativeSingularCohomology.map_comp R (ModuleCat.of R R) (prodSnd X T) h hpr1 hh1] at e
  exact congrArg (fun φ ↦ (ModuleCat.Hom.hom φ) c) e

/-- **Transport of the cap product along `id × h`.** Let `h : T → T` be properly homotopic to the
identity with `h⁻¹(t₂) = {t₁}`. For `c ∈ H^j(T, T - t₂)` and `a ∈ H_k(X × T)`, the classes
`pr^*(h^* c) ∩ a ∈ H_{k-j}(X × {t₁})` and `pr^* c ∩ a ∈ H_{k-j}(X × {t₂})` have the same image in
`H_{k-j} X`. -/
theorem pushforward_fibreProj_capProductSupportPullback_map [T1Space T] (h : T ⟶ T)
    (F : TopCat.Homotopy (𝟙 T) h) (hF : IsProperMap F) {t₁ t₂ : T}
    (hpre : h ⁻¹' {t₂} = {t₁})
    (hd₁ : HasProperNeighbourhoodDeformations (prodSnd X T ⁻¹' {t₁}))
    (hd₂ : HasProperNeighbourhoodDeformations (prodSnd X T ⁻¹' {t₂})) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) T {t₂} j)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (X × T)) k) :
    (pushforward R (ModuleCat.of R R) (fibreProj X t₁) (isProperMap_fibreProj X t₁) (k - j)).hom
        (capProductSupportPullback R (prodSnd X T) isClosed_singleton hd₁ j k
          ((relativeSingularCohomology.map R (ModuleCat.of R R) h
            (compl_singleton_subset_of_preimage_eq hpre) j).hom c) a) =
      (pushforward R (ModuleCat.of R R) (fibreProj X t₂) (isProperMap_fibreProj X t₂)
          (k - j)).hom
        (capProductSupportPullback R (prodSnd X T) isClosed_singleton hd₂ j k c a) := by
  have hh := isProperMap_of_properHomotopy_right F hF
  let g : TopCat.of (X × T) ⟶ TopCat.of (X × T) :=
    TopCat.ofHom ⟨Prod.map id h, continuous_id.prodMap h.hom.continuous⟩
  have hg : IsProperMap g := isProperMap_id.prodMap hh
  have hga : (pushforward R (ModuleCat.of R R) g hg k).hom a = a :=
    pushforward_prodMap_id_apply_of_properHomotopy R h F hF k a
  have hW : g ⁻¹' (prodSnd X T ⁻¹' {t₂}) = prodSnd X T ⁻¹' {t₁} := by
    ext p
    change h p.2 = t₂ ↔ p.2 = t₁
    exact Set.ext_iff.1 hpre p.2
  have hdW : HasProperNeighbourhoodDeformations (g ⁻¹' (prodSnd X T ⁻¹' {t₂})) := hW ▸ hd₁
  have hS₂ : IsClosed (prodSnd X T ⁻¹' {t₂}) := isClosed_prodSnd_preimage_singleton X t₂
  have hWc : IsClosed (g ⁻¹' (prodSnd X T ⁻¹' {t₂})) := hS₂.preimage g.hom.continuous
  have PF := pushforward_restrictPreimage_capProductSupportPullback R g hg hS₂ hd₂ hdW j k
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prodSnd X T) {t₂} j).hom c) a
  rw [hga] at PF
  have FS := pushforward_subsetInclusionOfSubset_capProductSupport R (TopCat.of (X × T)) hWc
    (isClosed_prodSnd_preimage_singleton X t₁) hdW hd₁ hW.le j k
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g (prodSnd X T ⁻¹' {t₂}) j).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prodSnd X T) {t₂} j).hom c)) a
  have hc := forget_pullback_pullback_prodSnd R (g := g) (h := h) rfl hpre hW.le j c
  have hq : subsetInclusionOfSubset hW.le ≫ fibreProj X t₁ =
      TopCat.ofHom (g.hom.restrictPreimage (prodSnd X T ⁻¹' {t₂})) ≫ fibreProj X t₂ := rfl
  rw [capProductSupportPullback_apply, ← hc, ← FS, capProductSupportPullback_apply, ← PF]
  refine (pushforward_pushforward_apply R _ _ _ _ _ _).trans
    ((congrArg (fun φ ↦ (ModuleCat.Hom.hom φ) _) (pushforward_congr' R hq _ _ _)).trans
      (pushforward_pushforward_apply R _ _ _ _ _ _).symm)

end borelMooreHomology

namespace Moving

open Finsupp ThomClass SingularChain SingularCochain FundamentalClass Filter Metric

variable {T : Type u} [TopologicalSpace T] [T2Space T] {H : Type*} [NormedAddCommGroup H]
  [NormedSpace ℝ H] [FiniteDimensional ℝ H] [ChartedSpace H T] {R : Type u} [CommRing R]

omit [FiniteDimensional ℝ H] in
/-- Translating the vertices of an affine simplex by `w` translates the simplex by `w`. -/
lemma _root_.MMP.ThomClass.affineSimplex_add_const {n : ℕ} (v : Fin (n + 1) → H) (w : H)
    (t : stdSimplex ℝ (Fin (n + 1))) :
    affineSimplex (fun k ↦ v k + w) t = affineSimplex v t + w := by
  have hs : ∑ k, (t : Fin (n + 1) → ℝ) k = 1 := t.2.2
  simp only [affineSimplex_apply, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hs,
    one_smul]

/-- The homotopy `moveOn` is a proper map: it is the identity outside the compact set
`e⁻¹(closedBall p ρ)`. -/
lemma isProperMap_moveOn {e : OpenPartialHomeomorph T H} {p w : H} {ρ : ℝ} (hρ : 0 < ρ)
    (hw : ‖w‖ < ρ) (hball : closedBall p (2 * ρ) ⊆ e.target) :
    IsProperMap fun x : unitInterval × T ↦ moveOn e p w ρ x.1 x.2 := by
  classical
  have hKt : closedBall p ρ ⊆ e.target :=
    (closedBall_subset_closedBall (by linarith)).trans hball
  set K := e.symm '' closedBall p ρ
  have hKc : IsCompact K :=
    (isCompact_closedBall p ρ).image_of_continuousOn (e.continuousOn_symm.mono hKt)
  have hfix : ∀ (lam : ℝ) (y : T), y ∉ K → moveOn e p w ρ lam y = y := by
    intro lam y hy
    simp only [moveOn]
    split_ifs with hs
    · have hfar : ρ ≤ ‖e y - p‖ := by
        by_contra hlt
        refine hy ⟨e y, ?_, e.left_inv hs⟩
        rw [mem_closedBall, dist_eq_norm]
        exact (lt_of_not_ge hlt).le
      rw [moveMap_of_ge _ hρ hfar, e.left_inv hs]
    · rfl
  have := ChartedSpace.locallyCompactSpace H T
  have hcont := continuous_moveOn hρ hw hball
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hcont, fun C hC ↦ ?_⟩
  refine (isCompact_univ.prod (hC.union hKc)).of_isClosed_subset (hC.isClosed.preimage hcont) ?_
  rintro ⟨lam, y⟩ hq
  refine ⟨trivial, ?_⟩
  by_cases hy : y ∈ K
  · exact Or.inr hy
  · left
    change moveOn e p w ρ lam y ∈ C at hq
    rwa [hfix lam y hy] at hq

/-- **The moving map in a chart.** If `y₁, y₂` lie in the source of a chart `e` with
`‖e y₂ - e y₁‖ < ρ / 2` and the closed ball of radius `2ρ` about `e y₁` lies in the chart target,
there is a map `h : T → T`, properly homotopic to the identity, with `h⁻¹(y₂) = {y₁}`, pulling
every chart-oriented cocycle at `y₂` back to one cohomologous in `H^n(T, T - y₁)` to every
chart-oriented cocycle at `y₁`. -/
theorem exists_properHomotopy_of_mem_source {m : ℕ} (b : Module.Basis (Fin (m + 1)) ℝ H)
    {e : OpenPartialHomeomorph T H} (he : e ∈ atlas H T) {y₁ y₂ : T} (hy₁ : y₁ ∈ e.source)
    (hy₂ : y₂ ∈ e.source) {ρ : ℝ} (hρ : 0 < ρ) (hw : ‖e y₂ - e y₁‖ < ρ / 2)
    (hball : closedBall (e y₁) (2 * ρ) ⊆ e.target) :
    ∃ h : TopCat.of T ⟶ TopCat.of T, ∃ F : TopCat.Homotopy (𝟙 (TopCat.of T)) h,
      IsProperMap F ∧ h ⁻¹' {y₂} = {y₁} ∧ ∀ α₁ α₂ : Simplex T (m + 1) → R,
        IsChartOrientedCocycle R b y₁ α₁ → IsChartOrientedCocycle R b y₂ α₂ →
          cochainPullback R h (m + 1) α₂ - α₁ ∈ relCoboundaries R ({y₁}ᶜ : Set T) (m + 1) := by
  set w := e y₂ - e y₁
  have hcont := continuous_moveOn (e := e) hρ (by linarith) hball
  have h1c : Continuous (moveOn e (e y₁) w ρ 1) :=
    hcont.comp (Continuous.prodMk (continuous_const : Continuous fun _ : T ↦ (1 : unitInterval))
      continuous_id)
  let hmap : C(T, T) := ⟨moveOn e (e y₁) w ρ 1, h1c⟩
  let Hm : TopCat.Homotopy (𝟙 (TopCat.of T)) (TopCat.ofHom hmap) :=
    { toFun := fun x ↦ moveOn e (e y₁) w ρ x.1 x.2
      continuous_toFun := hcont
      map_zero_left := fun y ↦ moveOn_zero y
      map_one_left := fun _ ↦ rfl }
  have hpreEq : TopCat.ofHom hmap ⁻¹' {y₂} = {y₁} :=
    Set.ext fun y ↦ moveOn_one_eq_iff hρ hw hball hy₁ rfl hy₂ (by simp [w]) y
  have hpre := borelMooreHomology.compl_singleton_subset_of_preimage_eq hpreEq
  have hHm : IsProperMap Hm := isProperMap_moveOn (e := e) (p := e y₁) (w := w) hρ (by linarith)
    hball
  refine ⟨TopCat.ofHom hmap, Hm, hHm, hpreEq, fun α₁ α₂ h₁ h₂ ↦ ?_⟩
  obtain ⟨v, hv, hvb⟩ := exists_isOrientedSimplexAroundZero_subset b (e y₁)
    (ball_mem_nhds (e y₁) (half_pos hρ))
  have hvt : range (affineSimplex v) ⊆ e.target := fun z hz ↦
    hball (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) (hvb hz))
  have hvw : IsOrientedSimplexAroundZero b fun k ↦ (v k + w) - e y₂ := by
    convert hv using 2 with k
    simp only [w]
    abel
  have hvwt : range (affineSimplex fun k ↦ v k + w) ⊆ e.target := by
    rintro _ ⟨t, rfl⟩
    refine hball ?_
    have h1 := hvb ⟨t, rfl⟩
    rw [mem_ball, dist_eq_norm] at h1
    rw [mem_closedBall, dist_eq_norm, affineSimplex_add_const v w t,
      show affineSimplex v t + w - e y₁ = (affineSimplex v t - e y₁) + w by abel]
    linarith [norm_add_le (affineSimplex v t - e y₁) w]
  have hcomp : hmap.comp (chartSimplexOf e v hvt) = chartSimplexOf e (fun k ↦ v k + w) hvwt := by
    ext t
    have h1 := hvb ⟨t, rfl⟩
    rw [mem_ball, dist_eq_norm] at h1
    simp only [ContinuousMap.comp_apply, chartSimplexOf_apply, affineSimplex_add_const v w t]
    exact moveOn_one_symm hρ (hvt ⟨t, rfl⟩) h1.le
  have hP : cochainPullback R (TopCat.ofHom hmap) (m + 1) α₂ - α₁ ∈
      relCocycles R ({y₁}ᶜ : Set T) (m + 1) :=
    Submodule.sub_mem _ (cochainPullback_mem_relCocycles (TopCat.ofHom hmap) hpre h₂.1) h₁.1
  refine mem_relCoboundaries_of_eval_chartSimplexOf b hy₁ hv hvt hP ?_
  have h1 := h₁.2 e he hy₁ v hv hvt
  have h2 := h₂.2 e he hy₂ _ hvw hvwt
  rw [linearCombination_single, one_smul] at h1 h2
  rw [linearCombination_single, one_smul, Pi.sub_apply, h1, sub_eq_zero]
  change α₂ (hmap.comp (chartSimplexOf e v hvt)) = 1
  rw [hcomp, h2]

/-- **The moving map.** Every point `y₀` of a manifold has a neighbourhood `V` such that for
`y₁, y₂ ∈ V` there is a map `h : T → T`, properly homotopic to the identity, with `h⁻¹(y₂) = {y₁}`,
pulling every chart-oriented cocycle at `y₂` back to one cohomologous in `H^n(T, T - y₁)` to every
chart-oriented cocycle at `y₁`. -/
theorem exists_mem_nhds_properHomotopy {m : ℕ} (b : Module.Basis (Fin (m + 1)) ℝ H)
    (y₀ : T) : ∃ V ∈ 𝓝 y₀, ∀ y₁ ∈ V, ∀ y₂ ∈ V,
      ∃ h : TopCat.of T ⟶ TopCat.of T, ∃ F : TopCat.Homotopy (𝟙 (TopCat.of T)) h,
        IsProperMap F ∧ h ⁻¹' {y₂} = {y₁} ∧ ∀ α₁ α₂ : Simplex T (m + 1) → R,
          IsChartOrientedCocycle R b y₁ α₁ → IsChartOrientedCocycle R b y₂ α₂ →
            cochainPullback R h (m + 1) α₂ - α₁ ∈ relCoboundaries R ({y₁}ᶜ : Set T) (m + 1) := by
  set e := chartAt H y₀
  have he : e ∈ atlas H T := chart_mem_atlas H y₀
  have hy₀ : y₀ ∈ e.source := mem_chart_source H y₀
  obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.1 e.open_target _ (e.map_source hy₀)
  set r := ε / 13
  have hr : 0 < r := by positivity
  refine ⟨e.source ∩ e ⁻¹' ball (e y₀) r,
    inter_mem (e.open_source.mem_nhds hy₀) (e.continuousAt hy₀ (ball_mem_nhds _ hr)),
    fun y₁ hy₁ y₂ hy₂ ↦ ?_⟩
  have hd₁ : ‖e y₁ - e y₀‖ < r := mem_ball_iff_norm.1 hy₁.2
  have hd₂ : ‖e y₂ - e y₀‖ < r := mem_ball_iff_norm.1 hy₂.2
  refine exists_properHomotopy_of_mem_source (e := e) (ρ := 5 * r) b he hy₁.1 hy₂.1
    (by positivity) ?_ ?_
  · have : ‖e y₂ - e y₁‖ ≤ ‖e y₂ - e y₀‖ + ‖e y₁ - e y₀‖ := by
      rw [show e y₂ - e y₁ = (e y₂ - e y₀) - (e y₁ - e y₀) by abel]
      exact norm_sub_le _ _
    linarith
  · refine Subset.trans ?_ hεt
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    calc ‖z - e y₀‖ = ‖(z - e y₁) + (e y₁ - e y₀)‖ := by abel_nf
      _ ≤ ‖z - e y₁‖ + ‖e y₁ - e y₀‖ := norm_add_le _ _
      _ < ε := by
        simp only [r] at hd₁ hz
        linarith

end Moving

section localOrientation

open Finsupp ThomClass SingularChain SingularCochain FundamentalClass Filter Metric

variable {T : TopCat.{u}} [T2Space T] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] [ChartedSpace H T] (R : Type u) [CommRing R]

/-- `u ∈ H^n(T, T - y)` is the *local orientation class* at `y` of the orientation of the atlas
given by the basis `b`: it is represented by a chart-oriented cocycle. -/
def IsLocalOrientationClass {n : ℕ} (b : Module.Basis (Fin n) ℝ H) (y : T)
    (u : cohomologyWithSupports R (ModuleCat.of R R) T {y} n) : Prop :=
  ∃ α : Simplex T n → R, ∃ hα : α ∈ relCocycles R ({y}ᶜ : Set T) n,
    IsChartOrientedCocycle R b y α ∧
      relativeSingularCohomologyEquiv R ({y}ᶜ : Set T) n u = Submodule.Quotient.mk ⟨α, hα⟩

variable {R}

/-- **Existence of the local orientation class.** On a manifold with an oriented atlas, for
`n > 0` and a basis `b` of `H`, every point `y` has a local orientation class in
`H^n(T, T - y)`. -/
theorem exists_isLocalOrientationClass (hT : IsOrientedAtlas H T) {n : ℕ} (hn : 0 < n)
    (b : Module.Basis (Fin n) ℝ H) (y : T) : ∃ u, IsLocalOrientationClass R b y u := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨α, hα⟩ := exists_isChartOrientedCocycle (R := R) hT b y
  exact ⟨(relativeSingularCohomologyEquiv R ({y}ᶜ : Set T) (m + 1)).symm
    (Submodule.Quotient.mk ⟨α, hα.1⟩), α, hα.1, hα, by simp⟩

omit [FiniteDimensional ℝ H] in
/-- **Uniqueness of the local orientation class.** For `0 < n`, two local orientation classes at
`y` for the basis `b` are equal. -/
theorem IsLocalOrientationClass.eq {n : ℕ} (hn : 0 < n) {b : Module.Basis (Fin n) ℝ H} {y : T}
    {u u' : cohomologyWithSupports R (ModuleCat.of R R) T {y} n}
    (hu : IsLocalOrientationClass R b y u) (hu' : IsLocalOrientationClass R b y u') : u = u' := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨α, hα, hc, hrep⟩ := hu
  obtain ⟨α', hα', hc', hrep'⟩ := hu'
  apply (relativeSingularCohomologyEquiv R ({y}ᶜ : Set T) (m + 1)).injective
  rw [hrep, hrep']
  refine (Submodule.Quotient.eq _).2 ?_
  set e := chartAt H y
  have hy : y ∈ e.source := mem_chart_source H y
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (e y)
    (e.open_target.mem_nhds (e.map_source hy))
  refine mem_relCoboundaries_of_eval_chartSimplexOf b hy hv hvt (Submodule.sub_mem _ hα hα') ?_
  have h1 := hc.2 e (chart_mem_atlas H y) hy v hv hvt
  have h2 := hc'.2 e (chart_mem_atlas H y) hy v hv hvt
  rw [linearCombination_single, one_smul] at h1 h2
  rw [linearCombination_single, one_smul]
  change α _ - α' _ = 0
  rw [h1, h2, sub_self]

omit [T2Space T] [FiniteDimensional ℝ H] in
/-- A map `h` pulling chart-oriented cocycles at `y₂` back to cocycles cohomologous to
chart-oriented cocycles at `y₁` carries the local orientation class at `y₂` to that at `y₁`. -/
theorem IsLocalOrientationClass.map {n : ℕ} {b : Module.Basis (Fin n) ℝ H} {y₁ y₂ : T}
    (h : T ⟶ T) (hs : ({y₁}ᶜ : Set T) ⊆ h ⁻¹' {y₂}ᶜ)
    (hα : ∀ α₁ α₂ : Simplex T n → R, IsChartOrientedCocycle R b y₁ α₁ →
      IsChartOrientedCocycle R b y₂ α₂ →
        cochainPullback R h n α₂ - α₁ ∈ relCoboundaries R ({y₁}ᶜ : Set T) n)
    {u₁ : cohomologyWithSupports R (ModuleCat.of R R) T {y₁} n}
    {u₂ : cohomologyWithSupports R (ModuleCat.of R R) T {y₂} n}
    (hu₁ : IsLocalOrientationClass R b y₁ u₁) (hu₂ : IsLocalOrientationClass R b y₂ u₂) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) h hs n).hom u₂ = u₁ := by
  obtain ⟨α₁, hα₁, hc₁, hrep₁⟩ := hu₁
  obtain ⟨α₂, hα₂, hc₂, hrep₂⟩ := hu₂
  apply (relativeSingularCohomologyEquiv R ({y₁}ᶜ : Set T) n).injective
  rw [relativeSingularCohomologyEquiv_map, hrep₂, hrep₁, relCohomologyMap_mk]
  exact (Submodule.Quotient.eq _).2 (hα α₁ α₂ hc₁ hc₂)

end localOrientation

namespace borelMooreHomology

open Finsupp ThomClass SingularChain SingularCochain FundamentalClass Filter Metric

variable {X : TopCat.{u}} {T : TopCat.{u}} [T2Space T] {H : Type*} [NormedAddCommGroup H]
  [NormedSpace ℝ H] [FiniteDimensional ℝ H] [ChartedSpace H T] (R : Type u) [CommRing R]

/-- **Lemma 19.2(c) for local orientation classes.** On a connected Hausdorff space `T` with an
oriented atlas, the image in `H_{k-n} X` of `pr^*(u_t) ∩ a ∈ H_{k-n}(X × {t})`, `u_t` the local
orientation class at `t`, does not depend on `t`. -/
theorem pushforward_fibreProj_capProductSupportPullback_eq_of_isLocalOrientationClass
    [ConnectedSpace T] (hT : IsOrientedAtlas H T) {n : ℕ} (hn : 0 < n)
    (b : Module.Basis (Fin n) ℝ H)
    (hd : ∀ s : T, HasProperNeighbourhoodDeformations (prodSnd X T ⁻¹' {s})) (k : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (X × T)) k) {t t' : T}
    {u : cohomologyWithSupports R (ModuleCat.of R R) T {t} n}
    {u' : cohomologyWithSupports R (ModuleCat.of R R) T {t'} n}
    (hu : IsLocalOrientationClass R b t u) (hu' : IsLocalOrientationClass R b t' u') :
    (pushforward R (ModuleCat.of R R) (fibreProj X t) (isProperMap_fibreProj X t) (k - n)).hom
        (capProductSupportPullback R (prodSnd X T) isClosed_singleton (hd t) n k u a) =
      (pushforward R (ModuleCat.of R R) (fibreProj X t') (isProperMap_fibreProj X t')
          (k - n)).hom
        (capProductSupportPullback R (prodSnd X T) isClosed_singleton (hd t') n k u' a) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  choose v hv using fun s : T ↦ exists_isLocalOrientationClass (R := R) hT hn b s
  let f : T → borelMooreHomology R (ModuleCat.of R R) X (k - ((m + 1 : ℕ) : ℤ)) := fun s ↦
    (pushforward R (ModuleCat.of R R) (fibreProj X s) (isProperMap_fibreProj X s)
        (k - ((m + 1 : ℕ) : ℤ))).hom
      (capProductSupportPullback R (prodSnd X T) isClosed_singleton (hd s) (m + 1 : ℕ) k (v s) a)
  have hf : IsLocallyConstant f := (IsLocallyConstant.iff_eventually_eq f).2 fun s₀ ↦ by
    obtain ⟨V, hV, hmov⟩ := Moving.exists_mem_nhds_properHomotopy (T := T) (R := R) b s₀
    filter_upwards [hV] with s hs
    obtain ⟨h, F, hF, hpre, hα⟩ := hmov s hs s₀ (mem_of_mem_nhds hV)
    have key := pushforward_fibreProj_capProductSupportPullback_map R h F hF hpre (hd s)
      (hd s₀) (m + 1 : ℕ) k (v s₀) a
    rwa [IsLocalOrientationClass.map h _ hα (hv s) (hv s₀)] at key
  obtain rfl := hu.eq hn (hv t)
  obtain rfl := hu'.eq hn (hv t')
  exact hf.apply_eq_of_preconnectedSpace t t'

end borelMooreHomology

namespace borelMooreHomology

section deformation

open Metric

/-- For `0 ≤ l ≤ 1`, the point `a + l • (p - a)` of the segment from `a` to `p` is no farther
from `p` than `a` is. -/
lemma dist_add_smul_sub_le {H : Type*} [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    (a p : H) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    dist (a + l • (p - a)) p ≤ dist a p := by
  rw [dist_eq_norm, dist_eq_norm, show a + l • (p - a) - p = (1 - l) • (a - p) by module,
    norm_smul, Real.norm_of_nonneg (by linarith)]
  nlinarith [norm_nonneg (a - p)]

/-- For an open set `O ⊆ X × H` containing `X × {p₀}` and `ε₀ > 0`, there is a continuous radius
`ρ : X → (0, ε₀ / 2]` with `(x, z) ∈ O` whenever `dist z p₀ ≤ ρ x`. -/
lemma exists_continuous_radius_of_isOpen {X H : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace H] {O : Set (X × H)} (hO : IsOpen O) {p₀ : H} (hpO : ∀ x, (x, p₀) ∈ O)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ ρ : X → ℝ, Continuous ρ ∧ (∀ x, 0 < ρ x) ∧ (∀ x, ρ x ≤ ε₀ / 2) ∧
      ∀ x z, dist z p₀ ≤ ρ x → (x, z) ∈ O := by
  classical
  let d : X → ℝ := fun x ↦ if Oᶜ.Nonempty then infDist (x, p₀) Oᶜ else ε₀
  have hd : Continuous d := by
    by_cases h : Oᶜ.Nonempty
    · simp only [d, h, ↓reduceIte]
      exact (continuous_infDist_pt _).comp (continuous_id.prodMk continuous_const)
    · simp only [d, h, ↓reduceIte]
      exact continuous_const
  have hdpos : ∀ x, 0 < d x := fun x ↦ by
    by_cases h : Oᶜ.Nonempty
    · simp only [d, h, ↓reduceIte]
      exact (hO.isClosed_compl.notMem_iff_infDist_pos h).1 fun hx ↦ hx (hpO x)
    · simp only [d, h, ↓reduceIte]
      exact hε₀
  have hdO : ∀ x z, dist z p₀ < d x → (x, z) ∈ O := fun x z hz ↦ by
    by_cases h : Oᶜ.Nonempty
    · simp only [d, h, ↓reduceIte] at hz
      by_contra hn
      refine notMem_of_dist_lt_infDist (s := Oᶜ) (x := (x, p₀)) (y := (x, z)) ?_ hn
      rw [Prod.dist_eq, dist_self, dist_comm]
      simpa using hz
    · by_contra hn
      exact h ⟨_, hn⟩
  exact ⟨fun x ↦ min (ε₀ / 2) (d x / 2), continuous_const.min (hd.div_const 2),
    fun x ↦ lt_min (half_pos hε₀) (half_pos (hdpos x)), fun x ↦ min_le_left _ _,
    fun x z hz ↦ hdO x z (hz.trans_lt ((min_le_right _ _).trans_lt (half_lt_self (hdpos x))))⟩

/-- For a partial homeomorphism `e : T → H`, a continuous `ρ : X → ℝ` and a closed `K ⊆ e.source`
containing every `s` with `dist (e s) p₀ ≤ ρ x`, the set
`{(x, s) : s ∈ e.source, dist (e s) p₀ ≤ ρ x}` is closed. -/
lemma isClosed_setOf_mem_source_dist_le {X T H : Type*} [TopologicalSpace X] [TopologicalSpace T]
    [PseudoMetricSpace H] (e : OpenPartialHomeomorph T H) {ρ : X → ℝ} (hρ : Continuous ρ)
    (p₀ : H) {K : Set T} (hK : IsClosed K) (hKs : K ⊆ e.source)
    (hNK : ∀ q : X × T, q.2 ∈ e.source → dist (e q.2) p₀ ≤ ρ q.1 → q.2 ∈ K) :
    IsClosed {q : X × T | q.2 ∈ e.source ∧ dist (e q.2) p₀ ≤ ρ q.1} := by
  have hf : ContinuousOn (fun q : X × T ↦ (ρ q.1, dist (e q.2) p₀)) (Prod.snd ⁻¹' e.source) :=
    (hρ.comp continuous_fst).continuousOn.prodMk
      ((continuous_id.dist (continuous_const (y := p₀))).comp_continuousOn
        (f := fun q : X × T ↦ e q.2) (e.continuousOn.comp continuousOn_snd fun _ h ↦ h))
  rw [← isOpen_compl_iff]
  convert (hK.isOpen_compl.preimage continuous_snd).union (hf.isOpen_inter_preimage
    (e.open_source.preimage continuous_snd) (isOpen_lt continuous_fst continuous_snd)) using 1
  ext q
  constructor
  · intro hq
    by_cases hq₂ : q.2 ∈ K
    · exact Or.inr ⟨hKs hq₂, lt_of_not_ge fun h ↦ hq ⟨hKs hq₂, h⟩⟩
    · exact Or.inl hq₂
  · rintro (h | ⟨-, h⟩) hq
    · exact h (hNK q hq.1 hq.2)
    · exact (not_le.2 h) hq.2

/-- For a partial homeomorphism `e : T → H` with `t ∈ e.source` and a continuous positive
`ρ : X → ℝ`, the fibre `X × {t}` lies in the interior of
`{(x, s) : s ∈ e.source, dist (e s) (e t) ≤ ρ x}`. -/
lemma subset_interior_setOf_mem_source_dist_le {X T H : Type*} [TopologicalSpace X]
    [TopologicalSpace T] [PseudoMetricSpace H] {e : OpenPartialHomeomorph T H} {t : T}
    (ht : t ∈ e.source) {ρ : X → ℝ} (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    {q : X × T | q.2 = t} ⊆
      interior {q : X × T | q.2 ∈ e.source ∧ dist (e q.2) (e t) ≤ ρ q.1} := by
  have hf : ContinuousOn (fun q : X × T ↦ (ρ q.1, dist (e q.2) (e t))) (Prod.snd ⁻¹' e.source) :=
    (hρ.comp continuous_fst).continuousOn.prodMk
      ((continuous_id.dist (continuous_const (y := e t))).comp_continuousOn
        (f := fun q : X × T ↦ e q.2) (e.continuousOn.comp continuousOn_snd fun _ h ↦ h))
  let W : Set (X × T) := Prod.snd ⁻¹' e.source ∩
    (fun q : X × T ↦ (ρ q.1, dist (e q.2) (e t))) ⁻¹' {p | p.2 < p.1}
  have hWo : IsOpen W := hf.isOpen_inter_preimage (e.open_source.preimage continuous_snd)
    (isOpen_lt continuous_snd continuous_fst)
  have hWN : W ⊆ {q : X × T | q.2 ∈ e.source ∧ dist (e q.2) (e t) ≤ ρ q.1} :=
    fun q hq ↦ ⟨hq.1, le_of_lt hq.2⟩
  intro q hq
  have hq₂ : q.2 = t := hq
  refine interior_maximal hWN hWo (?_ : q ∈ W)
  change q.2 ∈ e.source ∧ dist (e q.2) (e t) < ρ q.1
  rw [hq₂, dist_self]
  exact ⟨ht, hρpos _⟩

/-- For a closed `N ⊆ X × T` whose points have second coordinate in a compact `K`, the projection
`N → X` is a proper map. -/
lemma isProperMap_subtype_fst {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    [T2Space X] [CompactlyGeneratedSpace X] {N : Set (X × T)} (hN : IsClosed N) {K : Set T}
    (hK : IsCompact K) (hNK : ∀ q ∈ N, q.2 ∈ K) : IsProperMap fun q : N ↦ (q : X × T).1 := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_fst.comp continuous_subtype_val, fun C hC ↦ ?_⟩
  rw [Subtype.isCompact_iff]
  refine (hC.prod hK).of_isClosed_subset ?_ ?_
  · convert hN.inter (hC.isClosed.preimage continuous_fst) using 1
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩
      exact ⟨q'.2, hq'⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨q, h1⟩, h2, rfl⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨hq, hNK q.1 q.2⟩

/-- **A proper neighbourhood deformation of `X × {t}` in a chart.** Let `e` be a chart with
`t ∈ e.source` and `closedBall (e t) r₀ ⊆ e.target`, and `ρ : X → (0, r₀]` continuous. If `M`
contains `{(x, e⁻¹ z) : dist z (e t) ≤ ρ x}`, the closed neighbourhood
`N = {(x, s) : dist (e s) (e t) ≤ ρ x}` of `X × {t}`, the retraction `(x, s) ↦ (x, t)` and the
straight-line deformation in the chart form a proper neighbourhood deformation inside `M`. -/
theorem exists_properNeighbourhoodDeformation_of_chart (X : TopCat.{u})
    [TopologicalSpace.MetrizableSpace X] {T : TopCat.{u}} [T2Space T] {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    {e : OpenPartialHomeomorph T H} {t : T} (ht : t ∈ e.source) {r₀ : ℝ}
    (hr₀ : closedBall (e t) r₀ ⊆ e.target) {ρ : X → ℝ} (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x) (hρr : ∀ x, ρ x ≤ r₀) {M : Set (X × T)}
    (hM : ∀ x z, dist z (e t) ≤ ρ x → (x, e.symm z) ∈ M) :
    ∃ N : Set (X × T), IsClosed N ∧ prodSnd X T ⁻¹' {t} ⊆ interior N ∧ N ⊆ M ∧
      ∃ r : C(N, prodSnd X T ⁻¹' {t}), IsProperMap r ∧
        (∀ y : N, (y : X × T) ∈ prodSnd X T ⁻¹' {t} → (r y : X × T) = y) ∧
        ∃ G : C(N × unitInterval, X × T), IsProperMap G ∧ (∀ y, G (y, 0) = y) ∧
          (∀ y, G (y, 1) = r y) ∧
          (∀ y : N, ∀ s, (y : X × T) ∈ prodSnd X T ⁻¹' {t} → G (y, s) = y) ∧ ∀ q, G q ∈ M := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  set p₀ := e t
  set K := e.symm '' closedBall p₀ r₀
  have hKc : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono hr₀)
  set N : Set (X × T) := {q | q.2 ∈ e.source ∧ dist (e q.2) p₀ ≤ ρ q.1}
  have hNK : ∀ q ∈ N, q.2 ∈ K := fun q hq ↦
    ⟨e q.2, mem_closedBall.2 (hq.2.trans (hρr _)), e.left_inv hq.1⟩
  have hNc : IsClosed N := isClosed_setOf_mem_source_dist_le e hρ p₀ hKc.isClosed
    (fun _ ⟨_, hz, hzq⟩ ↦ hzq ▸ e.map_target (hr₀ hz)) fun q h₁ h₂ ↦ hNK q ⟨h₁, h₂⟩
  have hπ : IsProperMap fun q : N ↦ (q : X × T).1 := isProperMap_subtype_fst hNc hKc hNK
  let r : C(N, prodSnd X T ⁻¹' {t}) :=
    ⟨fun q ↦ ⟨(q.1.1, t), (mem_prodSnd_preimage_singleton X T _).2 rfl⟩,
      ((continuous_fst.comp continuous_subtype_val).prodMk continuous_const).subtype_mk _⟩
  have hr : IsProperMap r := isProperMap_of_comp_of_t2 (g := fibreProj X t) r.continuous
    (fibreProj X t).hom.continuous hπ
  have hsrcN : ∀ q : N, (q : X × T).2 ∈ e.source := fun q ↦ q.2.1
  let z : N × unitInterval → H := fun q ↦
    e (q.1 : X × T).2 + (q.2 : ℝ) • (p₀ - e (q.1 : X × T).2)
  have hz : Continuous z := by
    have h1 : Continuous fun q : N × unitInterval ↦ e (q.1 : X × T).2 :=
      e.continuousOn.comp_continuous
        (continuous_snd.comp (continuous_subtype_val.comp continuous_fst)) fun q ↦ hsrcN q.1
    exact h1.add ((continuous_subtype_val.comp continuous_snd).smul (continuous_const.sub h1))
  have hzρ : ∀ q, dist (z q) p₀ ≤ ρ (q.1 : X × T).1 := fun q ↦
    (dist_add_smul_sub_le _ _ q.2.2.1 q.2.2.2).trans q.1.2.2
  have hzt : ∀ q, z q ∈ e.target := fun q ↦ hr₀ (mem_closedBall.2 ((hzρ q).trans (hρr _)))
  let G : C(N × unitInterval, X × T) :=
    ⟨fun q ↦ ((q.1 : X × T).1, e.symm (z q)),
      (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        (e.continuousOn_symm.comp_continuous hz hzt)⟩
  have hG : IsProperMap G := isProperMap_of_comp_of_t2 (g := Prod.fst) G.continuous
    continuous_fst (hπ.comp isProperMap_fst_of_compactSpace)
  refine ⟨N, hNc, subset_interior_setOf_mem_source_dist_le ht hρ hρpos, fun q hq ↦ ?_, r, hr,
    fun q hq ↦ Prod.ext rfl (hq : (q : X × T).2 = t).symm, G, hG, fun q ↦ ?_, fun q ↦ ?_,
    fun q s hq ↦ ?_, fun q ↦ hM _ _ (hzρ q)⟩
  · have := hM q.1 (e q.2) hq.2
    rwa [e.left_inv hq.1] at this
  · change ((q : X × T).1, e.symm (e (q : X × T).2 + (0 : ℝ) • (p₀ - e (q : X × T).2))) = q
    rw [zero_smul, add_zero, e.left_inv (hsrcN q)]
  · change ((q : X × T).1, e.symm (e (q : X × T).2 + (1 : ℝ) • (p₀ - e (q : X × T).2))) =
      ((q : X × T).1, t)
    rw [one_smul, add_sub_cancel, e.left_inv ht]
  · have hq₂ : (q : X × T).2 = t := hq
    change ((q : X × T).1, e.symm (e (q : X × T).2 + (s : ℝ) • (p₀ - e (q : X × T).2))) = q
    rw [hq₂, sub_self, smul_zero, add_zero, e.left_inv ht]
    exact Prod.ext rfl hq₂.symm

/-- **The fibres `X × {t}` have arbitrarily small proper neighbourhood deformations** in `X × T`,
for `X` metrizable (Fulton's spaces, §19.1, have closed imbeddings in some `ℝᴺ`) and `T` a
Hausdorff manifold modelled on a finite-dimensional real space. -/
theorem hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton (X : TopCat.{u})
    [TopologicalSpace.MetrizableSpace X] {T : TopCat.{u}} [T2Space T] (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H] [ChartedSpace H T] (t : T) :
    HasProperNeighbourhoodDeformations (prodSnd X T ⁻¹' {t}) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  intro M hM
  set e := chartAt H t
  have ht : t ∈ e.source := mem_chart_source H t
  obtain ⟨ε₀, hε₀, hε₀t⟩ := Metric.isOpen_iff.1 e.open_target (e t) (e.map_source ht)
  have hSM' : prodSnd X T ⁻¹' {t} ⊆ interior M := subset_interior_iff_mem_nhdsSet.2 hM
  let ψ : X × H → X × T := fun q ↦ (q.1, e.symm q.2)
  have hψ : ContinuousOn ψ (Prod.snd ⁻¹' e.target) :=
    continuousOn_fst.prodMk (e.continuousOn_symm.comp continuousOn_snd fun _ h ↦ h)
  set O : Set (X × H) := Prod.snd ⁻¹' e.target ∩ ψ ⁻¹' interior M
  have hO : IsOpen O :=
    hψ.isOpen_inter_preimage (e.open_target.preimage continuous_snd) isOpen_interior
  have hpO : ∀ x : X, (x, e t) ∈ O := fun x ↦
    ⟨e.map_source ht, hSM' ((mem_prodSnd_preimage_singleton X T _).2 (e.left_inv ht))⟩
  obtain ⟨ρ, hρ, hρpos, hρε, hball⟩ := exists_continuous_radius_of_isOpen hO hpO hε₀
  exact exists_properNeighbourhoodDeformation_of_chart X ht
    ((closedBall_subset_ball (half_lt_self hε₀)).trans hε₀t) hρ hρpos hρε
    fun x z hz ↦ interior_subset (hball x z hz).2

end deformation

end borelMooreHomology

section complex

open Bundle ThomClass SingularCochain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {T : TopCat.{u}} [ChartedSpace E T] [T2Space T] (R : Type u) [CommRing R]

/-- The orientation class of a point `t` of a complex manifold is its local orientation class
for the complex orientation. -/
theorem isLocalOrientationClass_of_isOrientationClass (hT : IsOrientedAtlas E T) {t : T}
    {N : ({t} : Set T) → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)]
    [∀ x, TopologicalSpace (N x)] [TopologicalSpace (TotalSpace E N)] [FiberBundle E N]
    [_root_.VectorBundle ℂ E N] (φ : TubularNeighbourhood E N)
    {u : cohomologyWithSupports R (ModuleCat.of R R) T {t} (2 * Module.finrank ℂ E : ℕ)}
    (hu : IsOrientationClass E R φ u) :
    IsLocalOrientationClass R (complexOrientationBasisOf E) t u := by
  obtain ⟨⟨α, hα⟩, hrep⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv R ({t}ᶜ : Set T) (2 * Module.finrank ℂ E) u)
  exact ⟨α, hα, isChartOrientedCocycle_of_isThomClass R (complexOrientationBasisOf E) hT φ
    (φ.inducesOrientation_of_isOrientationCompatible hu.1) hu.2 hα hrep.symm, hrep.symm⟩

namespace borelMooreHomology

/-- **Fulton, Lemma 19.2(c)** ([BT] 2.6). Let `T` be a connected complex manifold (for Fulton a
connected non-singular complex curve, `E = ℂ`; here any finite-dimensional model `E ≠ 0`, of
complex dimension `r`), `X` a space, `pr : X × T → T` and `a ∈ H_k(X × T)`. Then
`pr^*(u_{t,T}) ∩ a ∈ H_{k-2r}(X × {t}) = H_{k-2r} X` does not depend on `t ∈ T`: for orientation
classes `u_{t,T}`, `u_{t',T}` of two points (`IsOrientationClass`), the push-forwards along
`X × {t} ≅ X` and `X × {t'} ≅ X` agree. The cap products `∩ : H^{2r}(X × T, X × T - X × {s}) ⊗
H_k(X × T) → H_{k-2r}(X × {s})` are defined because `X` is metrizable (Fulton's setting, §19.1),
via `hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton`. -/
theorem pushforward_fibreProj_capProductSupportPullback_eq_of_isOrientationClass
    [IsManifold (modelWithCornersSelf ℂ E) 1 T] [ConnectedSpace T] [Nontrivial E]
    (X : TopCat.{u}) [TopologicalSpace.MetrizableSpace X]
    (k : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (X × T)) k) {t t' : T}
    {N : ({t} : Set T) → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)]
    [∀ x, TopologicalSpace (N x)] [TopologicalSpace (TotalSpace E N)] [FiberBundle E N]
    [_root_.VectorBundle ℂ E N]
    {N' : ({t'} : Set T) → Type u} [∀ x, AddCommGroup (N' x)] [∀ x, Module ℂ (N' x)]
    [∀ x, TopologicalSpace (N' x)] [TopologicalSpace (TotalSpace E N')] [FiberBundle E N']
    [_root_.VectorBundle ℂ E N']
    (φ : TubularNeighbourhood E N) (φ' : TubularNeighbourhood E N')
    {u : cohomologyWithSupports R (ModuleCat.of R R) T {t} (2 * Module.finrank ℂ E : ℕ)}
    {u' : cohomologyWithSupports R (ModuleCat.of R R) T {t'} (2 * Module.finrank ℂ E : ℕ)}
    (hu : IsOrientationClass E R φ u) (hu' : IsOrientationClass E R φ' u') :
    (pushforward R (ModuleCat.of R R) (fibreProj X t) (isProperMap_fibreProj X t)
        (k - (2 * Module.finrank ℂ E : ℕ))).hom
        (capProductSupportPullback R (prodSnd X T) isClosed_singleton
          (hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton X E t)
          (2 * Module.finrank ℂ E : ℕ) k u a) =
      (pushforward R (ModuleCat.of R R) (fibreProj X t') (isProperMap_fibreProj X t')
          (k - (2 * Module.finrank ℂ E : ℕ))).hom
        (capProductSupportPullback R (prodSnd X T) isClosed_singleton
          (hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton X E t')
          (2 * Module.finrank ℂ E : ℕ) k u' a) := by
  have hT : IsOrientedAtlas E T := isOrientedAtlas_of_isManifold_complex T
  have hn : 0 < 2 * Module.finrank ℂ E := by
    have := Module.finrank_pos (R := ℂ) (M := E)
    omega
  exact pushforward_fibreProj_capProductSupportPullback_eq_of_isLocalOrientationClass R hT hn
    (complexOrientationBasisOf E)
    (fun s ↦ hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton X E s) k a
    (isLocalOrientationClass_of_isOrientationClass R hT φ hu)
    (isLocalOrientationClass_of_isOrientationClass R hT φ' hu')

end borelMooreHomology

end complex

section localOrientationIndependent

open SingularChain SingularCochain FundamentalClass ThomClass

variable {P : TopCat.{u}} [T2Space P] [ConnectedSpace P] {H : Type*} [NormedAddCommGroup H]
  [NormedSpace ℝ H] [FiniteDimensional ℝ H] [ChartedSpace H P] {R : Type u} [CommRing R]

/-- **The local orientation classes at two points of a connected oriented manifold have the same
image in `H^n P`** (Fulton, proof of Prop. 19.1.1, `ū_{t₁} = ū_{t₂}`; Dold VIII.13). -/
theorem cohomologyWithSupports.toCohomology_eq_of_isLocalOrientationClass
    (hP : IsOrientedAtlas H P) {n : ℕ} (hn : 0 < n) {b : Module.Basis (Fin n) ℝ H} {y₁ y₂ : P}
    {u₁ : cohomologyWithSupports R (ModuleCat.of R R) P {y₁} n}
    {u₂ : cohomologyWithSupports R (ModuleCat.of R R) P {y₂} n}
    (h₁ : IsLocalOrientationClass R b y₁ u₁) (h₂ : IsLocalOrientationClass R b y₂ u₂) :
    (cohomologyWithSupports.toCohomology R (ModuleCat.of R R) P {y₁} n).hom u₁ =
      (cohomologyWithSupports.toCohomology R (ModuleCat.of R R) P {y₂} n).hom u₂ := by
  obtain ⟨α₁, hα₁, hc₁, hrep₁⟩ := h₁
  obtain ⟨α₂, hα₂, hc₂, hrep₂⟩ := h₂
  apply (relativeSingularCohomologyEquiv R (Set.univᶜ : Set P) n).injective
  simp only [cohomologyWithSupports.toCohomology, cohomologyWithSupports.forget]
  erw [relativeSingularCohomologyEquiv_map, relativeSingularCohomologyEquiv_map, hrep₁, hrep₂,
    relCohomologyMap_mk, relCohomologyMap_mk]
  exact (Submodule.Quotient.eq _).2
    (sub_mem_relCoboundaries_of_isChartOrientedCocycle hP b hn hc₁ hc₂)

end localOrientationIndependent

end MMP
