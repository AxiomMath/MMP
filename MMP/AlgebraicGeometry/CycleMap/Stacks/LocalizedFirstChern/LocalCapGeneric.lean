module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.ThomChartGeneric
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.GenericCovering
public import MMP.AlgebraicTopology.BorelMoore.PushforwardSheets
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderFiveLemma
public import MMP.AlgebraicTopology.CapProduct.Restriction

/-!
# Borel-Moore bookkeeping for the localized first Chern class (Fulton 19.1.3)

Bundle-free lemmas of the proof of Fulton's Lemma 19.1.3: cap products with a class pulled back
along `g : Y → ℂ` read on `g⁻¹(0)`, changes of degree, push-forward along homeomorphisms, the
first coordinate of a ball product chart, and charts of open subsets of normed spaces.

## Main results

* `MMP.pushforward_setCongr_capProductSupport_map`,
  `MMP.pushforward_restrictPreimage_pushforward_setCongr_capProductSupport_map`,
  `MMP.pushforward_pushforward_capProductSupport_eq_smul`: cap products with supports.
* `MMP.ballChartFst`: the first coordinate of a ball product chart.
* `MMP.pushforward_congrDegree_apply_of_eq`, `MMP.congrDegree_restrict_apply_of_eq`,
  `MMP.congrDegree_capProductSupportPullback_eq_of_heq`: changes of degree.
* `MMP.eq_of_pushforward_homeomorph_eq`, `MMP.pushforward_homeomorph_trans_apply`:
  push-forward along homeomorphisms.
* `MMP.OpenPartialHomeomorph.injective_fderiv_of_differentiableAt`: the derivative of a
  differentiable open partial homeomorphism with differentiable inverse is injective.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set Metric
open MMP.UnderlyingSpace

namespace MMP

open borelMooreHomology BorelMooreCross

variable (R : Type) [CommRing R]

/-- Changing the closed set `T = g⁻¹(0)` of a cap product `g^* u ∩ a` to `g⁻¹(0)` itself. -/
lemma pushforward_setCongr_capProductSupport_map {Y : TopCat.{0}} (g : Y ⟶ TopCat.of ℂ)
    {T : Set Y} (hT : T = g ⁻¹' {0}) (hTc : IsClosed T) (hTd : HasProperNeighbourhoodDeformations T)
    (hg : Tᶜ ⊆ g ⁻¹' ({0}ᶜ : Set (TopCat.of ℂ)))
    (hYd : HasProperNeighbourhoodDeformations (g ⁻¹' {0})) (j k : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ℂ) {0} j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (TopCat.ofHom (Homeomorph.setCongr hT : C(T, g ⁻¹' {0})))
        (Homeomorph.setCongr hT).isProperMap (k - j)).hom
      (capProductSupport R Y hTc hTd j k
        ((relativeSingularCohomology.map R (ModuleCat.of R R) g hg j).hom u) a) =
      capProductSupportPullback R g isClosed_singleton hYd j k u a := by
  subst hT
  rw [capProductSupportPullback_apply]
  have : TopCat.ofHom ((Homeomorph.setCongr (rfl : g ⁻¹' {0} = g ⁻¹' {0})) :
      C(g ⁻¹' ({0} : Set (TopCat.of ℂ)), g ⁻¹' {0})) = 𝟙 _ := rfl
  rw [pushforward_apply_eq_of_hom_eq R (ModuleCat.of R R) this _
    (by simp [isProperMap_id])]
  rw [pushforward_id]
  rfl

/-- Transport of a cap product `(f ≫ g)^* u ∩ a`, with support `T = (f ≫ g)⁻¹(0)`, along a
proper map `f`: it is `g^* u ∩ f_* a`. -/
lemma pushforward_restrictPreimage_pushforward_setCongr_capProductSupport_map
    {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) (hf : IsProperMap f) (g : Y ⟶ TopCat.of ℂ)
    {T : Set Y'} (hT : T = f ⁻¹' (g ⁻¹' {0})) (hTc : IsClosed T)
    (hTd : HasProperNeighbourhoodDeformations T)
    (hg : Tᶜ ⊆ (f ≫ g) ⁻¹' ({0}ᶜ : Set (TopCat.of ℂ)))
    (hYd : HasProperNeighbourhoodDeformations (g ⁻¹' {0}))
    (hY'd : HasProperNeighbourhoodDeformations (f ⁻¹' (g ⁻¹' {0}))) (j k : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ℂ) {0} j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    (pushforward R (ModuleCat.of R R) (TopCat.ofHom (f.hom.restrictPreimage (g ⁻¹' {0})))
        (hf.restrictPreimage _) (k - j)).hom
      ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (Homeomorph.setCongr hT :
          C(T, f ⁻¹' (g ⁻¹' {0})))) (Homeomorph.setCongr hT).isProperMap (k - j)).hom
        (capProductSupport R Y' hTc hTd j k
          ((relativeSingularCohomology.map R (ModuleCat.of R R) (f ≫ g) hg j).hom u) a)) =
      capProductSupportPullback R g isClosed_singleton hYd j k u
        ((pushforward R (ModuleCat.of R R) f hf k).hom a) := by
  rw [pushforward_setCongr_capProductSupport_map R (f ≫ g) hT hTc hTd hg hY'd j k u a,
    capProductSupportPullback_apply, cohomologyWithSupports.pullback_comp]
  exact pushforward_restrictPreimage_capProductSupportPullback R f hf _ hYd hY'd j k _ a

/-- A cap product with a multiple `c = r • x` of a class, pushed forward twice. -/
lemma pushforward_pushforward_capProductSupport_eq_smul
    {Y' Y Y'' : TopCat.{0}} {T : Set Y'} (hTc : IsClosed T)
    (hTd : HasProperNeighbourhoodDeformations T) (j k : ℤ)
    (φ₁ : TopCat.of T ⟶ Y) (hφ₁ : IsProperMap φ₁) (φ₂ : Y ⟶ Y'') (hφ₂ : IsProperMap φ₂)
    {c x : cohomologyWithSupports R (ModuleCat.of R R) Y' T j} {r : R} (hcx : c = r • x)
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    (pushforward R (ModuleCat.of R R) φ₂ hφ₂ (k - j)).hom
      ((pushforward R (ModuleCat.of R R) φ₁ hφ₁ (k - j)).hom
        (capProductSupport R Y' hTc hTd j k c a)) =
      r • (pushforward R (ModuleCat.of R R) φ₂ hφ₂ (k - j)).hom
        ((pushforward R (ModuleCat.of R R) φ₁ hφ₁ (k - j)).hom
          (capProductSupport R Y' hTc hTd j k x a)) := by
  subst hcx
  rw [map_smul, LinearMap.smul_apply, map_smul, map_smul]

section BallChart

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- The first coordinate `p ↦ (Φ p).1 ∈ ℂ` of a ball product chart. -/
def ballChartFst {O : Opens (UnderlyingSpace ℂ X)} {B : Type} [TopologicalSpace B] {ε : ℝ}
    (Φ : regularOpensInter (𝕜 := ℂ) O ≃ₜ ball (0 : ℂ) ε × B) :
    TopCat.of (regularOpensInter (𝕜 := ℂ) O) ⟶ TopCat.of ℂ :=
  TopCat.ofHom ⟨fun p ↦ ((Φ p).1 : ℂ),
    continuous_subtype_val.comp (continuous_fst.comp Φ.continuous)⟩

/-- `ballChartFst Φ` sends `p` to the first coordinate of `Φ p`. -/
@[simp]
lemma ballChartFst_apply {O : Opens (UnderlyingSpace ℂ X)} {B : Type} [TopologicalSpace B]
    {ε : ℝ} (Φ : regularOpensInter (𝕜 := ℂ) O ≃ₜ ball (0 : ℂ) ε × B) (p) :
    ballChartFst Φ p = ((Φ p).1 : ℂ) :=
  rfl

end BallChart

/-- Proper pushforward commutes with `congrDegree` along an equality of degrees. -/
lemma pushforward_congrDegree_apply_of_eq {Y Y' : TopCat.{0}} (f : Y ⟶ Y') (hf : IsProperMap f)
    {i i' : ℤ} (h : i = i') (x : borelMooreHomology R (ModuleCat.of R R) Y i) :
    (pushforward R (ModuleCat.of R R) f hf i').hom (congrDegree R _ h x) =
      congrDegree R _ h ((pushforward R (ModuleCat.of R R) f hf i).hom x) := by
  subst h
  rfl

/-- Restriction to an open subset commutes with `congrDegree` along an equality of degrees. -/
lemma congrDegree_restrict_apply_of_eq {Y : TopCat.{0}} [T2Space Y] (V : Opens Y) {i i' : ℤ}
    (h : i = i') (x : borelMooreHomology R (ModuleCat.of R R) Y i) :
    (restrict R (ModuleCat.of R R) V i').hom (congrDegree R _ h x) =
      congrDegree R _ h ((restrict R (ModuleCat.of R R) V i).hom x) := by
  subst h
  rfl

/-- Changing the degree of the class in a cap product `g^* u ∩ a`, along an equality of degrees,
up to `congrDegree` on the result. -/
lemma congrDegree_capProductSupportPullback_eq_of_heq {Y' Y : TopCat.{0}} (g : Y' ⟶ Y)
    {T : Set Y} (hT : IsClosed T) (hTd : HasProperNeighbourhoodDeformations (g ⁻¹' T))
    {j j' : ℤ} (hj : j = j') (k : ℤ) {l : ℤ} (h₁ : k - j = l) (h₂ : k - j' = l)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y T j)
    (u' : cohomologyWithSupports R (ModuleCat.of R R) Y T j') (hu : HEq u u')
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    congrDegree R _ h₁ (capProductSupportPullback R g hT hTd j k u a) =
      congrDegree R _ h₂ (capProductSupportPullback R g hT hTd j' k u' a) := by
  subst hj
  cases hu
  rfl

/-- Push-forward along a homeomorphism is injective. -/
lemma eq_of_pushforward_homeomorph_eq {W B : Type} [TopologicalSpace W] [TopologicalSpace B]
    (φ : W ≃ₜ B) (n : ℤ) {x y : borelMooreHomology R (ModuleCat.of R R) (TopCat.of W) n}
    (h : (pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(W, B))) φ.isProperMap n).hom x =
      (pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(W, B))) φ.isProperMap n).hom y) :
    x = y := by
  rw [← pushforward_homeomorph_symm_apply R _ φ n x, h, pushforward_homeomorph_symm_apply]

/-- Push-forward along a composite of two homeomorphisms. -/
lemma pushforward_homeomorph_trans_apply {A B C : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] (e₁ : A ≃ₜ B) (e₂ : B ≃ₜ C) (n : ℤ)
    (x : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) n) :
    (pushforward R (ModuleCat.of R R) (TopCat.ofHom ((e₁.trans e₂) : C(A, C)))
        (e₁.trans e₂).isProperMap n).hom x =
      (pushforward R (ModuleCat.of R R) (TopCat.ofHom (e₂ : C(B, C))) e₂.isProperMap n).hom
        ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (e₁ : C(A, B))) e₁.isProperMap n).hom
          x) := by
  rw [pushforward_pushforward_eq_comp]
  rfl

/-- A chart of an open subset `V` of a topological space, from its standard atlas, is the
inclusion. -/
lemma opens_atlas_apply {E : Type*} [TopologicalSpace E] (V : Opens E)
    {c : OpenPartialHomeomorph V E} (hc : c ∈ atlas E V) (b : V) : c b = b.1 := by
  obtain ⟨x, hx⟩ := mem_iUnion.1 hc
  rw [mem_singleton_iff, chartAt_self_eq] at hx
  subst hx
  rfl

/-- The derivative of an open partial homeomorphism, differentiable at `z` with inverse
differentiable at `ψ z`, is injective. -/
lemma OpenPartialHomeomorph.injective_fderiv_of_differentiableAt {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (ψ : OpenPartialHomeomorph E F) {z : E} (hz : z ∈ ψ.source)
    (h₁ : DifferentiableAt 𝕜 ψ z) (h₂ : DifferentiableAt 𝕜 ψ.symm (ψ z)) :
    Function.Injective (fderiv 𝕜 ψ z) := by
  have hcomp := h₂.hasFDerivAt.comp z h₁.hasFDerivAt
  have hid : (ψ.symm ∘ ψ) =ᶠ[nhds z] id :=
    Filter.eventually_of_mem (ψ.open_source.mem_nhds hz) fun y hy ↦ ψ.left_inv hy
  have huniq := hcomp.unique ((hasFDerivAt_id z).congr_of_eventuallyEq hid)
  intro a b hab
  have h1 := congrArg (fun L ↦ L a) huniq
  have h2 := congrArg (fun L ↦ L b) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
  rw [← h1, ← h2, hab]

end MMP
