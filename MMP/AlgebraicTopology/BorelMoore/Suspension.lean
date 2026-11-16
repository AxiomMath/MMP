module

public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Transport
public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.CapExterior
public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.PointCross
public import MMP.AlgebraicTopology.CapProduct.CupSupport
public import MMP.AlgebraicTopology.FundamentalClass.Euclidean
public import MMP.AlgebraicTopology.OrientationClass.CapPoint

/-!
# The suspension of a class with supports and its cap product

For spaces `Y`, `Z`, a closed `A ⊆ Y`, a point `z₀ ∈ Z` and `v ∈ H^n(Z, Z - z₀)`, the
*suspension* of `c ∈ H^i(Y, Y - A)` is `pr₁^* c ∪ pr₂^* v ∈ H^{i+n}(Y × Z, Y × Z - A × z₀)`.
When `v ∩ b` is the class of the point `z₀` (`b ∈ H_n Z`), its cap product with `a × b` is the
image of `c ∩ a` under the slice `A ≅ A × z₀`.

## Main definitions

* `MMP.borelMooreHomology.suspension`: the suspension `c ↦ pr₁^* c ∪ pr₂^* v`.
* `MMP.borelMooreHomology.euclideanSuspension`: the suspension
  `H^i(ℝ^m, ℝ^m - A) → H^{i+1}(ℝ^{m+1}, ℝ^{m+1} - A × 0)`.

## Main results

* `MMP.borelMooreHomology.capProductSupport_cup_pullback_exteriorProduct`:
  `(pr₁^* c ∪ pr₂^* v) ∩ (a × b) = s_*(c ∩ a)` when `v ∩ b = [z₀]`.
* `MMP.borelMooreHomology.capProductSupport_euclideanSuspension`: the euclidean form of this
  identity.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Set Simplicial TensorProduct Topology
  MMP.BorelMooreCross MMP.BorelMooreCap MMP.SingularCross

universe u

namespace MMP

namespace BorelMooreCap

/-- The projection `X × Y → X`. -/
abbrev prFst (X Y : TopCat.{u}) : TopCat.of (X × Y) ⟶ X := TopCat.ofHom ContinuousMap.fst

end BorelMooreCap

namespace borelMooreHomology

variable (R : Type u) [CommRing R]

section slice

variable (Y Z : TopCat.{u}) (A : Set Y) (z₀ : Z)

/-- The slice `Y ≅ pr₂⁻¹ z₀ ⊆ Y × Z`, `y ↦ (y, z₀)`. -/
def sliceHomeomorph : Y ≃ₜ (prSnd Y Z ⁻¹' ({z₀} : Set Z)) where
  toFun y := ⟨(y, z₀), rfl⟩
  invFun p := p.1.1
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl p.2.symm)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The slice `A ≅ pr₁⁻¹ A ∩ pr₂⁻¹ z₀ ⊆ Y × Z`, `y ↦ (y, z₀)`. -/
def sliceInterHomeomorph :
    A ≃ₜ (prFst Y Z ⁻¹' A ∩ prSnd Y Z ⁻¹' ({z₀} : Set Z) : Set (TopCat.of (Y × Z))) where
  toFun y := ⟨(y.1, z₀), y.2, rfl⟩
  invFun p := ⟨p.1.1, p.2.1⟩
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl p.2.2.symm)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The slice `Y → pr₂⁻¹ z₀`, as a morphism. -/
abbrev slice : Y ⟶ TopCat.of (prSnd Y Z ⁻¹' ({z₀} : Set Z)) :=
  TopCat.ofHom (sliceHomeomorph Y Z z₀ : C(Y, _))

/-- The slice `A → pr₁⁻¹ A ∩ pr₂⁻¹ z₀`, as a morphism. -/
abbrev sliceInter :
    TopCat.of A ⟶ TopCat.of (prFst Y Z ⁻¹' A ∩ prSnd Y Z ⁻¹' ({z₀} : Set Z) :
      Set (TopCat.of (Y × Z))) :=
  TopCat.ofHom (sliceInterHomeomorph Y Z A z₀ : C(A, _))

end slice

/-- The cap product with a degree-cast homology class is the degree cast of the cap product. -/
lemma capProductSupport_congrDegree_right (Y : TopCat.{u}) {X : Set Y} (hX : IsClosed X)
    (hXd : HasProperNeighbourhoodDeformations X) (j : ℤ) {k k' : ℤ} (h : k = k')
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    capProductSupport R Y hX hXd j k' c (congrDegree R Y h a) =
      congrDegree R (TopCat.of X) (by rw [h]) (capProductSupport R Y hX hXd j k c a) := by
  subst h
  rfl

/-- If `x` and `y` have equal casts to a common degree, then the cast of `x` is `y`. -/
lemma congrDegree_eq_of_congrDegree_eq (X : TopCat.{u}) {i j l : ℤ} (h₁ : i = l) (h₂ : j = l)
    (h₃ : i = j) (x : borelMooreHomology R (ModuleCat.of R R) X i)
    (y : borelMooreHomology R (ModuleCat.of R R) X j)
    (h : congrDegree R X h₁ x = congrDegree R X h₂ y) : congrDegree R X h₃ x = y := by
  subst h₁ h₂
  exact h

/-- **Cap product with a pulled-back point dual.** For `v ∈ H^n(Z, Z - z₀)` and `b ∈ H_n Z` with
`v ∩ b = [z₀]` (the class of a single `0`-simplex), and `a ∈ H_k Y`:
`pr₂^* v ∩ (a × b) = s_* a` in `H_k(pr₂⁻¹ z₀)`, `s : Y ≅ pr₂⁻¹ z₀` the slice. -/
theorem capProductSupport_pullback_prSnd_exteriorProduct_of_point (Y Z : TopCat.{u}) {z₀ : Z}
    (hz : IsClosed ({z₀} : Set Z)) (hzd : HasProperNeighbourhoodDeformations ({z₀} : Set Z))
    (hWd : HasProperNeighbourhoodDeformations (prSnd Y Z ⁻¹' ({z₀} : Set Z)))
    (τ : Simp (TopCat.of ({z₀} : Set Z)) 0) (d : Cyc (R := R) (TopCat.of ({z₀} : Set Z)) 0)
    (hd : coeff R d.1 τ = 1) (hd₀ : ∀ τ', τ' ≠ τ → coeff R d.1 τ' = 0) (k n : ℕ)
    (v : cohomologyWithSupports R (ModuleCat.of R R) Z {z₀} n)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k)
    (b : borelMooreHomology R (ModuleCat.of R R) Z n)
    (hv : congrDegree R _ (by simp) (capProductSupport R Z hz hzd n n v b) =
      (homologyEquiv R (TopCat.of ({z₀} : Set Z)) 0).symm (Submodule.Quotient.mk d)) :
    capProductSupport R (TopCat.of (Y × Z)) (hz.preimage (prSnd Y Z).hom.continuous) hWd n
        (k + n) ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd Y Z) {z₀} n).hom v)
        (exteriorProduct R Y Z k n (a ⊗ₜ b)) =
      congrDegree R _ (by ring)
        ((pushforward R (ModuleCat.of R R) (slice Y Z z₀) (sliceHomeomorph Y Z z₀).isProperMap
          k).hom a) := by
  let s₀ : Y ⟶ TopCat.of (Y × ({z₀} : Set Z)) :=
    TopCat.ofHom ((Homeomorph.prodUnique Y ({z₀} : Set Z)).symm : C(Y, _))
  have hs₀ : IsProperMap s₀ := (Homeomorph.prodUnique Y ({z₀} : Set Z)).symm.isProperMap
  have hpt := exteriorProduct_tmul_pointCycle R s₀ hs₀ τ
    (fun x ↦ Prod.ext rfl (Subsingleton.elim _ _)) d hd hd₀ k a
  have hcap : capProductSupport R Z hz hzd n n v b =
      congrDegree R _ (by simp)
        ((homologyEquiv R (TopCat.of ({z₀} : Set Z)) 0).symm (Submodule.Quotient.mk d)) := by
    rw [← hv, congrDegree_congrDegree, congrDegree_self]
    rfl
  have hext := exteriorProduct_capProductSupport_pullback_prSnd R Y Z hz hzd hWd k n n v a b
  rw [hcap, exteriorProduct_congrDegree_right, hpt, congrDegree_congrDegree,
    pushforward_congrDegree, ← ModuleCat.comp_apply, ← pushforward_comp,
    pushforward_congr_hom R (show s₀ ≫ prodPreimage Y ({z₀} : Set Z) = slice Y Z z₀ from rfl) _
      (sliceHomeomorph Y Z z₀).isProperMap] at hext
  exact (congrDegree_eq_of_congrDegree_eq R _ _ _ _ _ _ hext).symm

/-- If `f ≫ g = h`, then `g_* (f_* x) = h_* x`. -/
lemma pushforward_pushforward_apply_of_comp_eq {X X' X'' : TopCat.{u}} (f : X ⟶ X')
    (g : X' ⟶ X'') (h : X ⟶ X'') (hf : IsProperMap f) (hg : IsProperMap g) (hh : IsProperMap h)
    (e : f ≫ g = h) (i : ℤ) (x : borelMooreHomology R (ModuleCat.of R R) X i) :
    (pushforward R (ModuleCat.of R R) g hg i).hom
        ((pushforward R (ModuleCat.of R R) f hf i).hom x) =
      (pushforward R (ModuleCat.of R R) h hh i).hom x := by
  subst e
  rw [← ModuleCat.comp_apply, ← pushforward_comp]

/-- The pull-back of `c` along `Y ≅ pr₂⁻¹ z₀ ⊆ Y × Z → Y` is `c`. -/
lemma pullback_slice_pullback_subsetInclusion_pullback_prFst (Y Z : TopCat.{u}) {A : Set Y}
    (z₀ : Z) (i : ℤ) (c : cohomologyWithSupports R (ModuleCat.of R R) Y A i) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) (slice Y Z z₀) _ i).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (subsetInclusion (prSnd Y Z ⁻¹' ({z₀} : Set Z))) _ i).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prFst Y Z) A i).hom c)) = c := by
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← cohomologyWithSupports.pullback_comp,
    ← cohomologyWithSupports.pullback_comp]
  change (cohomologyWithSupports.pullback R (ModuleCat.of R R) (𝟙 Y) A i).hom c = c
  rw [cohomologyWithSupports.pullback_id]
  rfl

/-- **The cap product of a suspension.** Let `A ⊆ Y` be closed, `z₀ ∈ Z` a closed point,
`v ∈ H^n(Z, Z - z₀)` and `b ∈ H_n Z` with `v ∩ b = [z₀]` (the class of a single `0`-simplex).
For `c ∈ H^i(Y, Y - A)` and `a ∈ H_k Y`, the suspension `pr₁^* c ∪ pr₂^* v` satisfies
`(pr₁^* c ∪ pr₂^* v) ∩ (a × b) = s_*(c ∩ a)` in `H_{k-i}(A × z₀)`, `s : A ≅ A × z₀` the slice. -/
theorem capProductSupport_cup_pullback_exteriorProduct (Y Z : TopCat.{u}) {A : Set Y}
    (hA : IsClosed A) (hAd : HasProperNeighbourhoodDeformations A) {z₀ : Z}
    (hz : IsClosed ({z₀} : Set Z)) (hzd : HasProperNeighbourhoodDeformations ({z₀} : Set Z))
    (hWd : HasProperNeighbourhoodDeformations (prSnd Y Z ⁻¹' ({z₀} : Set Z)))
    (hXWd : HasProperNeighbourhoodDeformations
      (prFst Y Z ⁻¹' A ∩ prSnd Y Z ⁻¹' ({z₀} : Set Z)))
    (hXd : HasProperNeighbourhoodDeformations
      (subsetInclusion (prSnd Y Z ⁻¹' ({z₀} : Set Z)) ⁻¹' (prFst Y Z ⁻¹' A)))
    (τ : Simp (TopCat.of ({z₀} : Set Z)) 0) (d : Cyc (R := R) (TopCat.of ({z₀} : Set Z)) 0)
    (hd : coeff R d.1 τ = 1) (hd₀ : ∀ τ', τ' ≠ τ → coeff R d.1 τ' = 0) (i : ℤ) (k n : ℕ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y A i)
    (v : cohomologyWithSupports R (ModuleCat.of R R) Z {z₀} n)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k)
    (b : borelMooreHomology R (ModuleCat.of R R) Z n)
    (hv : congrDegree R _ (by simp) (capProductSupport R Z hz hzd n n v b) =
      (homologyEquiv R (TopCat.of ({z₀} : Set Z)) 0).symm (Submodule.Quotient.mk d)) :
    congrDegree R _ (by ring)
      (capProductSupport R (TopCat.of (Y × Z))
        ((hA.preimage (prFst Y Z).hom.continuous).inter (hz.preimage (prSnd Y Z).hom.continuous))
        hXWd (i + n) (k + n)
        (cohomologyWithSupports.cup R (TopCat.of (Y × Z)) (hA.preimage (prFst Y Z).hom.continuous)
          (hz.preimage (prSnd Y Z).hom.continuous) i n
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prFst Y Z) A i).hom c)
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd Y Z) {z₀} n).hom v))
        (exteriorProduct R Y Z k n (a ⊗ₜ b))) =
      (pushforward R (ModuleCat.of R R) (sliceInter Y Z A z₀)
        (sliceInterHomeomorph Y Z A z₀).isProperMap (k - i)).hom
        (capProductSupport R Y hA hAd i k c a) := by
  have hX : IsClosed (prFst Y Z ⁻¹' A) := hA.preimage (prFst Y Z).hom.continuous
  have hW : IsClosed (prSnd Y Z ⁻¹' ({z₀} : Set Z)) := hz.preimage (prSnd Y Z).hom.continuous
  have hX' : IsClosed (subsetInclusion (prSnd Y Z ⁻¹' ({z₀} : Set Z)) ⁻¹' (prFst Y Z ⁻¹' A)) :=
    hX.preimage (subsetInclusion _).hom.continuous
  have h1 := capProductSupport_cup R (TopCat.of (Y × Z)) hX hW hWd hXWd hXd i n (k + n)
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prFst Y Z) A i).hom c)
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd Y Z) {z₀} n).hom v)
    (exteriorProduct R Y Z k n (a ⊗ₜ b))
  have hAd' : HasProperNeighbourhoodDeformations
      (slice Y Z z₀ ⁻¹' (subsetInclusion (prSnd Y Z ⁻¹' ({z₀} : Set Z)) ⁻¹' (prFst Y Z ⁻¹' A))) :=
    hAd
  rw [capProductSupport_pullback_prSnd_exteriorProduct_of_point R Y Z hz hzd hWd τ d hd hd₀ k n
      v a b hv, capProductSupportPullback_apply, capProductSupport_congrDegree_right,
    ← pushforward_restrictPreimage_capProductSupportPullback R (slice Y Z z₀)
      (sliceHomeomorph Y Z z₀).isProperMap hX' hXd hAd', capProductSupportPullback_apply,
    pullback_slice_pullback_subsetInclusion_pullback_prFst, pushforward_congrDegree] at h1
  refine congrDegree_eq_of_congrDegree_eq R _ _ _ _ _ _ (h1.trans (congrArg _ ?_))
  exact pushforward_pushforward_apply_of_comp_eq R _ _ (sliceInter Y Z A z₀) _ _
    (sliceInterHomeomorph Y Z A z₀).isProperMap rfl _ _

/-- **Duality maps and homeomorphisms.** For a homeomorphism `φ : M ≅ M'`, closed `A ⊆ M`,
`μ ∈ H_n M` and `c ∈ H^{n-k}(M, M - A)`: `c ∩ μ` is carried by `φ⁻¹ : φ(A) ≅ A` from
`(φ⁻¹)^* c ∩ φ_* μ`. -/
theorem pushforward_dualityMap_pullback_symm {M M' : TopCat.{u}} (φ : M ≃ₜ M') {A : Set M}
    (hA : IsClosed A) (hAd : HasProperNeighbourhoodDeformations A)
    (hA'd : HasProperNeighbourhoodDeformations (φ.symm ⁻¹' A)) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) M n) (k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)) :
    (pushforward R (ModuleCat.of R R)
        (TopCat.ofHom ((φ.symm : C(M', M)).restrictPreimage A))
        (φ.symm.isProperMap.restrictPreimage A) k).hom
      (dualityMap R (hA.preimage φ.symm.continuous) hA'd
        ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(M, M'))) φ.isProperMap n).hom μ) k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (φ.symm : C(M', M))) A (n - k)).hom c)) =
      dualityMap R hA hAd μ k c := by
  rw [pushforward_dualityMap_pullback R (TopCat.ofHom (φ.symm : C(M', M))) φ.symm.isProperMap hA
    hAd hA'd, pushforward_pushforward_apply_of_comp_eq R _ _ (𝟙 M) _ _
      (by simpa using isProperMap_id) (by ext x; exact φ.symm_apply_apply x), pushforward_id]
  rfl

/-- The *suspension* `c ↦ pr₁^* c ∪ pr₂^* v`, `H^i(Y, Y - A) → H^{i+n}(Y × Z, Y × Z - A × z₀)`,
for `v ∈ H^n(Z, Z - z₀)`. -/
def suspension (Y Z : TopCat.{u}) {A : Set Y} (hA : IsClosed A) {z₀ : Z}
    (hz : IsClosed ({z₀} : Set Z)) {n : ℕ}
    (v : cohomologyWithSupports R (ModuleCat.of R R) Z {z₀} n) (i : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y A i →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Y × Z))
        (prFst Y Z ⁻¹' A ∩ prSnd Y Z ⁻¹' ({z₀} : Set Z)) (i + n) :=
  (cohomologyWithSupports.cup R (TopCat.of (Y × Z)) (hA.preimage (prFst Y Z).hom.continuous)
      (hz.preimage (prSnd Y Z).hom.continuous) i n).flip
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd Y Z) {z₀} n).hom v) ∘ₗ
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) (prFst Y Z) A i).hom

/-- The suspension of `c` is `pr₁^* c ∪ pr₂^* v`. -/
lemma suspension_apply (Y Z : TopCat.{u}) {A : Set Y} (hA : IsClosed A) {z₀ : Z}
    (hz : IsClosed ({z₀} : Set Z)) {n : ℕ}
    (v : cohomologyWithSupports R (ModuleCat.of R R) Z {z₀} n) (i : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y A i) :
    suspension R Y Z hA hz v i c =
      cohomologyWithSupports.cup R (TopCat.of (Y × Z)) (hA.preimage (prFst Y Z).hom.continuous)
        (hz.preimage (prSnd Y Z).hom.continuous) i n
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prFst Y Z) A i).hom c)
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd Y Z) {z₀} n).hom v) :=
  rfl

open FundamentalClass SingularChain SingularCochain in
/-- **The class of a point.** On a one-point space `X`, a class `ν ∈ H_0 X` which is locally the
class of the point is the class `[d]` of any `0`-cycle `d` with coefficient `1` on the
`0`-simplex. -/
theorem eq_homologyEquiv_symm_mk_of_isLocallyClassOf {X : TopCat.{u}} [Subsingleton X] {x : X}
    {Δ : Simplex X 0} {ν : borelMooreHomology R (ModuleCat.of R R) X (0 : ℕ)}
    (hν : IsLocallyClassOf R ν x Δ) (τ : Simp X 0) (d : Cyc (R := R) X 0)
    (hd : coeff R d.1 τ = 1) :
    ν = (homologyEquiv R X 0).symm (Submodule.Quotient.mk d) := by
  obtain ⟨w₀, hw⟩ := Submodule.Quotient.mk_surjective _ (homologyEquiv R X 0 ν)
  let w : Cyc (R := R) X 0 := w₀
  have hνw : ν = (homologyEquiv R X 0).symm (Submodule.Quotient.mk w) :=
    (LinearEquiv.eq_symm_apply _).2 hw.symm
  have hφ : (fun _ ↦ (1 : R) : Simplex X 0 → R) ∈ relCocycles R ({x}ᶜ : Set X) 0 := by
    refine (mem_relCocycles_iff R _ 0 _).2 ⟨fun σ hσ ↦ ?_, ?_⟩
    · exact absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp [Subsingleton.elim (σ _) x])
    · ext σ
      simp [coboundary_apply, Fin.sum_univ_two]
  have hloc :=
    hν (((borelMooreChainComplex R (ModuleCat.of R R) X).sc 0).moduleCatCyclesIso.inv.hom w)
    (by rw [hνw, homologyEquiv_symm_mk_eq]; exact (ConcreteCategory.congr_hom
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X 0).inv_hom_id _).symm)
    _ hφ
  rw [iCycles_moduleCatCyclesIso_inv, localPairing_of_subsingleton _ _ Δ] at hloc
  have hS : ∀ σ : Simp X 0, σ = τ := fun σ ↦
    (X.toSSetObjEquiv _).injective (ContinuousMap.ext fun _ ↦ Subsingleton.elim _ _)
  haveI : Subsingleton (Simp X 0) := ⟨fun a b ↦ (hS a).trans (hS b).symm⟩
  have hwd : w = d := by
    refine Subtype.ext (coeff_injective R (funext fun σ ↦ ?_))
    rw [hS σ, hd]
    rw [finsum_eq_single _ τ (fun σ hσ ↦ absurd (hS σ) hσ)] at hloc
    simp only [mul_one] at hloc
    exact hloc
  rw [hνw, hwd]

section pointCycle

variable {Z : TopCat.{u}} (z₀ : Z)

/-- The `0`-simplex of the point `{z₀}`. -/
def singletonSimplex : Simp (TopCat.of ({z₀} : Set Z)) 0 :=
  ((TopCat.of ({z₀} : Set Z)).toSSetObjEquiv (op ⦋0⦌)).symm (ContinuousMap.const _ ⟨z₀, rfl⟩)

/-- The `0`-cycle `[z₀]` of the point `{z₀}`. -/
def singletonCycle : Cyc (R := R) (TopCat.of ({z₀} : Set Z)) 0 :=
  ⟨FundamentalClass.singleChain R (singletonSimplex z₀), by
    rw [mem_cyc_iff, (BM R (TopCat.of ({z₀} : Set Z))).shape 0 (0 - 1) (by simp)]
    rfl⟩

/-- The coefficient of `[z₀]` on the `0`-simplex of `{z₀}` is `1`. -/
@[simp]
lemma coeff_singletonCycle_self :
    coeff R (singletonCycle R z₀).1 (singletonSimplex z₀) = 1 := by
  simp [coeff, singletonCycle, FundamentalClass.singleChain]

/-- The coefficient of `[z₀]` on any other `0`-simplex is `0`. -/
lemma coeff_singletonCycle_of_ne {τ : Simp (TopCat.of ({z₀} : Set Z)) 0}
    (h : τ ≠ singletonSimplex z₀) : coeff R (singletonCycle R z₀).1 τ = 0 := by
  simp [coeff, singletonCycle, FundamentalClass.singleChain, h]

end pointCycle

end borelMooreHomology

/-- The atlas of a normed space, charted over itself, is oriented. -/
theorem isOrientedAtlas_self (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :
    IsOrientedAtlas H H := by
  intro e he e' he' x _
  rw [chartedSpaceSelf_atlas] at he he'
  subst he he'
  have h : ⇑((OpenPartialHomeomorph.refl H).symm.trans (OpenPartialHomeomorph.refl H)) = id :=
    rfl
  rw [h]
  refine ⟨differentiableAt_id, ?_⟩
  rw [fderiv_id]
  simp

namespace borelMooreHomology

open FundamentalClass in
/-- **The point dual on the real line.** There is `u ∈ H^1(ℝ, ℝ - 0)` with `u ∩ μ_ℝ = [0]`. -/
theorem exists_capProductSupport_realLineClass_eq (R : Type) [CommRing R]
    (h0d : HasProperNeighbourhoodDeformations ({0} : Set (TopCat.of ℝ))) :
    ∃ u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ℝ) {0} (1 : ℕ),
      congrDegree R _ (by simp)
          (capProductSupport R (TopCat.of ℝ) isClosed_singleton h0d (1 : ℕ) (1 : ℕ) u
            (realLineClass R)) =
        (homologyEquiv R (TopCat.of ({0} : Set ℝ)) 0).symm
          (Submodule.Quotient.mk (singletonCycle R (0 : TopCat.of ℝ))) := by
  obtain ⟨u, hu⟩ := exists_isLocalOrientationClass (T := TopCat.of ℝ) (R := R)
    (isOrientedAtlas_self ℝ) one_pos (Module.Basis.singleton (Fin 1) ℝ) (0 : ℝ)
  refine ⟨u, ?_⟩
  haveI : Subsingleton (TopCat.of ({0} : Set (TopCat.of ℝ))) :=
    inferInstanceAs (Subsingleton ({0} : Set ℝ))
  have hc := isLocallyClassOf_capProductSupport_of_isLocalOrientationClass (M := ℝ)
    (Module.Basis.singleton (Fin 1) ℝ) h0d (isFundamentalClass_realLineClass (R := R)) hu
    (by simp) default (ContinuousMap.const _ default)
  exact eq_homologyEquiv_symm_mk_of_isLocallyClassOf R hc (singletonSimplex (0 : TopCat.of ℝ)) _
    (coeff_singletonCycle_self R _)

open FundamentalClass in
/-- **The point dual on the lifted real line.** For the copy `ULift ℝ` of the real line in the
universe `u`, there is `v ∈ H^1(ULift ℝ, ULift ℝ - 0)` with `v ∩ liftLineClass = [0]`. -/
theorem exists_capProductSupport_liftLineClass_eq (R : Type u) [CommRing R]
    (h0d : HasProperNeighbourhoodDeformations ({0} : Set (TopCat.of (ULift.{u} ℝ)))) :
    ∃ v : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ)) {0} (1 : ℕ),
      congrDegree R _ (by simp)
          (capProductSupport R (TopCat.of (ULift.{u} ℝ)) isClosed_singleton h0d (1 : ℕ) (1 : ℕ) v
            (liftLineClass R)) =
        (homologyEquiv R (TopCat.of ({0} : Set (ULift.{u} ℝ))) 0).symm
          (Submodule.Quotient.mk (singletonCycle R (0 : TopCat.of (ULift.{u} ℝ)))) := by
  obtain ⟨v, hv⟩ := exists_isLocalOrientationClass (T := TopCat.of (ULift.{u} ℝ)) (R := R)
    (isOrientedAtlas_self (ULift.{u} ℝ)) one_pos liftLineBasis (0 : ULift.{u} ℝ)
  refine ⟨v, ?_⟩
  haveI : Subsingleton (TopCat.of ({0} : Set (TopCat.of (ULift.{u} ℝ)))) :=
    inferInstanceAs (Subsingleton ({0} : Set (ULift.{u} ℝ)))
  have hc := isLocallyClassOf_capProductSupport_of_isLocalOrientationClass (M := ULift.{u} ℝ)
    liftLineBasis h0d (isFundamentalClass_liftLineClass (R := R)) hv
    (by simp) default (ContinuousMap.const _ default)
  exact eq_homologyEquiv_symm_mk_of_isLocallyClassOf R hc
    (singletonSimplex (0 : TopCat.of (ULift.{u} ℝ))) _ (coeff_singletonCycle_self R _)

open FundamentalClass

variable (R : Type u) [CommRing R]

/-- The set `{x ∈ ℝ^{m+1} | (x₀, …, x_{m-1}) ∈ A, x_m = 0}`, the image of `A × 0` under
`ℝ^m × ℝ ≅ ℝ^{m+1}`. -/
abbrev suspensionSet {m : ℕ} (A : Set (Fin m → ULift.{u} ℝ)) :
    Set (TopCat.of (Fin (m + 1) → ULift.{u} ℝ)) :=
  (snocHomeomorph m).symm ⁻¹'
    (prFst (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) ⁻¹' A ∩
      prSnd (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) ⁻¹'
        ({0} : Set (ULift.{u} ℝ)))

/-- The euclidean suspension `H^i(ℝ^m, ℝ^m - A) → H^{i+1}(ℝ^{m+1}, ℝ^{m+1} - A × 0)`: the
suspension by `u ∈ H^1(ℝ, ℝ - 0)`, carried to `ℝ^{m+1}` along `ℝ^m × ℝ ≅ ℝ^{m+1}`. -/
def euclideanSuspension {m : ℕ} {A : Set (Fin m → ULift.{u} ℝ)} (hA : IsClosed A)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ)) {0} (1 : ℕ))
    (i : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin m → ULift.{u} ℝ)) A i →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin (m + 1) → ULift.{u} ℝ))
        (suspensionSet A) (i + (1 : ℕ)) :=
  (cohomologyWithSupports.pullback R (ModuleCat.of R R)
      (TopCat.ofHom ((snocHomeomorph m).symm :
        C(Fin (m + 1) → ULift.{u} ℝ, (Fin m → ULift.{u} ℝ) × ULift.{u} ℝ))) _
      (i + (1 : ℕ))).hom ∘ₗ
    suspension R (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) hA
      (z₀ := (0 : ULift.{u} ℝ)) isClosed_singleton u i

/-- **The cap product of a euclidean suspension.** For closed `A ⊆ ℝ^m`, `u ∈ H^1(ℝ, ℝ - 0)`
with `u ∩ μ_ℝ = [0]` and `c ∈ H^i(ℝ^m, ℝ^m - A)`: `σ(c) ∩ μ_{ℝ^{m+1}}`, carried to `A × 0` by
`ℝ^{m+1} ≅ ℝ^m × ℝ`, is `s_*(c ∩ μ_{ℝ^m})`, `s : A ≅ A × 0` the slice. -/
theorem capProductSupport_euclideanSuspension (m : ℕ) {A : Set (Fin m → ULift.{u} ℝ)}
    (hA : IsClosed A) (hAd : HasProperNeighbourhoodDeformations A)
    (h0d : HasProperNeighbourhoodDeformations ({0} : Set (TopCat.of (ULift.{u} ℝ))))
    (hWd : HasProperNeighbourhoodDeformations
      (prSnd (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) ⁻¹'
        ({0} : Set (ULift.{u} ℝ))))
    (hXWd : HasProperNeighbourhoodDeformations
      (prFst (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) ⁻¹' A ∩
        prSnd (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) ⁻¹'
          ({0} : Set (ULift.{u} ℝ))))
    (hXd : HasProperNeighbourhoodDeformations
      (subsetInclusion (prSnd (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) ⁻¹'
          ({0} : Set (ULift.{u} ℝ))) ⁻¹'
        (prFst (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) ⁻¹' A)))
    (hEd : HasProperNeighbourhoodDeformations (suspensionSet A))
    (τ : Simp (TopCat.of ({0} : Set (ULift.{u} ℝ))) 0)
    (d : Cyc (R := R) (TopCat.of ({0} : Set (ULift.{u} ℝ))) 0)
    (hd : coeff R d.1 τ = 1) (hd₀ : ∀ τ', τ' ≠ τ → coeff R d.1 τ' = 0)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ)) {0} (1 : ℕ))
    (hu : congrDegree R _ (by simp)
        (capProductSupport R (TopCat.of (ULift.{u} ℝ)) isClosed_singleton h0d (1 : ℕ) (1 : ℕ) u
          (liftLineClass R)) =
      (homologyEquiv R (TopCat.of ({0} : Set (ULift.{u} ℝ))) 0).symm (Submodule.Quotient.mk d))
    (i : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin m → ULift.{u} ℝ)) A i) :
    congrDegree R _ (by push_cast; ring)
      ((pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (((snocHomeomorph m).symm :
          C(Fin (m + 1) → ULift.{u} ℝ, (Fin m → ULift.{u} ℝ) × ULift.{u} ℝ)).restrictPreimage
          (prFst (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) ⁻¹' A ∩
            prSnd (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) ⁻¹'
              ({0} : Set (ULift.{u} ℝ)))))
        ((snocHomeomorph m).symm.isProperMap.restrictPreimage _)
        (((m + 1 : ℕ) : ℤ) - (i + (1 : ℕ)))).hom
        (capProductSupport R (TopCat.of (Fin (m + 1) → ULift.{u} ℝ))
          ((((hA.preimage (prFst _ _).hom.continuous).inter
            (isClosed_singleton.preimage (prSnd _ _).hom.continuous))).preimage
              (snocHomeomorph m).symm.continuous) hEd (i + (1 : ℕ)) ((m + 1 : ℕ) : ℤ)
          (euclideanSuspension R hA u i c) (euclideanClass R (m + 1)))) =
      (pushforward R (ModuleCat.of R R)
        (sliceInter (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) A (0 : ULift.{u} ℝ))
        (sliceInterHomeomorph (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) A
          (0 : ULift.{u} ℝ)).isProperMap
        ((m : ℕ) - i)).hom
        (capProductSupport R (TopCat.of (Fin m → ULift.{u} ℝ)) hA hAd i (m : ℕ) c
          (euclideanClass R m)) := by
  have hS : IsClosed (prFst (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) ⁻¹' A ∩
      prSnd (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) ⁻¹'
        ({0} : Set (ULift.{u} ℝ))) :=
    (hA.preimage (prFst _ _).hom.continuous).inter
      (isClosed_singleton.preimage (prSnd _ _).hom.continuous)
  have key := pushforward_restrictPreimage_capProductSupportPullback R
    (TopCat.ofHom ((snocHomeomorph m).symm :
        C(Fin (m + 1) → ULift.{u} ℝ, (Fin m → ULift.{u} ℝ) × ULift.{u} ℝ)))
    (snocHomeomorph m).symm.isProperMap hS hXWd hEd (i + (1 : ℕ)) ((m + 1 : ℕ) : ℤ)
    (suspension R (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) hA
      (z₀ := (0 : ULift.{u} ℝ)) isClosed_singleton u i c)
    (euclideanClass R (m + 1))
  rw [show euclideanClass R (m + 1) = (pushforward R (ModuleCat.of R R)
      (TopCat.ofHom (snocHomeomorph m :
        C((Fin m → ULift.{u} ℝ) × ULift.{u} ℝ, Fin (m + 1) → ULift.{u} ℝ)))
      (snocHomeomorph m).isProperMap (m + 1 : ℕ)).hom
      (BorelMooreCross.congrDegree R _ (Nat.cast_add m 1).symm
        (exteriorProduct R (TopCat.of (Fin m → ULift.{u} ℝ)) (TopCat.of (ULift.{u} ℝ)) m 1
          (euclideanClass R m ⊗ₜ liftLineClass R))) from rfl,
    pushforward_pushforward_apply_of_comp_eq R _ _ (𝟙 _) _ _ (by simpa using isProperMap_id)
      (TopCat.hom_ext (ContinuousMap.ext fun x ↦ (snocHomeomorph m).symm_apply_apply x)),
    pushforward_id,
    ModuleCat.id_apply, capProductSupport_congrDegree_right] at key
  have h := congrArg (congrDegree R _
      (by push_cast; ring : ((m + 1 : ℕ) : ℤ) - (i + (1 : ℕ)) = (m : ℕ) - i)) key
  refine h.trans ?_
  rw [congrDegree_congrDegree, suspension_apply]
  exact capProductSupport_cup_pullback_exteriorProduct R _ _ hA hAd isClosed_singleton h0d hWd
    hXWd hXd τ d hd hd₀ i m 1 c u (euclideanClass R m) (liftLineClass R) hu

end borelMooreHomology

end MMP
