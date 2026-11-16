module

public import MMP.AlgebraicTopology.CapProduct.ExteriorProduct
public import MMP.AlgebraicTopology.CapProduct.CupSupport
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.PoincareDuality.DualClassSupport
public import MMP.AlgebraicTopology.SingularCohomology.EvenRing
public import MMP.AlgebraicGeometry.CycleMap.RefinedIntersection
public import MMP.AlgebraicTopology.OrientationClass.CapDeformation

/-!
# The diagonal swap and iterated cap products (Fulton, §19.1 and §19.2)

For a space `Y`, the cap product `capProduct` with absolute target `H_{k-j} Y` and the cap
product with supports `capProductSupport` with target `H_{k-j} X` are related by the
projection formula, the formula for the cap product with a cup product, and the graded
commutativity of the cup product. This file records the consequences used for the cycle map
as a ring homomorphism (Fulton, Corollary 19.2).

* For a proper `f : Y' → Y`, `f_* (f^* c ∩ a) = c ∩ f_* a` in `H_{k-j} Y`.
* `u ∩ (v ∩ a) = (u ∪ v) ∩ a`, and for even-degree absolute classes
  `d ∩ (c ∩ a) = (c ∪ d) ∩ a`.
* For closed `D`, `S ⊆ Y`, `u ∈ H^n(Y, Y - D)`, `e ∈ H^j(Y, Y - S)` with `(-1)^{nj} = 1`:
  `u ∩ (e ∩ z) = j_D^* e ∩ (u ∩ z)` in `H_{K-n-j} D`.
* For `c ∈ H^j Y` of even degree: `a × (c ∩ b) = pr₂^* c ∩ (a × b)`.
* **The diagonal swap.** Let `φ : M × M ≅ P` be a homeomorphism, `q : P → M` with
  `q ∘ φ = pr₂`, `D ⊆ P` closed, `u ∈ H^n(P, P - D)`, `μ ∈ H_n M`, `h : M → D` proper with
  `q ∘ h = id`, and suppose `h_* a = u ∩ φ_*(a × μ)`. Then for `d ∈ H^j M` of even degree,
  `h_*(d ∩ a) = u ∩ φ_*(a × (d ∩ μ))`. Indeed `φ_*(a × (d ∩ μ)) = q^* d ∩ φ_*(a × μ)`, so
  `u ∩ φ_*(a × (d ∩ μ)) = j_D^* q^* d ∩ (u ∩ φ_*(a × μ)) = j_D^* q^* d ∩ h_* a = h_*(d ∩ a)`
  by the projection formula along `h`, since `q ∘ j_D ∘ h = id`.

## Main results

* `MMP.borelMooreHomology.capProduct_capProduct_eq_capProduct_cup`
* `MMP.borelMooreHomology.capProduct_capProduct_eq_capProduct_cupUniv`
* `MMP.borelMooreHomology.capProductSupport_capProduct_eq`
* `MMP.borelMooreHomology.exteriorProduct_capProduct_univ`
* `MMP.borelMooreHomology.pushforward_capProduct_eq_capProductSupportPullback_exteriorProduct`

## Implementation notes

The class `q^* d` has support `q⁻¹ M`, which is all of `P`; the supports `f⁻¹ X` produced by
pullbacks are kept as they are, and the arbitrarily small proper neighbourhood deformations of
such sets come from `hasProperNeighbourhoodDeformations_univ`. The diagonal swap holds for any
map `g : P → P` (the class `g^* u` with support `g⁻¹ D`); it is used with `g = 1`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and the proof of Proposition 19.2.
-/

@[expose] public noncomputable section

open CategoryTheory Set TensorProduct

universe u

namespace MMP

open MMP

namespace borelMooreHomology

open MMP.borelMooreHomology

open BorelMooreCap BorelMooreCross

variable (R : Type u) [CommRing R]

/-- The cap product with a pulled-back class depends only on the map. -/
lemma capProduct_pullback_congr {Y' Y : TopCat.{u}} {f f' : Y' ⟶ Y} (hff : f = f') (X : Set Y)
    (j k : ℤ) (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    capProduct R Y' (f ⁻¹' X) j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f X j).hom c) a =
      capProduct R Y' (f' ⁻¹' X) j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f' X j).hom c) a := by
  subst hff
  rfl

/-- The cap product with `g^* f^* c` is the cap product with `(f ∘ g)^* c`. -/
lemma capProduct_pullback_pullback {Y'' Y' Y : TopCat.{u}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y)
    (X : Set Y) (j k : ℤ) (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y'' k) :
    capProduct R Y'' (g ⁻¹' (f ⁻¹' X)) j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g (f ⁻¹' X) j).hom
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f X j).hom c)) a =
      capProduct R Y'' ((g ≫ f) ⁻¹' X) j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (g ≫ f) X j).hom c) a := by
  rw [cohomologyWithSupports.pullback_comp]
  rfl

/-- The cap product with `𝟙^* c` is the cap product with `c`. -/
lemma capProduct_pullback_id (Y : TopCat.{u}) (X : Set Y) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    capProduct R Y ((𝟙 Y : Y ⟶ Y) ⁻¹' X) j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (𝟙 Y) X j).hom c) a =
      capProduct R Y X j k c a := by
  rw [cohomologyWithSupports.pullback_id]
  rfl

/-- The cap product commutes with transport along an equality of homological degrees. -/
lemma capProduct_congrDegree (Y : TopCat.{u}) (X : Set Y) (j : ℤ) {k k' : ℤ} (h : k = k')
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    capProduct R Y X j k' c (congrDegree R Y h a) =
      congrDegree R Y (by rw [h]) (capProduct R Y X j k c a) := by
  subst h
  rfl

/-- **The cap product with a cup product**, absolute target: for closed `X`, `W` in `Y`,
`u ∈ H^i(Y, Y - X)`, `v ∈ H^j(Y, Y - W)` and `a ∈ H_k Y`, `u ∩ (v ∩ a) = (u ∪ v) ∩ a` in
`H_{k-i-j} Y`. -/
theorem capProduct_capProduct_eq_capProduct_cup (Y : TopCat.{u}) {X W : Set Y}
    (hX : IsClosed X) (hW : IsClosed W) (hXd : HasProperNeighbourhoodDeformations X)
    (hWd : HasProperNeighbourhoodDeformations W)
    (hXWd : HasProperNeighbourhoodDeformations (X ∩ W))
    (hXd' : HasProperNeighbourhoodDeformations (subsetInclusion W ⁻¹' X)) (i j k : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (v : cohomologyWithSupports R (ModuleCat.of R R) Y W j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    capProduct R Y X i (k - j) u (capProduct R Y W j k v a) =
      congrDegree R Y (by ring)
        (capProduct R Y (X ∩ W) (i + j) k (cohomologyWithSupports.cup R Y hX hW i j u v) a) := by
  have h1 := capProductSupport_cup R Y hX hW hWd hXWd hXd' i j k u v a
  have h2 := congrArg (pushforward R (ModuleCat.of R R) (subsetInclusion (X ∩ W))
    (isProperMap_subsetInclusion (hX.inter hW)) (k - j - i)).hom h1
  rw [pushforward_congrDegree, pushforward_subsetInclusion_capProductSupport,
    ← pushforward_comp_apply'] at h2
  rw [← pushforward_subsetInclusion_capProductSupport R Y hW hWd j k v a,
    ← pushforward_subsetInclusion_capProductSupport R Y hX hXd,
    ← pushforward_restrictPreimage_capProductSupportPullback R (subsetInclusion W)
      (isProperMap_subsetInclusion hW) hX hXd hXd', h2]
  refine (pushforward_comp_apply' R (TopCat.ofHom ((subsetInclusion W).hom.restrictPreimage X))
    (subsetInclusion X) ((isProperMap_subsetInclusion hW).restrictPreimage X)
    (isProperMap_subsetInclusion hX) _ _).symm.trans ?_
  exact congrFun (congrArg (fun φ ↦ ⇑(ModuleCat.Hom.hom φ))
    (pushforward_congr (R := R) rfl _ _ _)) _

/-- **Cap product with supports against an absolute-target cap product.** For closed `D`, `S`
in `Y`, `u ∈ H^n(Y, Y - D)`, `e ∈ H^j(Y, Y - S)` with `(-1)^{nj} = 1` and `z ∈ H_K Y`,
`u ∩ (e ∩ z) = j_D^* e ∩ (u ∩ z)` in `H_{K-n-j} D`, the right side pushed forward from
`j_D⁻¹ S` to `D`. -/
theorem capProductSupport_capProduct_eq (Y : TopCat.{u}) {D S : Set Y} (hD : IsClosed D)
    (hS : IsClosed S) (hDd : HasProperNeighbourhoodDeformations D)
    (hSd : HasProperNeighbourhoodDeformations S)
    (hDSd : HasProperNeighbourhoodDeformations (D ∩ S))
    (hSDd : HasProperNeighbourhoodDeformations (S ∩ D))
    (hSD' : HasProperNeighbourhoodDeformations (subsetInclusion S ⁻¹' D))
    (hDS' : HasProperNeighbourhoodDeformations (subsetInclusion D ⁻¹' S)) {n j : ℤ} (K : ℤ)
    (hs : (-1 : Rˣ) ^ (n * j) = 1)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y D n)
    (e : cohomologyWithSupports R (ModuleCat.of R R) Y S j)
    (z : borelMooreHomology R (ModuleCat.of R R) Y K) :
    capProductSupport R Y hD hDd n (K - j) u (capProduct R Y S j K e z) =
      congrDegree R (TopCat.of D) (by ring)
        (capProduct R (TopCat.of D) (subsetInclusion D ⁻¹' S) j (K - n)
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (subsetInclusion D) S j).hom e)
          (capProductSupport R Y hD hDd n K u z)) := by
  have h1 := capProductSupport_cup R Y hD hS hSd hDSd hSD' n j K u e z
  have h2 := capProductSupport_cup_eq_pushforward_swap R Y hD hS hDd hDSd hSDd hDS' K hs u e z
  set x := capProductSupportPullback R (subsetInclusion S) hD hSD' n (K - j) u
    (capProductSupport R Y hS hSd j K e z)
  set y := capProductSupportPullback R (subsetInclusion D) hS hDS' j (K - n) e
    (capProductSupport R Y hD hDd n K u z)
  have hA : (pushforward R (ModuleCat.of R R)
        (preimageInterHom S D ≫ subsetInclusionOfSubset (inter_comm S D).le)
        ((isProperMap_subsetInclusionOfSubset (hS.inter hD) (inter_comm S D).le).comp
          (isProperMap_preimageInterHom hS hD)) (K - j - n)).hom x =
      congrDegree R (TopCat.of (D ∩ S : Set Y)) (by ring)
        ((pushforward R (ModuleCat.of R R) (preimageInterHom D S)
          (isProperMap_preimageInterHom hD hS) (K - n - j)).hom y) := by
    rw [← h1, ← h2, congrDegree_congrDegree]
  have hi := isProperMap_subsetInclusionOfSubset (hD.inter hS) (inter_subset_left (s := D) (t := S))
  rw [← pushforward_subsetInclusion_capProductSupport R Y hS hSd j K e z,
    ← pushforward_restrictPreimage_capProductSupportPullback R (subsetInclusion S)
      (isProperMap_subsetInclusion hS) hD hDd hSD']
  calc _ = (pushforward R (ModuleCat.of R R) (subsetInclusionOfSubset inter_subset_left) hi
          (K - j - n)).hom ((pushforward R (ModuleCat.of R R)
            (preimageInterHom S D ≫ subsetInclusionOfSubset (inter_comm S D).le)
            ((isProperMap_subsetInclusionOfSubset (hS.inter hD) (inter_comm S D).le).comp
              (isProperMap_preimageInterHom hS hD)) (K - j - n)).hom x) := by
        rw [← pushforward_comp_apply']
        exact congrFun (congrArg (fun φ ↦ ⇑(ModuleCat.Hom.hom φ))
          (pushforward_congr (R := R) rfl _ _ _)) _
    _ = congrDegree R (TopCat.of D) (by ring)
          ((pushforward R (ModuleCat.of R R) (preimageInterHom D S ≫
            subsetInclusionOfSubset inter_subset_left)
            (hi.comp (isProperMap_preimageInterHom hD hS)) (K - n - j)).hom y) := by
        rw [hA, pushforward_congrDegree, pushforward_comp_apply']
    _ = _ := by
        rw [← pushforward_subsetInclusion_capProductSupport R (TopCat.of D)
          (hS.preimage (subsetInclusion D).hom.continuous) hDS',
          ← capProductSupportPullback_apply R (subsetInclusion D) hS hDS']
        exact congrArg (congrDegree R (TopCat.of D) _) <| congrFun (congrArg (fun φ ↦ ⇑(ModuleCat.Hom.hom φ))
          (pushforward_congr (R := R) rfl _ _ _)) _

/-- The cap product commutes with transport of the cohomology class along equalities of the
support and the degree. -/
lemma capProduct_congrIndex (Y : TopCat.{u}) {S S' : Set Y} (hS : Sᶜ = S'ᶜ) {m m' : ℤ}
    (hm : m = m') (k : ℤ) (x : cohomologyWithSupports R (ModuleCat.of R R) Y S m)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    capProduct R Y S' m' k (cohomologyWithSupports.congrIndex R Y hS hm x) a =
      congrDegree R Y (by rw [hm]) (capProduct R Y S m k x a) := by
  obtain rfl : S = S' := compl_injective hS
  subst hm
  rfl

/-- `d ∩ (c ∩ a) = (c ∪ d) ∩ a` for even-degree absolute classes. -/
theorem capProduct_capProduct_eq_capProduct_cupUniv (M : TopCat.{u}) (p q : ℕ) (k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) M Set.univ (2 * p : ℕ))
    (d : cohomologyWithSupports R (ModuleCat.of R R) M Set.univ (2 * q : ℕ))
    (a : borelMooreHomology R (ModuleCat.of R R) M k) :
    capProduct R M Set.univ (2 * q : ℕ) (k - (2 * p : ℕ)) d
        (capProduct R M Set.univ (2 * p : ℕ) k c a) =
      congrDegree R _ (by push_cast; ring)
        (capProduct R M Set.univ (2 * (p + q) : ℕ) k (cupUniv R M p q c d) a) := by
  have hU := hasProperNeighbourhoodDeformations_univ M
  have hUU : HasProperNeighbourhoodDeformations (univ ∩ univ : Set M) := by
    rw [inter_self]; exact hU
  have hU' : HasProperNeighbourhoodDeformations
      (subsetInclusion (univ : Set M) ⁻¹' (univ : Set M)) := by
    rw [preimage_univ]; exact hasProperNeighbourhoodDeformations_univ _
  have hc := cohomologyWithSupports.cup_comm R M isClosed_univ isClosed_univ
    (2 * p : ℕ) (2 * q : ℕ) c d
  have hs : (-1 : Rˣ) ^ (((2 * p : ℕ) : ℤ) * ((2 * q : ℕ) : ℤ)) = 1 :=
    Even.neg_one_zpow ⟨(2 * p * q : ℕ), by push_cast; ring⟩
  rw [hs, Units.val_one, one_smul] at hc
  rw [capProduct_capProduct_eq_capProduct_cup R M isClosed_univ isClosed_univ hU hU hUU hU',
    cupUniv, LinearMap.compr₂_apply, LinearEquiv.coe_coe, capProduct_congrIndex, ← hc,
    capProduct_congrIndex, congrDegree_congrDegree, congrDegree_congrDegree]

/-- **The exterior product with an absolute cap product.** For `c ∈ H^j Y` of even degree,
`a ∈ H_i X` and `b ∈ H_k Y`, `a × (c ∩ b) = pr₂^* c ∩ (a × b)` in `H_{i+k-j}(X × Y)`. -/
theorem exteriorProduct_capProduct_univ (X Y : TopCat.{u}) (i j k : ℤ) (hj : Even j)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ j)
    (a : borelMooreHomology R (ModuleCat.of R R) X i)
    (b : borelMooreHomology R (ModuleCat.of R R) Y k) :
    exteriorProduct R X Y i (k - j) (a ⊗ₜ capProduct R Y Set.univ j k c b) =
      congrDegree R (TopCat.of (X × Y)) (by ring)
        (capProduct R (TopCat.of (X × Y)) (prSnd X Y ⁻¹' Set.univ) j (i + k)
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd X Y) Set.univ j).hom c)
          (exteriorProduct R X Y i k (a ⊗ₜ b))) := by
  have hU := hasProperNeighbourhoodDeformations_univ Y
  have hXU : HasProperNeighbourhoodDeformations (prSnd X Y ⁻¹' (univ : Set Y)) := by
    rw [preimage_univ]; exact hasProperNeighbourhoodDeformations_univ _
  have key := pushforward_prodPreimage_exteriorProduct_capProductSupport R X Y isClosed_univ hU
    hXU i j k hj c a b
  have key2 := congrArg (pushforward R (ModuleCat.of R R) (subsetInclusion (prPre X (univ : Set Y)))
    (isProperMap_subsetInclusion (isClosed_prPre isClosed_univ)) (i + (k - j))).hom key
  rw [← pushforward_comp_apply', pushforward_congrDegree, capProductSupportPullback_apply,
    pushforward_subsetInclusion_capProductSupport] at key2
  rw [← key2, ← pushforward_subsetInclusion_capProductSupport R Y isClosed_univ hU j k c b]
  have hid : IsProperMap (𝟙 X : X ⟶ X) := by simpa using isProperMap_id
  have e := pushforward_exteriorProduct R (𝟙 X) (subsetInclusion (univ : Set Y)) hid
    (isProperMap_subsetInclusion isClosed_univ) i (k - j) a
    (capProductSupport R Y isClosed_univ hU j k c b)
  rw [pushforward_id] at e
  refine (e.symm.trans ?_)
  exact congrFun (congrArg (fun φ ↦ ⇑(ModuleCat.Hom.hom φ))
    (pushforward_congr (R := R) rfl _ _ _)) _

/-- **The diagonal swap** (Fulton, proof of Proposition 19.2 / Corollary 19.2). Let
`φ : M × M ≅ P`, `q : P → M` with `q ∘ φ = pr₂`, `u ∈ H^n(P, P - D)`, `μ ∈ H_n M` and
`h : M → g⁻¹ D` proper with `q ∘ h = id`, such that `h_* a = g^* u ∩ φ_*(a × μ)`. Then for
`d ∈ H^j M` of even degree, `h_*(d ∩ a) = g^* u ∩ φ_*(a × (d ∩ μ))`. -/
theorem pushforward_capProduct_eq_capProductSupportPullback_exteriorProduct
    {M P : TopCat.{u}} (φ : M × M ≃ₜ P) (q : P ⟶ M) (hq : ∀ x y : M, q (φ (x, y)) = y)
    (g : P ⟶ P) {D : Set P} (hD : IsClosed D)
    (hDd : HasProperNeighbourhoodDeformations (g ⁻¹' D))
    (h : M ⟶ TopCat.of (g ⁻¹' D)) (hh : IsProperMap h) (hqh : ∀ x : M, q (h x).1 = x)
    {n : ℤ} (u : cohomologyWithSupports R (ModuleCat.of R R) P D n)
    (μ : borelMooreHomology R (ModuleCat.of R R) M n)
    {j : ℤ} (hj : Even j) (d : cohomologyWithSupports R (ModuleCat.of R R) M Set.univ j)
    (k : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) M k)
    (hunit : (pushforward R (ModuleCat.of R R) h hh k).hom a =
        congrDegree R _ (by ring)
          (capProductSupportPullback R g hD hDd n (k + n) u
            ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(M × M, P)))
              φ.isProperMap (k + n)).hom (exteriorProduct R M M k n (a ⊗ₜ μ))))) :
    (pushforward R (ModuleCat.of R R) h hh (k - j)).hom (capProduct R M Set.univ j k d a) =
      congrDegree R _ (by ring)
        (capProductSupportPullback R g hD hDd n (k + (n - j)) u
          ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(M × M, P)))
            φ.isProperMap (k + (n - j))).hom
            (exteriorProduct R M M k (n - j) (a ⊗ₜ capProduct R M Set.univ j n d μ)))) := by
  have hall : ∀ {Z : Type u} [TopologicalSpace Z] (X : Set Z), (∀ y, y ∈ X) →
      HasProperNeighbourhoodDeformations X := fun X hX ↦ by
    rw [eq_univ_of_forall hX]; exact hasProperNeighbourhoodDeformations_univ _
  have hD' : IsClosed (g ⁻¹' D) := hD.preimage g.hom.continuous
  have hS : IsClosed (q ⁻¹' (univ : Set M)) := isClosed_univ.preimage q.hom.continuous
  have hSall : ∀ y, y ∈ q ⁻¹' (univ : Set M) := fun _ ↦ trivial
  have hSd : HasProperNeighbourhoodDeformations (q ⁻¹' (univ : Set M)) := by
    rw [eq_univ_of_forall hSall]; exact hasProperNeighbourhoodDeformations_univ _
  have hDSd : HasProperNeighbourhoodDeformations (g ⁻¹' D ∩ q ⁻¹' (univ : Set M)) := by
    rw [inter_eq_left.2 fun x _ ↦ hSall x]; exact hDd
  have hSDd : HasProperNeighbourhoodDeformations (q ⁻¹' (univ : Set M) ∩ g ⁻¹' D) := by
    rw [inter_eq_right.2 fun x _ ↦ hSall x]; exact hDd
  have hSD' : HasProperNeighbourhoodDeformations
      (subsetInclusion (q ⁻¹' (univ : Set M)) ⁻¹' (g ⁻¹' D)) :=
    hDd.preimage_homeomorph
      ((Homeomorph.setCongr (eq_univ_of_forall hSall)).trans (Homeomorph.Set.univ P))
  have hDS' : HasProperNeighbourhoodDeformations
      (subsetInclusion (g ⁻¹' D) ⁻¹' (q ⁻¹' (univ : Set M))) :=
    hall _ fun _ ↦ trivial
  have hDS'c : IsClosed (subsetInclusion (g ⁻¹' D) ⁻¹' (q ⁻¹' (univ : Set M))) :=
    hS.preimage (subsetInclusion _).hom.continuous
  have hφS : HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (φ : C(M × M, P))) ⁻¹' (q ⁻¹' (univ : Set M))) :=
    hall _ fun _ ↦ trivial
  have hhS : HasProperNeighbourhoodDeformations
      (h ⁻¹' (subsetInclusion (g ⁻¹' D) ⁻¹' (q ⁻¹' (univ : Set M)))) :=
    hall _ fun _ ↦ trivial
  have hs : (-1 : Rˣ) ^ (n * j) = 1 := (hj.mul_left n).neg_one_zpow
  have hφq : TopCat.ofHom (φ : C(M × M, P)) ≫ q = prSnd M M := by
    ext ⟨x, y⟩; exact hq x y
  have hhq : (h ≫ subsetInclusion (g ⁻¹' D)) ≫ q = 𝟙 M := by
    ext x; exact hqh x
  have hunit' := (congrDegree_eq_iff_eq_congrDegree_symm R _ _ _ _).1 hunit.symm
  rw [exteriorProduct_capProduct_univ R M M k j n hj d a μ, pushforward_congrDegree,
    capProductSupportPullback_congrDegree_apply, ← capProduct_pullback_congr R hφq,
    ← capProduct_pullback_pullback, pushforward_capProduct_pullback R _ φ.isProperMap hS hSd hφS,
    capProductSupportPullback_apply,
    capProductSupport_capProduct_eq R P hD' hS hDd hSd hDSd hSDd hSD' hDS' (k + n) hs,
    ← capProductSupportPullback_apply R g hD, hunit', capProduct_congrDegree,
    ← pushforward_capProduct_pullback R h hh hDS'c hDS' hhS, capProduct_pullback_pullback,
    capProduct_pullback_pullback, capProduct_pullback_congr R hhq, capProduct_pullback_id]
  simp only [pushforward_congrDegree, congrDegree_congrDegree]
  rfl

end borelMooreHomology

end MMP
