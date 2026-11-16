module

public import MMP.AlgebraicTopology.CapProduct.ExteriorProductNbhd
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.CapProduct.Cup
/-!
# Cap products and exterior products (Fulton §19.1; [BT] 2.2, Dold VII.12.17)

Let `B` be closed in a space `Y`, `c ∈ H^j(Y, Y - B)` with `j` even, `pr : X × Y → Y` the
projection, `a ∈ H_i X` and `b ∈ H_k Y`. Then `pr^*(c) ∩ (a × b) = a × (c ∩ b)` in
`H_{i+k-j}(X × B)`, where `X × B` is identified with `pr⁻¹ B` (`BorelMooreCap.prodPreimage`).

## Main results

* `MMP.borelMooreHomology.pushforward_prodPreimage_exteriorProduct_capProductNbhd`:
  the identity for the neighbourhood cap products, `N' = pr⁻¹ N ≅ X × N`.
* `MMP.borelMooreHomology.pushforward_prodPreimage_exteriorProduct_capProductSupport`:
  the identity `pr^*(c) ∩ (a × b) = a × (c ∩ b)` for the cap products with supports.

## Implementation notes

The cap products `c ∩ b ∈ H_*(B)` and `pr^* c ∩ (a × b) ∈ H_*(pr⁻¹ B)` are only defined
(`borelMooreHomology.capProductSupport`) when the supports `B ⊆ Y` and `pr⁻¹ B ⊆ X × Y` have
arbitrarily small proper neighbourhood deformations, so both are hypotheses of the statement; no
other hypothesis is added.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Set Simplicial AlgebraicTopology TensorProduct
  MMP.BorelMooreCross MMP.SingularCochain MMP.SingularCochain
  MMP.BorelMooreCap MMP.BorelMooreCap

universe u

namespace MMP

open MMP

namespace borelMooreHomology

open MMP.borelMooreHomology

variable (R : Type u) [CommRing R]

/-- The neighbourhood cap product in degrees `j ≤ m : ℕ`, on cocycles modulo coboundaries and
cycles modulo boundaries. -/
lemma capProductNbhd_natCast (Y : TopCat.{u}) {X N : Set Y} (hX : IsClosed X) (hN : IsClosed N)
    (hXN : X ⊆ interior N) {j m : ℕ} (hjm : j ≤ m)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (b : borelMooreHomology R (ModuleCat.of R R) Y m) :
    capProductNbhd R Y hX hN hXN j m c b =
      congrDegree R (TopCat.of N) (by omega)
        ((homologyEquiv R (TopCat.of N) (m - j)).symm
          (capHomQNbhd R hX.isOpen_compl hN (compl_union_interior_eq_univ hXN) j (m - j) m
            (by omega) (relativeSingularCohomologyEquiv R Xᶜ j c) (homologyEquiv R Y m b))) := by
  rw [capProductNbhd, dif_pos ⟨by positivity, by exact_mod_cast hjm⟩]
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, congrDegree_symm]
  have key : ∀ (j₁ m₁ : ℕ) (e1 : j = j₁) (e2 : m = m₁) (h1 : (j : ℤ) = j₁) (h2 : (m : ℤ) = m₁)
      (h3 : ((m₁ - j₁ : ℕ) : ℤ) = (m : ℤ) - j) (h4 : j₁ + (m₁ - j₁) = m₁),
      congrDegree R (TopCat.of N) h3 ((homologyEquiv R (TopCat.of N) (m₁ - j₁)).symm
        (capHomQNbhd R hX.isOpen_compl hN (compl_union_interior_eq_univ hXN) j₁ (m₁ - j₁) m₁ h4
          (relativeSingularCohomologyEquiv R Xᶜ j₁ (cohomologyWithSupports.congrIndex R Y rfl h1 c))
          (homologyEquiv R Y m₁ (congrDegree R Y h2 b)))) =
      congrDegree R (TopCat.of N) (by omega)
        ((homologyEquiv R (TopCat.of N) (m - j)).symm
          (capHomQNbhd R hX.isOpen_compl hN (compl_union_interior_eq_univ hXN) j (m - j) m
            (by omega) (relativeSingularCohomologyEquiv R Xᶜ j c) (homologyEquiv R Y m b))) := by
    rintro j₁ m₁ rfl rfl h1 h2 h3 h4
    rfl
  exact key _ _ (Int.toNat_natCast j).symm (Int.toNat_natCast m).symm _ _ _ _

/-- Under `relativeSingularCohomologyEquiv`, the pullback of cohomology with supports in `X`
along `f` is the relative cohomology map of `f`. -/
lemma relativeSingularCohomologyEquiv_pullback {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) (X : Set Y)
    (n : ℕ) (c : cohomologyWithSupports R (ModuleCat.of R R) Y X n) :
    relativeSingularCohomologyEquiv R (f ⁻¹' X)ᶜ n
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f X n).hom c) =
      relCohomologyMap R f (fun _ hx ↦ hx) n (relativeSingularCohomologyEquiv R Xᶜ n c) :=
  relativeSingularCohomologyEquiv_map _ _ _ _

/-- The exterior product in degrees `p, n : ℕ`, on cycles modulo boundaries. -/
lemma exteriorProduct_natCast (X Y : TopCat.{u}) (p n : ℕ)
    (a : borelMooreHomology R (ModuleCat.of R R) X p)
    (b : borelMooreHomology R (ModuleCat.of R R) Y n) :
    exteriorProduct R X Y p n (a ⊗ₜ b) =
      congrDegree R (TopCat.of (X × Y)) (Nat.cast_add p n).symm
        ((homologyEquiv R (TopCat.of (X × Y)) (p + n)).symm
          (crossHomQ R X Y p n (homologyEquiv R X p a) (homologyEquiv R Y n b))) := by
  rw [exteriorProduct_tmul]
  conv_lhs => rw [← (homologyEquiv R X p).symm_apply_apply a,
    ← (homologyEquiv R Y n).symm_apply_apply b]
  exact exteriorProductBilin_natCast R X Y p n _ _

/-- The exterior product commutes with transport along an equality of degrees in the second
factor. -/
lemma exteriorProduct_congrDegree_right (X Y : TopCat.{u}) (i : ℤ) {j j' : ℤ} (h : j = j')
    (a : borelMooreHomology R (ModuleCat.of R R) X i)
    (b : borelMooreHomology R (ModuleCat.of R R) Y j) :
    exteriorProduct R X Y i j' (a ⊗ₜ congrDegree R Y h b) =
      congrDegree R (TopCat.of (X × Y)) (by rw [h]) (exteriorProduct R X Y i j (a ⊗ₜ b)) := by
  subst h
  rfl

/-- The neighbourhood cap product commutes with transport along an equality of homological
degrees. -/
lemma capProductNbhd_congrDegree (Y : TopCat.{u}) {X N : Set Y} (hX : IsClosed X)
    (hN : IsClosed N) (hXN : X ⊆ interior N) (j : ℤ) {k k' : ℤ} (h : k = k')
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (b : borelMooreHomology R (ModuleCat.of R R) Y k) :
    capProductNbhd R Y hX hN hXN j k' c (congrDegree R Y h b) =
      congrDegree R (TopCat.of N) (by rw [h]) (capProductNbhd R Y hX hN hXN j k c b) := by
  subst h
  rfl

/-- Transport along `(p : ℤ) + q = ((p + q : ℕ) : ℤ)` is the identity. -/
lemma congrDegree_cast_add (X : TopCat.{u}) (p q : ℕ) (h : (p : ℤ) + q = ((p + q : ℕ) : ℤ))
    (v : borelMooreHomology R (ModuleCat.of R R) X ((p : ℤ) + q)) :
    congrDegree R X h v = v :=
  rfl

/-- Transport along `((p + q : ℕ) : ℤ) = (p : ℤ) + q` is the identity. -/
lemma congrDegree_cast_add' (X : TopCat.{u}) (p q : ℕ) (h : ((p + q : ℕ) : ℤ) = (p : ℤ) + q)
    (v : borelMooreHomology R (ModuleCat.of R R) X ((p + q : ℕ) : ℤ)) :
    congrDegree R X h v = v :=
  rfl

/-- The neighbourhood cap product in degrees `j, k` vanishes unless `0 ≤ j ≤ k`. -/
lemma capProductNbhd_of_not_le (Y : TopCat.{u}) {X N : Set Y} (hX : IsClosed X)
    (hN : IsClosed N) (hXN : X ⊆ interior N) {j k : ℤ} (h : ¬ (0 ≤ j ∧ j ≤ k)) :
    capProductNbhd R Y hX hN hXN j k = 0 := by
  rw [capProductNbhd, dif_neg h]

/-- The exterior product `a × b` vanishes when either degree is negative. -/
lemma exteriorProduct_tmul_of_neg (X Y : TopCat.{u}) {i j : ℤ} (h : i < 0 ∨ j < 0)
    (a : borelMooreHomology R (ModuleCat.of R R) X i)
    (b : borelMooreHomology R (ModuleCat.of R R) Y j) :
    exteriorProduct R X Y i j (a ⊗ₜ b) = 0 := by
  rw [exteriorProduct_tmul, exteriorProductBilin_of_neg R X Y h, LinearMap.zero_apply,
    LinearMap.zero_apply]

/-- The main case of `pushforward_prodPreimage_exteriorProduct_capProductNbhd`: degrees
`p, n, j : ℕ` with `j ≤ n`. -/
lemma pushforward_prodPreimage_exteriorProduct_capProductNbhd_natCast (X Y : TopCat.{u})
    {B N : Set Y} (hB : IsClosed B) (hN : IsClosed N) (hBN : B ⊆ interior N) (p n j' : ℕ)
    (hjn : j' ≤ n) (hj' : Even j')
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y B j')
    (a : borelMooreHomology R (ModuleCat.of R R) X p)
    (b : borelMooreHomology R (ModuleCat.of R R) Y n) :
    (pushforward R (ModuleCat.of R R) (prodPreimage X N) (isProperMap_prodPreimage hN)
        (p + (n - j'))).hom
        (exteriorProduct R X (TopCat.of N) p (n - j')
          (a ⊗ₜ capProductNbhd R Y hB hN hBN j' n c b)) =
      congrDegree R (TopCat.of (prPre X N)) (by ring)
        (capProductNbhd R (TopCat.of (X × Y)) (isClosed_prPre hB) (isClosed_prPre hN)
          (preimage_subset_interior_preimage (prSnd X Y) hBN) j' (p + n)
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd X Y) B j').hom c)
          (exteriorProduct R X Y p n (a ⊗ₜ b))) := by
  rw [capProductNbhd_natCast R Y hB hN hBN hjn c b,
    exteriorProduct_congrDegree_right R X (TopCat.of N) (p : ℤ) _ a]
  erw [exteriorProduct_natCast R X (TopCat.of N) p (n - j')]
  rw [LinearEquiv.apply_symm_apply, pushforward_eq_homologyMap, homologyMap_congrDegree]
  simp only [congrDegree_cast_add, congrDegree_cast_add']
  have hT1 := homologyMap_crossHomQ_capHomQNbhd (A := Bᶜ) (X := X) hB.isOpen_compl hN
    (compl_union_interior_eq_univ hBN) p j' (n - j') n (p + n - j') (by omega) (by omega)
    (isClosed_prPre (X := X) hB).isOpen_compl
    (compl_union_interior_eq_univ (preimage_subset_interior_preimage (prSnd X Y) hBN))
    Set.preimage_compl.superset rfl (relativeSingularCohomologyEquiv R Bᶜ j' c)
    (homologyEquiv R X p a) (homologyEquiv R Y n b)
  rw [hT1, exteriorProduct_natCast R X Y p n,
    capProductNbhd_congrDegree]
  erw [capProductNbhd_natCast R _ _ _ _ (show j' ≤ p + n by omega)]
  rw [LinearEquiv.apply_symm_apply, relativeSingularCohomologyEquiv_pullback]
  simp only [congrDegree_congrDegree]

/-- **Cap products and exterior products, near a closed set.** For `B` closed in `Y`, a closed
neighbourhood `N` of `B`, `c ∈ H^j(Y, Y - B)` with `j` even, `a ∈ H_i X` and `b ∈ H_k Y`: through
`X × N ≅ pr⁻¹ N`, `a × (c ∩_N b) = pr^* c ∩_{pr⁻¹ N} (a × b)`. -/
theorem pushforward_prodPreimage_exteriorProduct_capProductNbhd (X Y : TopCat.{u}) {B N : Set Y}
    (hB : IsClosed B) (hN : IsClosed N) (hBN : B ⊆ interior N) (i j k : ℤ) (hj : Even j)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y B j)
    (a : borelMooreHomology R (ModuleCat.of R R) X i)
    (b : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (prodPreimage X N) (isProperMap_prodPreimage hN)
        (i + (k - j))).hom
        (exteriorProduct R X (TopCat.of N) i (k - j) (a ⊗ₜ capProductNbhd R Y hB hN hBN j k c b)) =
      congrDegree R (TopCat.of (prPre X N)) (by ring)
        (capProductNbhd R (TopCat.of (X × Y)) (isClosed_prPre hB) (isClosed_prPre hN)
          (preimage_subset_interior_preimage (prSnd X Y) hBN) j (i + k)
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd X Y) B j).hom c)
          (exteriorProduct R X Y i k (a ⊗ₜ b))) := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [exteriorProduct_tmul_of_neg R _ _ (Or.inl hi),
      exteriorProduct_tmul_of_neg R _ _ (Or.inl hi),
      map_zero, map_zero, map_zero]
  rcases lt_or_ge k 0 with hk | hk
  · rw [exteriorProduct_tmul_of_neg R _ _ (Or.inr hk),
      capProductNbhd_of_not_le R _ _ _ _ (by omega), LinearMap.zero_apply, LinearMap.zero_apply,
      TensorProduct.tmul_zero, map_zero, map_zero, map_zero, map_zero]
  rcases lt_or_ge j 0 with hj0 | hj0
  · rw [capProductNbhd_of_not_le R _ _ _ _ (by omega),
      capProductNbhd_of_not_le R _ _ _ _ (by omega),
      LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply,
      TensorProduct.tmul_zero, map_zero, map_zero, map_zero]
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  obtain ⟨j', rfl⟩ := Int.eq_ofNat_of_zero_le hj0
  have hj' : Even j' := by exact_mod_cast hj
  rcases lt_or_ge n j' with hnj | hjn
  · rw [capProductNbhd_of_not_le R _ _ _ _ (by omega), LinearMap.zero_apply, LinearMap.zero_apply,
      TensorProduct.tmul_zero, map_zero, map_zero]
    rw [exteriorProduct_natCast R X Y p n, capProductNbhd_congrDegree]
    rcases lt_or_ge (p + n) j' with hpn | hpn
    · rw [capProductNbhd_of_not_le R _ _ _ _ (by omega), LinearMap.zero_apply, LinearMap.zero_apply,
        map_zero, map_zero]
    erw [capProductNbhd_natCast R _ _ _ _ hpn]
    rw [LinearEquiv.apply_symm_apply,
      relativeSingularCohomologyEquiv_pullback]
    have e : (prPre X B)ᶜ = prPre X Bᶜ := rfl
    have hz := capHomQNbhd_relCohomologyMap_crossHomQ_eq_zero_of_lt (A := Bᶜ) (X := X) hB.isOpen_compl hN
      (compl_union_interior_eq_univ hBN) p j' n (p + n - j') (by omega)
      (isClosed_prPre (X := X) hB).isOpen_compl
      (compl_union_interior_eq_univ (preimage_subset_interior_preimage (prSnd X Y) hBN))
      Set.preimage_compl.superset e hnj (relativeSingularCohomologyEquiv R Bᶜ j' c)
      (homologyEquiv R X p a) (homologyEquiv R Y n b)
    simp only [hz, map_zero]
  exact pushforward_prodPreimage_exteriorProduct_capProductNbhd_natCast R X Y hB hN hBN p n j'
    hjn hj' c a b

/-- The homeomorphism `X × S ≃ₜ pr⁻¹ S`. -/
def prodPreimageHomeomorph (X : TopCat.{u}) {Y : TopCat.{u}} (S : Set Y) :
    (X × S) ≃ₜ prPre X S where
  toFun := prodPreimage X S
  invFun x := (x.1.1, ⟨x.1.2, x.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (prodPreimage X S).hom.continuous
  continuous_invFun := by fun_prop

/-- Pushforwards along equal proper maps are equal. -/
lemma pushforward_congr_hom {X' Y' : TopCat.{u}} {f g : X' ⟶ Y'} (h : f = g) (hf : IsProperMap f)
    (hg : IsProperMap g) (i : ℤ) :
    pushforward R (ModuleCat.of R R) f hf i = pushforward R (ModuleCat.of R R) g hg i := by
  subst h
  rfl

/-- **Cap products and exterior products** (Fulton §19.1; [BT] 2.2; Dold VII.12.17). Let `B` be
closed in a space `Y`, `c ∈ H^j(Y, Y - B)` with `j` even, `pr : X × Y → Y` the projection,
`a ∈ H_i X` and `b ∈ H_k Y`. Then `pr^*(c) ∩ (a × b) = a × (c ∩ b)` in `H_{i+k-j}(X × B)`,
through the identification `X × B ≅ pr⁻¹ B` (`BorelMooreCap.prodPreimage`, a homeomorphism).
The cap products into `H_* B` and `H_*(pr⁻¹ B)` are `capProductSupport`, for `B` and `pr⁻¹ B`
having arbitrarily small proper neighbourhood deformations. -/
theorem pushforward_prodPreimage_exteriorProduct_capProductSupport (X Y : TopCat.{u})
    {B : Set Y} (hB : IsClosed B) (hBd : HasProperNeighbourhoodDeformations B)
    (hXBd : HasProperNeighbourhoodDeformations (prSnd X Y ⁻¹' B)) (i j k : ℤ) (hj : Even j)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y B j)
    (a : borelMooreHomology R (ModuleCat.of R R) X i)
    (b : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (prodPreimage X B) (isProperMap_prodPreimage hB)
        (i + (k - j))).hom
        (exteriorProduct R X (TopCat.of B) i (k - j) (a ⊗ₜ capProductSupport R Y hB hBd j k c b)) =
      congrDegree R (TopCat.of (prSnd X Y ⁻¹' B)) (by ring)
        (capProductSupportPullback R (prSnd X Y) hB hXBd j (i + k) c
          (exteriorProduct R X Y i k (a ⊗ₜ b))) := by
  obtain ⟨N, hN, hBN, r, hr, hrB⟩ := hBd.exists_retraction
  let r' : C(prPre X N, prPre X B) :=
    ⟨(prodPreimageHomeomorph X B) ∘ Prod.map id r ∘ (prodPreimageHomeomorph X N).symm,
      (prodPreimageHomeomorph X B).continuous.comp ((continuous_id.prodMap r.continuous).comp
        (prodPreimageHomeomorph X N).symm.continuous)⟩
  have hr' : IsProperMap r' :=
    (prodPreimageHomeomorph X B).isProperMap.comp
      ((isProperMap_id.prodMap hr).comp (prodPreimageHomeomorph X N).symm.isProperMap)
  have hr'B : ∀ y : prPre X N,
      (y : TopCat.of (X × Y)) ∈ prPre X B → (r' y : TopCat.of (X × Y)) = y :=
    fun y hy ↦ Prod.ext rfl (hrB ⟨y.1.2, y.2⟩ hy)
  rw [capProductSupport_eq_capProductAlong R Y hB hBd hN hBN r hr hrB,
    capProductSupportPullback_apply,
    capProductSupport_eq_capProductAlong R _ (hB.preimage (prSnd X Y).hom.continuous) hXBd
      (isClosed_prPre hN) (preimage_subset_interior_preimage (prSnd X Y) hBN) r' hr' hr'B]
  simp only [capProductAlong, LinearMap.compr₂_apply]
  have h1 := pushforward_exteriorProduct R (𝟙 X) (TopCat.ofHom r) (by simpa using isProperMap_id)
    hr i (k - j) a (capProductNbhd R Y hB hN hBN j k c b)
  rw [pushforward_id, ModuleCat.id_apply] at h1
  rw [← h1, ← ModuleCat.comp_apply, ← pushforward_comp,
    pushforward_congr_hom R (show SingularCross.prodHom (𝟙 X) (TopCat.ofHom r) ≫ prodPreimage X B =
      prodPreimage X N ≫ TopCat.ofHom r' from rfl) _
      (hr'.comp (isProperMap_prodPreimage hN)),
    pushforward_comp R _ (prodPreimage X N) (TopCat.ofHom r') (isProperMap_prodPreimage hN) hr',
    ModuleCat.comp_apply,
    pushforward_prodPreimage_exteriorProduct_capProductNbhd R X Y hB hN hBN i j k hj c a b,
    pushforward_eq_homologyMap, homologyMap_congrDegree]
  rfl

end borelMooreHomology

end MMP
