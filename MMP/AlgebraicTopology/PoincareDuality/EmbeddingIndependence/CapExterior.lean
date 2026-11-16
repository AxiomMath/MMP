module

public import MMP.AlgebraicTopology.CapProduct.ExteriorProduct

/-!
# Cap products with classes pulled back from the second factor, in every degree

`pr^*(c) ∩ (a × b) = a × (c ∩ b)` for `pr : X × Y → Y`, `c ∈ H^j(Y, Y - B)` of ANY degree `j`.
This is `pushforward_prodPreimage_exteriorProduct_capProductSupport`
(`CapProduct/ExteriorProduct.lean`, `lem_ext_c19_cap_exterior_product`) without its hypothesis
`Even j`: with Fulton's back-face cap convention the chain-level
identity `homologyMap_crossHomQ_capHomQNbhd` carries no sign, and the proof there never uses
`Even j`. The proofs below are that file's, with the hypothesis removed.
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

/-- The main case of `pushforward_prodPreimage_exteriorProduct_capProductNbhd`: degrees
`p, n, j : ℕ` with `j ≤ n`. -/
lemma exteriorProduct_capProductNbhd_pullback_prSnd_natCast (X Y : TopCat.{u})
    {B N : Set Y} (hB : IsClosed B) (hN : IsClosed N) (hBN : B ⊆ interior N) (p n j' : ℕ)
    (hjn : j' ≤ n)
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
neighbourhood `N` of `B`, `c ∈ H^j(Y, Y - B)` `a ∈ H_i X` and `b ∈ H_k Y`: through
`X × N ≅ pr⁻¹ N`, `a × (c ∩_N b) = pr^* c ∩_{pr⁻¹ N} (a × b)`. -/
theorem exteriorProduct_capProductNbhd_pullback_prSnd (X Y : TopCat.{u}) {B N : Set Y}
    (hB : IsClosed B) (hN : IsClosed N) (hBN : B ⊆ interior N) (i j k : ℤ)
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
      exteriorProduct_tmul_of_neg R _ _ (Or.inl hi), map_zero, map_zero, map_zero]
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
    have hz := capHomQNbhd_relCohomologyMap_crossHomQ_eq_zero_of_lt (A := Bᶜ) (X := X)
      hB.isOpen_compl hN
      (compl_union_interior_eq_univ hBN) p j' n (p + n - j') (by omega)
      (isClosed_prPre (X := X) hB).isOpen_compl
      (compl_union_interior_eq_univ (preimage_subset_interior_preimage (prSnd X Y) hBN))
      Set.preimage_compl.superset e hnj (relativeSingularCohomologyEquiv R Bᶜ j' c)
      (homologyEquiv R X p a) (homologyEquiv R Y n b)
    simp only [hz, map_zero]
  exact exteriorProduct_capProductNbhd_pullback_prSnd_natCast R X Y hB hN hBN p n j' hjn c a b

/-- **Cap products and exterior products** (Fulton §19.1; [BT] 2.2; Dold VII.12.17). Let `B` be
closed in a space `Y`, `c ∈ H^j(Y, Y - B)` `pr : X × Y → Y` the projection,
`a ∈ H_i X` and `b ∈ H_k Y`. Then `pr^*(c) ∩ (a × b) = a × (c ∩ b)` in `H_{i+k-j}(X × B)`,
through the identification `X × B ≅ pr⁻¹ B` (`BorelMooreCap.prodPreimage`, a homeomorphism).
The cap products into `H_* B` and `H_*(pr⁻¹ B)` are defined (`capProductSupport`) when `B` and
`pr⁻¹ B` have arbitrarily small proper neighbourhood deformations, hence these hypotheses. -/
theorem exteriorProduct_capProductSupport_pullback_prSnd (X Y : TopCat.{u})
    {B : Set Y} (hB : IsClosed B) (hBd : HasProperNeighbourhoodDeformations B)
    (hXBd : HasProperNeighbourhoodDeformations (prSnd X Y ⁻¹' B)) (i j k : ℤ)
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
  have hr'B : ∀ y : prPre X N, (y : TopCat.of (X × Y)) ∈ prPre X B →
      (r' y : TopCat.of (X × Y)) = y :=
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
    exteriorProduct_capProductNbhd_pullback_prSnd R X Y hB hN hBN i j k c a b,
    pushforward_eq_homologyMap, homologyMap_congrDegree]
  rfl

end borelMooreHomology

end MMP

