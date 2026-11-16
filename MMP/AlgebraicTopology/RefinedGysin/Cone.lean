module

public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
/-!
# Capping a cone through the pulled-back bundle (Fulton, proof of Theorem 19.2)

Let `ι : C' → N'` be a proper map (the inclusion of the normal cone `C' = C_{X'} V` in
`N' = g'^* N_X Y`), `ḡ : N' → N` a map, `Z ⊆ N` closed (the zero section of `N`),
`c ∈ H^j(N, N - Z)` and `x ∈ H_k C'`. Then
`ι'_* ((ḡ ∘ ι)^* c ∩ x) = ḡ^* c ∩ ι_* x` in `H_{k-j}(ḡ⁻¹ Z)`.
For `c = u_s` and `x = cl_{C'}[C']` this is Fulton's step
`ĝ^*(u_s) ∩ cl_{C'}[C'] = u_{s'} ∩ cl_{N'}[C']`, once `ḡ^* u_s = u_{s'}`
(`lem_c19_orientation_class_base_change`) and `ι_* cl_{C'}[C'] = cl_{N'}[C']`
(`lem_c19_cycle_map_proper_pushforward`).

## Main results

* `MMP.borelMooreHomology.pushforward_restrictPreimage_capProductSupportPullback_comp`

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology

universe u

namespace MMP

namespace borelMooreHomology

variable (R : Type u) [CommRing R]

/-- **Projection formula through a composite** (Fulton, proof of Theorem 19.2). For a proper
`ι : C' → N'`, a map `ḡ : N' → N`, `Z ⊆ N` closed, `c ∈ H^j(N, N - Z)` and `x ∈ H_k C'`,
`ι'_* ((ι ≫ ḡ)^* c ∩ x) = ḡ^* c ∩ ι_* x` in `H_{k-j}(ḡ⁻¹ Z)`, for `ι' : (ḡ ∘ ι)⁻¹ Z → ḡ⁻¹ Z`
the restriction of `ι`. -/
theorem pushforward_restrictPreimage_capProductSupportPullback_comp {C N' N : TopCat.{u}}
    (ι : C ⟶ N') (hι : IsProperMap ι) (g : N' ⟶ N) {Z : Set N} (hZ : IsClosed Z)
    (hd : HasProperNeighbourhoodDeformations (g ⁻¹' Z))
    (hd' : HasProperNeighbourhoodDeformations ((ι ≫ g) ⁻¹' Z)) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) N Z j)
    (x : borelMooreHomology R (ModuleCat.of R R) C k) :
    (pushforward R (ModuleCat.of R R) (TopCat.ofHom (ι.hom.restrictPreimage (g ⁻¹' Z)))
        (hι.restrictPreimage (g ⁻¹' Z)) (k - j)).hom
        (capProductSupportPullback R (ι ≫ g) hZ hd' j k c x) =
      capProductSupportPullback R g hZ hd j k c
        ((pushforward R (ModuleCat.of R R) ι hι k).hom x) := by
  have h := pushforward_restrictPreimage_capProductSupportPullback R ι hι
    (hZ.preimage g.hom.continuous) hd hd' j k
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g Z j).hom c) x
  rw [capProductSupportPullback_apply R (ι ≫ g), cohomologyWithSupports.pullback_comp]
  exact h

end borelMooreHomology

end MMP
