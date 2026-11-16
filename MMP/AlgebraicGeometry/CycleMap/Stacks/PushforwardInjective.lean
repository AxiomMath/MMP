module

public import MMP.AlgebraicTopology.BorelMoore.Pushforward

/-!
# Push-forward along a bijective closed embedding is injective

A bijective closed embedding `f : A → B` is a homeomorphism, so push-forward of Borel–Moore
homology along `f` has a left inverse, the push-forward along `f⁻¹`.

## Main results

* `MMP.Chow.pushforward_injective_of_isClosedEmbedding`: push-forward of Borel–Moore homology
  along a bijective closed embedding is injective.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace MMP.Chow

/-- Push-forward of Borel–Moore homology along a bijective closed embedding is injective: the
push-forward along the inverse homeomorphism is a left inverse. -/
theorem pushforward_injective_of_isClosedEmbedding {R : Type} [CommRing R] {A B : TopCat.{0}}
    (f : A ⟶ B) (hf : IsProperMap f) (hemb : Topology.IsClosedEmbedding f)
    (hsurj : Function.Surjective f) (k : ℤ) :
    Function.Injective (borelMooreHomology.pushforward R (ModuleCat.of R R) f hf k).hom := by
  let Φ := hemb.isEmbedding.toHomeomorphOfSurjective hsurj
  have hid : borelMooreHomology.pushforward R (ModuleCat.of R R)
      (f ≫ TopCat.ofHom ⟨Φ.symm, Φ.symm.continuous⟩) (Φ.symm.isProperMap.comp hf) k = 𝟙 _ := by
    convert borelMooreHomology.pushforward_id R (ModuleCat.of R R) (X := A) k using 2
    ext a
    exact Φ.symm_apply_apply a
  rw [borelMooreHomology.pushforward_comp] at hid
  refine Function.LeftInverse.injective
    (g := (borelMooreHomology.pushforward R (ModuleCat.of R R)
      (TopCat.ofHom ⟨Φ.symm, Φ.symm.continuous⟩) Φ.symm.isProperMap k).hom) fun a => ?_
  simpa using congrArg (fun φ ↦ φ.hom a) hid

end MMP.Chow
