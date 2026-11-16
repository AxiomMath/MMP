module

public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic

/-!
# Realizations of open immersions, of isomorphisms over an open, and of preimages

Let `X` be a scheme over `ℂ` and `X^an` its complex realization. For an open immersion
`j : U ⟶ X` over `ℂ` (for instance the inclusion of an open subscheme), the realized map
`U^an → X^an` is an open embedding whose image is the set of `ℂ`-points lying over `j(U)`.
Consequently, if a morphism `f : X ⟶ Y` over `ℂ` restricts to an isomorphism `f⁻¹(V) ≅ V` over
an open `V ⊆ Y`, then `f^an` restricts to a homeomorphism from `(f^an)⁻¹(V^an)` onto `V^an`,
where `V^an` is the set of `ℂ`-points of `Y` lying over `V`. This applies to the blowup
`b : V' ⟶ V` of a scheme in an ideal sheaf with support `T`, which is an isomorphism off `T`:
`b^an` restricts to a homeomorphism `V'^an - b⁻¹(T)^an ≃ₜ V^an - T^an`.

For a set `Q` of points of `Y`, the preimage of `Q^an = {y | y lies over Q}` under `f^an` is
`f⁻¹(Q)^an`, and for every continuous map and every subset of its target the square formed by
the preimage, with the subspace topologies, is a pullback square in `TopCat`.

## Main results

* `MMP.Analytic.ComplexPoints.isOpenEmbedding_realize_of_isOpenImmersion`,
  `MMP.Analytic.ComplexPoints.range_realize_of_isOpenImmersion`: the realization of an open
  immersion is an open embedding onto the points lying over its image.
* `MMP.Analytic.ComplexPoints.isHomeomorph_restrictPreimage_realize`: a morphism which is an
  isomorphism over `V` realizes to a homeomorphism over `V^an`.
* `MMP.Analytic.ComplexPoints.isHomeomorph_restrictPreimage_realize_blowUpToBase`: the
  realization of a blowup is a homeomorphism off the centre.
* `MMP.Analytic.ComplexPoints.preimage_realize_setOf_toScheme_mem`: `(f^an)⁻¹(Q^an) = f⁻¹(Q)^an`.
* `MMP.Analytic.ComplexPoints.isPullback_restrictPreimage`: the preimage square of a subset is
  a pullback in `TopCat`.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*]
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace MMP.Analytic.ComplexPoints

variable {X Y U : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
  {sU : U ⟶ Spec (.of ℂ)}

/-- The point of the scheme under the realization of `g` is the image under `g`. -/
@[simp]
lemma toScheme_realize (g : X ⟶ Y) (hg : g ≫ sY = sX) (x : ComplexPoints sX) :
    (realize g hg x).toScheme = g x.toScheme :=
  rfl

/-- The preimage of `Q^an` under `f^an` is `f⁻¹(Q)^an`. -/
lemma preimage_realize_setOf_toScheme_mem (f : X ⟶ Y) (hf : f ≫ sY = sX) (Q : Set Y) :
    realize f hf ⁻¹' {y : ComplexPoints sY | y.toScheme ∈ Q} =
      {x : ComplexPoints sX | x.toScheme ∈ f ⁻¹' Q} :=
  rfl

/-- `Q^an` is closed in `Y^an` for `Q` Zariski closed. -/
lemma isClosed_setOf_toScheme_mem {Q : Set Y} (hQ : IsClosed Q) :
    IsClosed {y : ComplexPoints sY | y.toScheme ∈ Q} :=
  hQ.preimage continuous_toScheme

/-- `V^an` is open in `Y^an` for `V` Zariski open. -/
lemma isOpen_setOf_toScheme_mem {V : Set Y} (hV : IsOpen V) :
    IsOpen {y : ComplexPoints sY | y.toScheme ∈ V} :=
  hV.preimage continuous_toScheme

/-- The image of the realization of an open immersion `j : U ⟶ X` is the set of `ℂ`-points of
`X` lying over the image of `j`. -/
theorem range_realize_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU) :
    Set.range (realize j hj) = {x : ComplexPoints sX | x.toScheme ∈ j.opensRange} := by
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · have H : Set.range x.hom ⊆ Set.range j := by
      rintro _ ⟨p, rfl⟩
      rw [Subsingleton.elim p default]
      exact hx
    refine ⟨⟨IsOpenImmersion.lift j x.hom H, ?_⟩, ?_⟩
    · rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac, x.hom_comp_structure]
    · ext1
      exact IsOpenImmersion.lift_fac j x.hom H

/-- **The realization of an open immersion is an open embedding.** -/
theorem isOpenEmbedding_realize_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ sX = sU) : IsOpenEmbedding (realize j hj) := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  let : U.Over (Spec (.of ℂ)) := ⟨sU⟩
  have : j.IsOver (Spec (.of ℂ)) := ⟨hj⟩
  exact (homeomorphUnderlyingSpace (X := X)).symm.isOpenEmbedding.comp
    ((MMP.UnderlyingSpace.isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) j).comp
      (homeomorphUnderlyingSpace (X := U)).isOpenEmbedding)

/-- The inclusion of the `ℂ`-points of an open subscheme `W ⊆ X` is an open embedding. -/
theorem isOpenEmbedding_realize_ι (W : X.Opens) :
    IsOpenEmbedding (realize (sX := W.ι ≫ sX) W.ι rfl) :=
  isOpenEmbedding_realize_of_isOpenImmersion W.ι rfl

/-- The image of the inclusion of the `ℂ`-points of an open subscheme `W ⊆ X` is the set of
`ℂ`-points lying in `W`. -/
theorem range_realize_ι (W : X.Opens) :
    Set.range (realize (sX := W.ι ≫ sX) W.ι rfl) = {x : ComplexPoints sX | x.toScheme ∈ W} := by
  rw [range_realize_of_isOpenImmersion, Scheme.Opens.opensRange_ι]

/-- The realization of an isomorphism over `ℂ`, as a homeomorphism. -/
def realizeHomeomorph (g : X ⟶ Y) [IsIso g] (hg : g ≫ sY = sX) :
    ComplexPoints sX ≃ₜ ComplexPoints sY where
  toFun := realize g hg
  invFun := realize (inv g) (by rw [← hg, IsIso.inv_hom_id_assoc])
  left_inv x := by ext1; simp
  right_inv y := by ext1; simp
  continuous_toFun := continuous_realize _ _
  continuous_invFun := continuous_realize _ _

/-- The homeomorphism `realizeHomeomorph g hg` acts on `ℂ`-points as the realization of `g`. -/
@[simp]
lemma realizeHomeomorph_apply (g : X ⟶ Y) [IsIso g] (hg : g ≫ sY = sX) (x : ComplexPoints sX) :
    realizeHomeomorph g hg x = realize g hg x :=
  rfl

/-- The inverse of `realizeHomeomorph g hg` acts on `ℂ`-points as the realization of `inv g`. -/
@[simp]
lemma realizeHomeomorph_symm_apply (g : X ⟶ Y) [IsIso g] (hg : g ≫ sY = sX)
    (y : ComplexPoints sY) :
    (realizeHomeomorph g hg).symm y = realize (inv g) (by rw [← hg, IsIso.inv_hom_id_assoc]) y :=
  rfl

/-- **A morphism which is an isomorphism over an open `V` realizes to a homeomorphism over
`V^an`.** If `f : X ⟶ Y` over `ℂ` restricts to an isomorphism `f⁻¹(V) ≅ V`, then `f^an`
restricts to a homeomorphism from `(f^an)⁻¹(V^an)` onto `V^an`, where `V^an` is the set of
`ℂ`-points of `Y` lying over `V`. -/
theorem isHomeomorph_restrictPreimage_realize (f : X ⟶ Y) (hf : f ≫ sY = sX) (V : Y.Opens)
    [IsIso (f ∣_ V)] :
    IsHomeomorph ({y : ComplexPoints sY | y.toScheme ∈ V}.restrictPreimage (realize f hf)) := by
  set S := {y : ComplexPoints sY | y.toScheme ∈ V}
  have hφ : f ∣_ V ≫ V.ι ≫ sY = (f ⁻¹ᵁ V).ι ≫ sX := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hf]
  let eP := (isOpenEmbedding_realize_ι (sX := sX) (f ⁻¹ᵁ V)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_realize_ι (f ⁻¹ᵁ V)))
  let eS := (isOpenEmbedding_realize_ι (sX := sY) V).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_realize_ι V))
  let eφ := realizeHomeomorph (f ∣_ V) hφ
  have key : S.restrictPreimage (realize f hf) = eS ∘ eφ ∘ eP.symm := by
    funext p
    obtain ⟨u, rfl⟩ := eP.surjective p
    rw [Function.comp_apply, Function.comp_apply, Homeomorph.symm_apply_apply]
    apply Subtype.ext
    change realize f hf (realize (f ⁻¹ᵁ V).ι rfl u) = realize V.ι rfl (realize (f ∣_ V) hφ u)
    ext1
    simp only [realize_hom, Category.assoc, morphismRestrict_ι]
  rw [key]
  exact (eP.symm.trans (eφ.trans eS)).isHomeomorph

/-- **The realization of a blowup is a homeomorphism off the centre.** For the blowup
`b : V' ⟶ V` of a scheme `V` over `ℂ` in an ideal sheaf `I` with support `T`, the realized map
`b^an` restricts to a homeomorphism from `V'^an - b⁻¹(T)^an = (b^an)⁻¹(V^an - T^an)` onto
`V^an - T^an`. -/
theorem isHomeomorph_restrictPreimage_realize_blowUpToBase {V : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) (I : V.IdealSheafData) :
    IsHomeomorph ({y : ComplexPoints sV | y.toScheme ∉ (I.support : Set V)}.restrictPreimage
      (realize (blowUpToBase I) (rfl : blowUpToBase I ≫ sV = _))) := by
  have := isIso_blowUp_restrict_compl_support I
  exact isHomeomorph_restrictPreimage_realize (blowUpToBase I) rfl
    ⟨(I.support : Set V)ᶜ, I.support.isClosed.isOpen_compl⟩

/-- **The preimage square of a subset is a pullback in `TopCat`.** For a continuous map
`f : X ⟶ Z` and a subset `s ⊆ Z`, the square formed by `f⁻¹(s) ↪ X`, the restriction
`f⁻¹(s) → s`, `f` and `s ↪ Z`, with subspace topologies, is a pullback square. -/
theorem isPullback_restrictPreimage {X Z : TopCat.{u}} (f : X ⟶ Z) (s : Set Z) :
    IsPullback (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of (f ⁻¹' s) ⟶ X)
      (TopCat.ofHom ⟨s.restrictPreimage f, f.hom.continuous.restrictPreimage⟩)
      f (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of s ⟶ Z) := by
  have hmem : ∀ c : PullbackCone f (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of s ⟶ Z), ∀ w, c.fst w ∈ f ⁻¹' s := fun c w ↦ by
    have := ConcreteCategory.congr_hom c.condition w
    simp only [ConcreteCategory.comp_apply] at this
    simp [this]
  refine ⟨⟨rfl⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ TopCat.ofHom ⟨fun w ↦ ⟨c.fst w, hmem c w⟩,
      (c.fst.hom.continuous).subtype_mk _⟩) (fun c ↦ rfl) (fun c ↦ ?_) (fun c m h₁ _ ↦ ?_)⟩⟩
  · ext w
    simpa using ConcreteCategory.congr_hom c.condition w
  · ext w
    exact ConcreteCategory.congr_hom h₁ w

end MMP.Analytic.ComplexPoints
