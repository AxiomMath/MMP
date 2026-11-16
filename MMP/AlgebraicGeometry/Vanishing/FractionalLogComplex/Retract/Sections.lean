module

public import MMP.AlgebraicGeometry.DeRham.RationalForms.OpenFormsConnection
public import MMP.AlgebraicGeometry.Cohomology.HypercohomologyAffineDirectImage

/-!
# Sections of the two sides of the retract

Let `π : V ⟶ Spec ℂ` carry the data `D`, `M` of the fractional logarithmic complex, and let
`g : V' ⟶ V` be a cover with a relative simple normal crossing divisor `S'`. The sections of `C^p`
over an open `W` of `V` are forms on `U ∩ W ∩ U'` (`U = V ∖ D`, `U' = V ∖ (D ∪ Supp M)`), and the
sections of the direct image `g_* Ω^p_{V'}(log S')(-S')` over `W` are forms on
`(V' ∖ S') ∩ g⁻¹ W`. This file collects what the comparison of the two needs: non-empty affine
opens inside these opens, the identification of the terms of `Ω^•_{V'}(log S')(-S')` with the
logarithmic forms, and the compatibility of the actions of `π⁻¹𝒪` on both sides with the map
`k(V) → k(V')` of function fields.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.mem_relativeLogDeRhamTerms_iff`: the terms of
  `Ω^•_{X/S}(log D)(-D)` are the logarithmic forms.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_affineOpen_le_OO`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.exists_affineOpen_le_cU`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.exists_affineOpen_le_preimage`: non-empty affine opens.
* `MMP.FourfoldProofs.FractionalLogComplexProof.germ_inverseImageStructureMap_relRingHom`: the germs of
  the images of a section of `π⁻¹𝒪` in `k(V)` and in `k(V')` correspond.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

/-! ### The terms of the twisted logarithmic complex -/

section Terms

variable (n : ℕ) {X S : Scheme.{0}} (f : X ⟶ S) [SmoothOfRelativeDimension n f]
  (D : MMP.Mori.Divisor X) (hD : D.IsRelativeSNC n f)

/-- **The terms of `Ω^•_{X/S}(log D)(-D)` are the logarithmic forms.** -/
theorem relativeLogDeRhamTerms_suppIdeal_eq :
    MMP.Mori.Divisor.relativeLogDeRhamTerms n f D hD D.suppIdeal =
      MMP.Mori.Divisor.LogSpreadingProof.G1.logSubmodule n f D hD D.suppIdeal := by
  have hd := MMP.Mori.Divisor.LogSpreadingProof.G1.deRham_mem_relativeLogForms hD true
  refine le_antisymm (sInf_le ⟨fun q W ω hω => hω, fun q W ω hω => hd q W.unop ω hω⟩) ?_
  refine le_sInf ?_
  rintro N ⟨hN, -⟩ q
  exact SheafOfModules.Submodule.le_iff.mpr <| PresheafOfModules.Submodule.le_iff.mpr
    fun W ω hω => hN q W.unop ω hω

/-- A form is a section of the `p`-th term of `Ω^•_{X/S}(log D)(-D)` exactly when it is a
logarithmic form. -/
theorem mem_relativeLogDeRhamTerms_iff (p : ℕ) (W : X.Opens)
    (ω : ((MMP.Mori.Divisor.complementDeRhamPushforward f D).X p).val.obj (op W)) :
    ω ∈ (MMP.Mori.Divisor.relativeLogDeRhamTerms n f D hD D.suppIdeal p).obj (op W) ↔
      ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal p W := by
  rw [relativeLogDeRhamTerms_suppIdeal_eq]
  rfl

end Terms

/-! ### Non-empty affine opens -/

section Affine

/-- On an irreducible `V` with `U'` non-empty, every non-empty open `W` contains a non-empty affine
open of `U = V ∖ D` lying in `U ∩ W ∩ U'`. -/
theorem exists_affineOpen_le_OO {V : Scheme.{0}} [PreirreducibleSpace V]
    (D M : MMP.Mori.Divisor V) [Nonempty (cU' D M)] (W : V.Opens) (hW : (W : Set V).Nonempty) :
    ∃ O : (cU D).toScheme.affineOpens, (O : (cU D).toScheme.Opens) ≤ OO D M W ∧
      Nonempty (O : (cU D).toScheme.Opens) := by
  obtain ⟨y, hyW, hyU'⟩ := nonempty_preirreducible_inter W.2 (cU' D M).2 hW
    (let ⟨y⟩ := ‹Nonempty (cU' D M)›; ⟨y.1, y.2⟩)
  have hyU : y ∈ (cU D : Set V) := fun h => hyU' (Or.inl h)
  have hx : (⟨y, hyU⟩ : (cU D).toScheme) ∈ OO D M W := ⟨hyW, hyU'⟩
  obtain ⟨O, hO, hxO, hOle⟩ := Opens.isBasis_iff_nbhd.mp (cU D).toScheme.isBasis_affineOpens hx
  exact ⟨⟨O, hO⟩, hOle, ⟨⟨_, hxO⟩⟩⟩

/-- A non-empty open of `V'` meets `V' ∖ S'` in a non-empty affine open. -/
theorem exists_affineOpen_le_cU {V' : Scheme.{0}} [PreirreducibleSpace V']
    (S' : MMP.Mori.Divisor V') [Nonempty (cU S')] (W' : V'.Opens) (hW : (W' : Set V').Nonempty) :
    ∃ O' : (cU S').toScheme.affineOpens, (O' : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ W' ∧
      Nonempty (O' : (cU S').toScheme.Opens) := by
  obtain ⟨y, hyW, hyU⟩ := nonempty_preirreducible_inter W'.2 (cU S').2 hW
    (let ⟨y⟩ := ‹Nonempty (cU S')›; ⟨y.1, y.2⟩)
  have hx : (⟨y, hyU⟩ : (cU S').toScheme) ∈ (cU S').ι ⁻¹ᵁ W' := hyW
  obtain ⟨O, hO, hxO, hOle⟩ := Opens.isBasis_iff_nbhd.mp (cU S').toScheme.isBasis_affineOpens hx
  exact ⟨⟨O, hO⟩, hOle, ⟨⟨_, hxO⟩⟩⟩

/-- The preimage of a non-empty open under a surjective morphism meets `V' ∖ S'` in a non-empty
affine open. -/
theorem exists_affineOpen_le_preimage {V V' : Scheme.{0}} [PreirreducibleSpace V'] (g : V' ⟶ V)
    [Surjective g] (S' : MMP.Mori.Divisor V') [Nonempty (cU S')] (W : V.Opens)
    (hW : (W : Set V).Nonempty) :
    ∃ O' : (cU S').toScheme.affineOpens, (O' : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W) ∧
      Nonempty (O' : (cU S').toScheme.Opens) := by
  obtain ⟨y, hy⟩ := hW
  obtain ⟨x, rfl⟩ := g.surjective y
  exact exists_affineOpen_le_cU S' (g ⁻¹ᵁ W) ⟨x, hy⟩

/-- An open `W` of `V` is non-empty if `U ∩ W ∩ U'` contains a non-empty open. -/
theorem nonempty_of_le_OO {V : Scheme.{0}} (D M : MMP.Mori.Divisor V) {W : V.Opens}
    {O : (cU D).toScheme.Opens} (hO : O ≤ OO D M W) [Nonempty O] : (W : Set V).Nonempty :=
  let ⟨x⟩ := ‹Nonempty O›; ⟨_, (hO x.2).1⟩

/-- An open of `V` whose preimage contains a non-empty open of `V' ∖ S'` is non-empty. -/
theorem nonempty_of_le_preimage {V V' : Scheme.{0}} (g : V' ⟶ V) (S' : MMP.Mori.Divisor V')
    {W : V.Opens} {O' : (cU S').toScheme.Opens} (hO' : O' ≤ (cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))
    [Nonempty O'] : (W : Set V).Nonempty :=
  let ⟨x⟩ := ‹Nonempty O'›; ⟨_, hO' x.2⟩

end Affine

/-! ### The actions of `π⁻¹𝒪` -/

section Action

variable {V V' : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (g : V' ⟶ V)

/-- The image in `𝒪_{V'}` of a section of `π⁻¹𝒪` is the pull-back of its image in `𝒪_V`. -/
theorem inverseImageStructureMap_relRingHom (W : V.Opens) (a : (invRing π).obj.obj (op W)) :
    ((inverseImageStructureMap (g ≫ π)).hom.app (op (g ⁻¹ᵁ W))).hom
        (((relRingHom g π).hom.app (op W)).hom a) =
      g.app W (((inverseImageStructureMap π).hom.app (op W)).hom a) :=
  congrArg (fun φ => (φ.hom.app (op W)).hom a)
    (Stacks.DeRhamDirectImage.inverseImageCompHom_comp_compInverseImageStructureMap g π)

/-- **The germs of the images of a section of `π⁻¹𝒪` correspond**: on non-empty opens
`O ⊆ U ∩ W ∩ U'` and `O' ⊆ (V' ∖ S') ∩ g⁻¹ W`, the germ in `k(V')` of the image of `a` in
`𝒪_{V'}` is the image under `k(V) → k(V')` of the germ in `k(V)` of its image in `𝒪_V`. -/
theorem germ_inverseImageStructureMap_relRingHom [IsIntegral V] [IsIntegral V'] [Surjective g]
    (D M : MMP.Mori.Divisor V) (S' : MMP.Mori.Divisor V') [Nonempty (cU D)] [Nonempty (cU S')]
    (W : V.Opens) (a : (invRing π).obj.obj (op W))
    {O : (cU D).toScheme.Opens} (hO : O ≤ OO D M W) [Nonempty O]
    {O' : (cU S').toScheme.Opens} (hO' : O' ≤ (cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W)) [Nonempty O'] :
    letI := MMP.Mori.functionFieldMapAlgebra g
    openFunctionFieldEquiv (cU S') ((cU S').toScheme.germToFunctionField O'
        ((cU S').toScheme.presheaf.map (homOfLE hO').op ((cU S').ι.app (g ⁻¹ᵁ W)
          (((inverseImageStructureMap (g ≫ π)).hom.app (op (g ⁻¹ᵁ W))).hom
            (((relRingHom g π).hom.app (op W)).hom a))))) =
      algebraMap V.functionField V'.functionField (openFunctionFieldEquiv (cU D)
        ((cU D).toScheme.germToFunctionField O ((cU D).toScheme.presheaf.map (homOfLE hO).op
          ((cU D).ι.app (W ⊓ cU' D M) (V.presheaf.map (homOfLE inf_le_left).op
            (((inverseImageStructureMap π).hom.app (op W)).hom a)))))) := by
  have : Nonempty W := let ⟨x, hx⟩ := nonempty_of_le_OO D M hO; ⟨⟨x, hx⟩⟩
  have : Nonempty (W ⊓ cU' D M : V.Opens) := let ⟨x⟩ := ‹Nonempty O›; ⟨⟨_, hO x.2⟩⟩
  have : Nonempty (g ⁻¹ᵁ W) := let ⟨x⟩ := ‹Nonempty O'›; ⟨⟨_, hO' x.2⟩⟩
  let := MMP.Mori.functionFieldMapAlgebra g
  refine Eq.trans ?_ (congrArg (algebraMap V.functionField V'.functionField)
    ((openFunctionFieldEquiv_germ_restrict (cU D) hO _).trans
      (germToFunctionField_map (inf_le_left : W ⊓ cU' D M ≤ W) _))).symm
  refine (openFunctionFieldEquiv_germ_restrict (cU S') hO' _).trans ?_
  refine (congrArg (V'.germToFunctionField (g ⁻¹ᵁ W))
    (inverseImageStructureMap_relRingHom π g W a)).trans ?_
  rw [Scheme.Hom.app_eq_appLE]
  exact (MMP.Spreading.functionFieldMap_germToFunctionField g W (g ⁻¹ᵁ W) le_rfl _).symm

end Action

end MMP.FourfoldProofs.FractionalLogComplexProof
