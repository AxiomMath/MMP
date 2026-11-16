module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksPresentation

/-!
# Local regular presentations on a neighbourhood, for Stacks vector bundles

The local regular presentation `σ|_W = M f`, `f = G σ|_W` of
`MMP.Modules.exists_isLocalRegularPresentation`, built at a complex point `i(x)` of `X`, is a
local regular presentation at every complex point of `X` lying in `W`: `f` cuts out `X` on `W`,
so it vanishes at those points, and it is weakly regular on every basic open of the affine open
on which it is a regular sequence.

## Main results

* `MMP.Modules.exists_isLocalRegularPresentation_nhds`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim
  isRegularClosedImmersionOfCodim_iff_kerGeneratedBy)

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] {e d : ℕ}
  {E : Y.Modules} [E.IsQuasicoherent]

private lemma presheaf_map_map {U W W' : Y.Opens} (h : W ≤ U) (h' : W' ≤ W) (a : Γ(Y, U)) :
    Y.presheaf.map (homOfLE h').op (Y.presheaf.map (homOfLE h).op a) =
      Y.presheaf.map (homOfLE (h'.trans h)).op a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **Local regular presentations on a neighbourhood.** At every complex point `i(x)` of `X` in
the open `V` of a chart `c = (V, b)` of `ℰ` there are an open `W ⊆ σ⁻¹(π⁻¹V) = V` containing
`i(x)` and matrices `M`, `G`, `f` which are a local regular presentation of `σ` at every complex
point of `X` lying in `W`. -/
theorem exists_isLocalRegularPresentation_nhds (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d) (σ : Y ⟶ totalSpace E)
    (hσ : σ ≫ proj E = 𝟙 Y)
    (hs : zeroLocus E σ = i.ker) (c : Chart E e)
    (x : UnderlyingSpace ℂ X) (hx : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ c.1.1) :
    ∃ (W : Y.Opens) (hWc : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) (_ : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ W)
      (M : Fin e → Fin d → Γ(Y, W)) (G : Fin d → Fin e → Γ(Y, W)) (f : Fin d → Γ(Y, W)),
      ∀ (x' : UnderlyingSpace ℂ X) (hx' : ⊤ ≤ (mapFun i x').toHom ⁻¹ᵁ W),
        IsLocalRegularPresentation σ c (mapFun i x') hWc hx' M G f := by
  have hp : ∀ (x' : UnderlyingSpace ℂ X) (U : Y.Opens),
      ⊤ ≤ (mapFun i x').toHom ⁻¹ᵁ U ↔ i (x'.toHom (IsLocalRing.closedPoint ℂ)) ∈ U :=
    fun x' U ↦ by
      rw [top_le_preimage_iff, toHom_mapFun]
      exact Iff.rfl
  set p := x.toHom (IsLocalRing.closedPoint ℂ)
  have hx' : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ (σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) := by
    rwa [preimage_preimage_proj_of_comp_eq_id hσ]
  obtain ⟨V, hpV, r, rs, hker, rfl, hreg⟩ :=
    (isRegularClosedImmersionOfCodim_iff_kerGeneratedBy i d).1 hi (i p)
      (subset_closure ⟨p, rfl⟩)
  have hker' : i.ker.ideal V = Ideal.span (Set.range rs) := by rw [i.ker_apply, hker]
  obtain ⟨g, hgle, hpg⟩ := V.2.exists_basicOpen_le
    (V := σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) ⟨i p, (hp x _).1 hx'⟩ hpV
  let ρ := Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op
  let f : Fin r → Γ(Y, Y.basicOpen g) := fun b ↦ ρ (rs b)
  have hW : i.ker.ideal (Y.affineBasicOpen g) = Ideal.span (Set.range f) := by
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, hker', Ideal.map_span]
    congr 1
    rw [← Set.range_comp]
    rfl
  have hS : i.ker.ideal (Y.affineBasicOpen g) =
      Ideal.span (Set.range (sectionCoord σ c (W := Y.basicOpen g) hgle)) :=
    hs ▸ ideal_zeroLocus σ c (Y.affineBasicOpen g) hgle
  have hSW := hS.symm.trans hW
  have hM : ∀ a, ∃ c' : Fin r → Γ(Y, Y.basicOpen g),
      ∑ b, c' b * f b = sectionCoord σ c hgle a := fun a ↦
    Ideal.mem_span_range_iff_exists_fun.1 (show _ ∈ Ideal.span (Set.range f) by
      rw [← hSW]; exact Ideal.subset_span ⟨a, rfl⟩)
  have hG : ∀ b, ∃ c' : Fin e → Γ(Y, Y.basicOpen g),
      ∑ a, c' a * sectionCoord σ c hgle a = f b := fun b ↦
    Ideal.mem_span_range_iff_exists_fun.1 (show f b ∈ Ideal.span
      (Set.range (sectionCoord σ c (W := Y.basicOpen g) hgle)) by
      rw [hSW]; exact Ideal.subset_span ⟨b, rfl⟩)
  choose M hM using hM
  choose G hG using hG
  refine ⟨Y.basicOpen g, hgle, (hp x _).2 hpg, M, G, f, fun x' hx' ↦
    ⟨fun a ↦ (hM a).symm, fun b ↦ (hG b).symm, fun b ↦ ?_, fun W' hW' hx'' ↦ ?_⟩⟩
  · exact eval_mapFun_eq_zero_of_mem_ker i x' (W := Y.affineBasicOpen g) _
      (by rw [hW]; exact Ideal.subset_span ⟨b, rfl⟩)
  · have hp'V : i (x'.toHom (IsLocalRing.closedPoint ℂ)) ∈ V.1 :=
      Y.basicOpen_le g ((hp x' _).1 hx')
    obtain ⟨g', hg'le, hpg'⟩ := V.2.exists_basicOpen_le (V := W') ⟨_, (hp x' _).1 hx''⟩ hp'V
    refine ⟨Y.basicOpen g', hg'le, (hp x' _).2 hpg', ?_⟩
    have := isWeaklyRegular_map_basicOpen V.2 hreg g'
    convert this using 1
    rw [List.map_ofFn]
    congr 1
    funext b
    simp only [f, ρ, Function.comp_apply, presheaf_map_map]

end MMP.Modules
