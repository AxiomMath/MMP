module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksNormalFibre
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimLocal
public import Mathlib.RingTheory.Regular.Flat

/-!
# Local regular presentations of a section of a vector bundle cutting out a regular imbedding

Let `i : X → Y` be a regular imbedding of codimension `d` of schemes over `ℂ`, and
`σ : Y ⟶ 𝐕(ℰ)` a section of the vector bundle of a quasi-coherent `𝒪_Y`-module `ℰ`, finite
locally free of rank `e`, with zero scheme `Z(σ) = X`. At every complex point `x = i(x')` of `X`
lying in a chart `c = (V, b)` of `ℰ`, the local coordinates of `σ` and a regular sequence cutting
out `X` generate each other on a basic affine open neighbourhood of `x` inside `V`: this is a
local regular presentation (`MMP.Modules.IsLocalRegularPresentation`), to which
`MMP.Modules.normalFibre_eq_range` applies.

## Main results

* `MMP.Modules.eval_mapFun_eq_zero_of_mem_ker`: a section in the ideal of `X` vanishes at the
  complex points of `X`.
* `MMP.Modules.isWeaklyRegular_map_basicOpen`: a weakly regular sequence on an affine open `V`
  stays weakly regular on every basic open of `V`.
* `MMP.Modules.exists_isLocalRegularPresentation`: local regular presentations exist at every
  complex point of `X` in a chart of `ℰ`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim
  isRegularClosedImmersionOfCodim_iff_kerGeneratedBy)

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] {e d : ℕ}

private lemma presheaf_map_map {U W W' : Y.Opens} (h : W ≤ U) (h' : W' ≤ W) (a : Γ(Y, U)) :
    Y.presheaf.map (homOfLE h').op (Y.presheaf.map (homOfLE h).op a) =
      Y.presheaf.map (homOfLE (h'.trans h)).op a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- A section in the ideal of a closed subscheme `X` vanishes at the complex points of `X`. -/
lemma eval_mapFun_eq_zero_of_mem_ker (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))] [QuasiCompact i]
    (x : UnderlyingSpace ℂ X) {W : Y.affineOpens} (hx : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ W.1)
    {g : Γ(Y, W.1)} (hg : g ∈ i.ker.ideal W) : eval (mapFun i x) hx g = 0 := by
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hg
  rw [eval_mapFun, hg]
  exact map_zero (evalRingHom (K := ℂ) (U := i ⁻¹ᵁ W.1) x hx)

/-- A weakly regular sequence on an affine open `V` stays weakly regular on each basic open
`D(g) ⊆ V`, `Γ(Y, D(g))` being the localization of `Γ(Y, V)` away from `g`. -/
lemma isWeaklyRegular_map_basicOpen {V : Y.Opens} (hV : IsAffineOpen V) {rs : List Γ(Y, V)}
    (h : RingTheory.Sequence.IsWeaklyRegular Γ(Y, V) rs) (g : Γ(Y, V)) :
    RingTheory.Sequence.IsWeaklyRegular Γ(Y, Y.basicOpen g)
      (rs.map (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom) := by
  letI := (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  haveI := hV.isLocalization_basicOpen g
  exact h.of_isLocalization (S := Γ(Y, Y.basicOpen g)) (T := Submonoid.powers g)

variable {E : Y.Modules} [E.IsQuasicoherent]

/-- **Local regular presentations exist.** Let `i : X → Y` be a regular imbedding of codimension
`d` and `σ` a section of `𝐕(ℰ)` with `Z(σ) = X`. At every complex point `i(x)` of `X` in the
open `V` of a chart `c = (V, b)` of `ℰ` there are a basic affine open `W ⊆ V` containing `i(x)`,
a regular sequence `f₁, …, f_d` cutting out `X` on `W`, and matrices `M`, `G` with `σ|_W = M f`
and `f = G σ|_W`, `f` being weakly regular on arbitrarily small neighbourhoods of `i(x)`. -/
theorem exists_isLocalRegularPresentation (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d) (σ : Y ⟶ totalSpace E)
    (hσ : σ ≫ proj E = 𝟙 Y)
    (hs : zeroLocus E σ = i.ker) (c : Chart E e)
    (x : UnderlyingSpace ℂ X) (hx : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ c.1.1) :
    ∃ (W : Y.Opens) (hWc : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) (hxW : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ W)
      (M : Fin e → Fin d → Γ(Y, W)) (G : Fin d → Fin e → Γ(Y, W)) (f : Fin d → Γ(Y, W)),
      IsLocalRegularPresentation σ c (mapFun i x) hWc hxW M G f := by
  set p := x.toHom (IsLocalRing.closedPoint ℂ)
  have hp : ∀ U : Y.Opens, ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ U ↔ i p ∈ U := fun U ↦ by
    rw [top_le_preimage_iff, toHom_mapFun]
    exact Iff.rfl
  have hx' : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ (σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) := by
    rwa [preimage_preimage_proj_of_comp_eq_id hσ]
  obtain ⟨V, hpV, r, rs, hker, rfl, hreg⟩ :=
    (isRegularClosedImmersionOfCodim_iff_kerGeneratedBy i d).1 hi (i p)
      (subset_closure ⟨p, rfl⟩)
  have hker' : i.ker.ideal V = Ideal.span (Set.range rs) := by rw [i.ker_apply, hker]
  obtain ⟨g, hgle, hpg⟩ := V.2.exists_basicOpen_le
    (V := σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) ⟨i p, (hp _).1 hx'⟩ hpV
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
  refine ⟨Y.basicOpen g, hgle, (hp _).2 hpg, M, G, f, fun a ↦ (hM a).symm, fun b ↦ (hG b).symm,
    fun b ↦ ?_, fun W' hW' hx' ↦ ?_⟩
  · exact eval_mapFun_eq_zero_of_mem_ker i x (W := Y.affineBasicOpen g) _
      (by rw [hW]; exact Ideal.subset_span ⟨b, rfl⟩)
  · obtain ⟨g', hg'le, hpg'⟩ := V.2.exists_basicOpen_le (V := W') ⟨i p, (hp _).1 hx'⟩ hpV
    refine ⟨Y.basicOpen g', hg'le, (hp _).2 hpg', ?_⟩
    have := isWeaklyRegular_map_basicOpen V.2 hreg g'
    convert this using 1
    rw [List.map_ofFn]
    congr 1
    funext b
    simp only [f, ρ, Function.comp_apply, presheaf_map_map]

end MMP.Modules
