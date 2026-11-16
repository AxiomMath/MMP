module

public import MMP.AlgebraicGeometry.DeRham.SNCCharts
public import MMP.AlgebraicGeometry.DeRham.RationalForms.Basic

/-!
# Differential forms are determined by their rational forms

Let `X` be an integral scheme, smooth of relative dimension `m` over a field `k`. Every point of
an open `O` has an affine neighbourhood `W ⊆ O` on which `Ω_{X/k}` is free: the sections of `X`
over an affine open are locally standard smooth over `k`
(`MMP.DeRham.locally_isStandardSmoothOfRelativeDimension_sectionAlgebra`), and the Kähler
differentials of a standard smooth algebra are free. On such a `W` a form is determined by its
rational form (`MMP.FourfoldProofs.FractionalLogComplexProof.ratForm_injective`), so by the sheaf
property a form on any open `O` is determined by its rational forms on the affine opens inside
`O`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_affine_free_kaehler`: affine neighbourhoods on
  which `Ω_{X/k}` is free.
* `MMP.FourfoldProofs.FractionalLogComplexProof.eq_of_ratForm_eq`: two forms on an open with the same
  rational forms on every non-empty affine open inside it are equal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- **Affine neighbourhoods with free differentials.** On a scheme smooth over `k`, every point
of an open `O` has an affine neighbourhood `W ⊆ O` with `Ω_{Γ(X, W)/k}` free. -/
theorem exists_affine_free_kaehler {m : ℕ} [SmoothOfRelativeDimension m sX] {O : X.Opens}
    {x : X} (hx : x ∈ O) :
    ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧ (W : X.Opens) ≤ O ∧
      (letI := MMP.Mori.sectionAlgebra sX W; Module.Free Γ(X, W) Ω[Γ(X, W)⁄k]) := by
  obtain ⟨W₀, hW₀, hxW₀, hW₀O⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  let := MMP.Mori.sectionAlgebra sX W₀
  obtain ⟨s, hs, hP⟩ :=
    MMP.DeRham.locally_isStandardSmoothOfRelativeDimension_sectionAlgebra sX (m := m) hW₀
  obtain ⟨⟨t, ht⟩, hxt⟩ :=
    Opens.mem_iSup.mp ((hW₀.self_le_iSup_basicOpen_iff (s := s)).2 hs hxW₀)
  let W : X.affineOpens := ⟨X.basicOpen t, hW₀.basicOpen t⟩
  refine ⟨W, hxt, (X.basicOpen_le t).trans hW₀O, ?_⟩
  let := MMP.Mori.sectionAlgebra sX W
  have : IsLocalization.Away t Γ(X, X.basicOpen t) := hW₀.isLocalization_basicOpen t
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res sX (X.basicOpen_le t)
  let e : Localization.Away t ≃ₐ[Γ(X, W₀)] Γ(X, X.basicOpen t) :=
    IsLocalization.algEquiv (Submonoid.powers t) _ _
  have he : (e : Localization.Away t →+* Γ(X, X.basicOpen t)).comp
      (algebraMap Γ(X, W₀) (Localization.Away t)) = algebraMap Γ(X, W₀) Γ(X, X.basicOpen t) :=
    e.toAlgHom.comp_algebraMap
  have hres : algebraMap k Γ(X, W) =
      (e : Localization.Away t →+* Γ(X, X.basicOpen t)).comp
        ((algebraMap Γ(X, W₀) (Localization.Away t)).comp (algebraMap k Γ(X, W₀))) := by
    rw [← RingHom.comp_assoc, he]
    exact IsScalarTower.algebraMap_eq k Γ(X, W₀) Γ(X, W)
  have h1 : RingHom.IsStandardSmoothOfRelativeDimension m (algebraMap k Γ(X, W)) :=
    hres ▸ RingHom.isStandardSmoothOfRelativeDimension_respectsIso.left _ e.toRingEquiv (hP t ht)
  have : Algebra.IsStandardSmooth k Γ(X, W) :=
    RingHom.isStandardSmooth_algebraMap.1 (h1.isStandardSmooth _)
  infer_instance

/-- **Forms are determined by their rational forms.** On an integral scheme smooth over `k`, two
`q`-forms on an open `O` whose restrictions to every non-empty affine open `W ⊆ O` have the same
rational form are equal. -/
theorem eq_of_ratForm_eq [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension m sX] (q : ℕ)
    {O : X.Opens} (θ θ' : Γ(sX.relativeDifferentialForms (q : ℤ), O))
    (h : ∀ (W : X.affineOpens) (hW : (W : X.Opens) ≤ O) [Nonempty (W : X.Opens)],
      ratForm sX q W ((sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hW).op θ) =
        ratForm sX q W ((sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hW).op θ')) :
    θ = θ' := by
  rw [← sub_eq_zero]
  refine TopCat.Presheaf.section_ext (C := Ab.{u})
    ⟨(sX.relativeDifferentialForms (q : ℤ)).presheaf,
      (sX.relativeDifferentialForms (q : ℤ)).isSheaf⟩ O (θ - θ') 0 fun x hx => ?_
  obtain ⟨W, hxW, hWO, hfree⟩ := exists_affine_free_kaehler sX (m := m) hx
  have : Nonempty (W : X.Opens) := ⟨⟨x, hxW⟩⟩
  have h0 : (sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hWO).op (θ - θ') = 0 := by
    rw [map_sub, sub_eq_zero]
    exact ratForm_injective sX q W hfree (h W hWO)
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hWO) x hxW, h0, map_zero, map_zero]

end MMP.FourfoldProofs.FractionalLogComplexProof
