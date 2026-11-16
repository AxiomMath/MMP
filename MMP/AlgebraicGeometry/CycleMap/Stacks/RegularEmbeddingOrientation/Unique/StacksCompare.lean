module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Unique.StacksPresentation
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksEmbedding

/-!
# Two common presentations of a pair of sections of Stacks bundles, in any charts

Let `σ₁`, `σ₂` be sections of the vector bundles `𝐕(ℰ₁)`, `𝐕(ℰ₂)` on a scheme `Y` over `ℂ`. Two
common local regular presentations `(M₁, M₂, f)` (charts `c₁`, `c₂`) and `(M₁', M₂', f')` (charts
`c₁'`, `c₂'`) of `σ₁`, `σ₂` at a point `x` give the same points of `𝐕(ℰ₁)(ℂ)`, `𝐕(ℰ₂)(ℂ)` up to
one matrix: there is `T : ℂᵈ → ℂᵈ` with `φ_{c₁'}⁻¹(x, M₁'(x) v) = φ_{c₁}⁻¹(x, M₁(x) T v)` and
`φ_{c₂'}⁻¹(x, M₂'(x) v) = φ_{c₂}⁻¹(x, M₂(x) T v)`.

## Main results

* `MMP.Modules.IsLocalRegularPresentation.restrict`
* `MMP.Modules.IsLocalRegularPresentation.exists_chartInv_eq_pair`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped Matrix

namespace MMP.Modules

open UnderlyingSpace

variable {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] {e e' d : ℕ}

omit [Y.Over (Spec (.of ℂ))] in
private lemma presheaf_map_map'' {U W W' : Y.Opens} (h : W ≤ U) (h' : W' ≤ W) (a : Γ(Y, U)) :
    Y.presheaf.map (homOfLE h').op (Y.presheaf.map (homOfLE h).op a) =
      Y.presheaf.map (homOfLE (h'.trans h)).op a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {E : Y.Modules} [E.IsQuasicoherent] {σ : Y ⟶ totalSpace E} {c : Chart E e}
  {x : UnderlyingSpace ℂ Y} {W : Y.Opens} {hWc : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)}
  {hxW : ⊤ ≤ x.toHom ⁻¹ᵁ W} {M : Fin e → Fin d → Γ(Y, W)} {G : Fin d → Fin e → Γ(Y, W)}
  {f : Fin d → Γ(Y, W)}

/-- **Restriction of a local regular presentation** to a smaller open `U ∋ x`, with the regular
sequence given as any `f₀` equal to the restriction of `f`. -/
theorem IsLocalRegularPresentation.restrict
    (h : IsLocalRegularPresentation σ c x hWc hxW M G f)
    {U : Y.Opens} (hUW : U ≤ W) (hxU : ⊤ ≤ x.toHom ⁻¹ᵁ U) (f₀ : Fin d → Γ(Y, U))
    (hf₀ : ∀ b, Y.presheaf.map (homOfLE hUW).op (f b) = f₀ b) :
    IsLocalRegularPresentation σ c x (hUW.trans hWc) hxU
      (fun a b ↦ Y.presheaf.map (homOfLE hUW).op (M a b))
      (fun b a ↦ Y.presheaf.map (homOfLE hUW).op (G b a)) f₀ where
  eq_M a := by
    have := congrArg (Y.presheaf.map (homOfLE hUW).op) (h.eq_M a)
    simp only [map_sum, map_mul, hf₀, map_sectionCoord] at this
    exact this
  eq_G b := by
    have := congrArg (Y.presheaf.map (homOfLE hUW).op) (h.eq_G b)
    simp only [map_sum, map_mul, hf₀, map_sectionCoord] at this
    exact this
  eval_eq_zero b := by
    rw [← hf₀, eval_restrict]
    exact h.eval_eq_zero b
  isWeaklyRegular W' hW' hx' := by
    obtain ⟨W'', hW'', hx'', hreg⟩ := h.isWeaklyRegular W' (hW'.trans hUW) hx'
    refine ⟨W'', hW'', hx'', ?_⟩
    convert hreg using 2
    funext b
    simp only [← hf₀, presheaf_map_map'']

/-- The values at `x` of the matrix of a restricted presentation are those of the original. -/
lemma evalMatrix_restrict {U : Y.Opens} (hUW : U ≤ W) (hxU : ⊤ ≤ x.toHom ⁻¹ᵁ U) {m n : ℕ}
    (A : Fin m → Fin n → Γ(Y, W)) :
    evalMatrix x hxU (fun a b ↦ Y.presheaf.map (homOfLE hUW).op (A a b)) = evalMatrix x hxW A := by
  refine LinearMap.ext fun v ↦ funext fun a ↦ ?_
  simp only [evalMatrix_apply, eval_restrict]

/-- **Two common presentations of a pair of sections, in any charts.** If `(M₁, M₂, f)` on `W`
(charts `c₁`, `c₂`) and `(M₁', M₂', f')` on `W'` (charts `c₁'`, `c₂'`) are common local regular
presentations of `σ₁`, `σ₂` at `x`, there is `T : ℂᵈ → ℂᵈ` with
`φ_{c₁'}⁻¹(x, M₁'(x) v) = φ_{c₁}⁻¹(x, M₁(x) T v)` and the same for `σ₂`. -/
theorem IsLocalRegularPresentation.exists_chartInv_eq_pair {E₁ E₂ : Y.Modules}
    [E₁.IsQuasicoherent] [E₂.IsQuasicoherent] {σ₁ : Y ⟶ totalSpace E₁}
    {σ₂ : Y ⟶ totalSpace E₂} (hσ₁ : σ₁ ≫ proj E₁ = 𝟙 Y) (hσ₂ : σ₂ ≫ proj E₂ = 𝟙 Y)
    {c₁ c₁' : Chart E₁ e} {c₂ c₂' : Chart E₂ e'} {W W' : Y.Opens}
    {hW₁ : W ≤ σ₁ ⁻¹ᵁ (proj E₁ ⁻¹ᵁ c₁.1.1)} {hW₂ : W ≤ σ₂ ⁻¹ᵁ (proj E₂ ⁻¹ᵁ c₂.1.1)}
    {hW₁' : W' ≤ σ₁ ⁻¹ᵁ (proj E₁ ⁻¹ᵁ c₁'.1.1)} {hW₂' : W' ≤ σ₂ ⁻¹ᵁ (proj E₂ ⁻¹ᵁ c₂'.1.1)}
    {hxW : ⊤ ≤ x.toHom ⁻¹ᵁ W} {hxW' : ⊤ ≤ x.toHom ⁻¹ᵁ W'}
    {M₁ : Fin e → Fin d → Γ(Y, W)} {G₁ : Fin d → Fin e → Γ(Y, W)}
    {M₂ : Fin e' → Fin d → Γ(Y, W)} {G₂ : Fin d → Fin e' → Γ(Y, W)} {f : Fin d → Γ(Y, W)}
    {M₁' : Fin e → Fin d → Γ(Y, W')} {G₁' : Fin d → Fin e → Γ(Y, W')}
    {M₂' : Fin e' → Fin d → Γ(Y, W')} {G₂' : Fin d → Fin e' → Γ(Y, W')} {f' : Fin d → Γ(Y, W')}
    (h₁ : IsLocalRegularPresentation σ₁ c₁ x hW₁ hxW M₁ G₁ f)
    (h₂ : IsLocalRegularPresentation σ₂ c₂ x hW₂ hxW M₂ G₂ f)
    (h₁' : IsLocalRegularPresentation σ₁ c₁' x hW₁' hxW' M₁' G₁' f')
    (h₂' : IsLocalRegularPresentation σ₂ c₂' x hW₂' hxW' M₂' G₂' f')
    (hx₁ : ⊤ ≤ x.toHom ⁻¹ᵁ c₁.1.1) (hx₂ : ⊤ ≤ x.toHom ⁻¹ᵁ c₂.1.1)
    (hx₁' : ⊤ ≤ x.toHom ⁻¹ᵁ c₁'.1.1) (hx₂' : ⊤ ≤ x.toHom ⁻¹ᵁ c₂'.1.1) :
    ∃ T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ), ∀ v,
      chartInv c₁' x hx₁' (evalMatrix x hxW' M₁' v) =
          chartInv c₁ x hx₁ (evalMatrix x hxW M₁ (T v)) ∧
        chartInv c₂' x hx₂' (evalMatrix x hxW' M₂' v) =
          chartInv c₂ x hx₂ (evalMatrix x hxW M₂ (T v)) := by
  obtain ⟨U₁, hU₁, hU₁c, hxU₁, N₁, H₁, k₁, hk₁⟩ := h₁'.exists_chart hσ₁ c₁ hx₁
  obtain ⟨U₂, hU₂, hU₂c, hxU₂, N₂, H₂, k₂, hk₂⟩ := h₂'.exists_chart hσ₂ c₂ hx₂
  have hxU₀ : ⊤ ≤ x.toHom ⁻¹ᵁ (U₁ ⊓ U₂) := by
    rw [Scheme.Hom.preimage_inf]; exact le_inf hxU₁ hxU₂
  have hU' : U₁ ⊓ U₂ ≤ W' := inf_le_left.trans hU₁
  let f₀ : Fin d → Γ(Y, U₁ ⊓ U₂) := fun b ↦ Y.presheaf.map (homOfLE hU').op (f' b)
  have r₁ := k₁.restrict (inf_le_left : U₁ ⊓ U₂ ≤ U₁) hxU₀ f₀ fun b ↦ presheaf_map_map'' _ _ _
  have r₂ := k₂.restrict (inf_le_right : U₁ ⊓ U₂ ≤ U₂) hxU₀ f₀ fun b ↦ presheaf_map_map'' _ _ _
  obtain ⟨T, hT₁, hT₂⟩ := IsLocalRegularPresentation.exists_evalMatrix_eq_comp_pair h₁ h₂ r₁ r₂
  rw [evalMatrix_restrict (hxW := hxU₁)] at hT₁
  rw [evalMatrix_restrict (hxW := hxU₂)] at hT₂
  refine ⟨T, fun v ↦ ⟨?_, ?_⟩⟩
  · have := LinearMap.congr_fun hT₁ v
    rw [LinearMap.comp_apply, hk₁] at this
    rw [chartInv_eq_chartInv c₁' c₁ hx₁' hx₁, this]
  · have := LinearMap.congr_fun hT₂ v
    rw [LinearMap.comp_apply, hk₂] at this
    rw [chartInv_eq_chartInv c₂' c₂ hx₂' hx₂, this]

end MMP.Modules
