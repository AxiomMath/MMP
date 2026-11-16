module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksClass
public import MMP.RingTheory.Regular.RegularSequenceFibre
/-!
# The normal fibre of a zero scheme cut out by a regular sequence, for Stacks vector bundles

Let `σ : Y ⟶ 𝐕(ℰ)` be a section of the vector bundle of a quasi-coherent `𝒪_Y`-module `ℰ`,
finite locally free of rank `e`, on a complex scheme `Y`, `c = (V, b)` a chart of `ℰ` and
`x ∈ Y(ℂ)`. Suppose that on an open `W ⊆ σ⁻¹(π⁻¹V) = V` containing `x` the local coordinates
`σ^♯bₐ` of `σ` and a sequence `f₁, …, f_d ∈ Γ(Y, W)` vanishing at `x` generate each other,
`σ|_W = M f` and `f = G σ|_W`, and that `f` is weakly regular on arbitrarily small open
neighbourhoods of `x` in `W`. Then the fibre `N_x ⊆ ℂᵉ` of the normal bundle of `Z(σ)` in the
chart coordinates (`MMP.Modules.normalFibre`) is the range of the matrix `M(x)`, and
`G(x) M(x) = 1`.

## Main results

* `MMP.Modules.normalFibre_eq_range`: `N_x = range M(x)`.
* `MMP.Modules.eval_mul_eval_eq_one`: `G(x) M(x) = 1`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace MMP.Modules

open UnderlyingSpace

variable {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] {E : Y.Modules} [E.IsQuasicoherent] {e d : ℕ}

private lemma map_map {U W W' : Y.Opens} (h : W ≤ U) (h' : W' ≤ W) (a : Γ(Y, U)) :
    Y.presheaf.map (homOfLE h').op (Y.presheaf.map (homOfLE h).op a) =
      Y.presheaf.map (homOfLE (h'.trans h)).op a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The hypotheses of the local analysis at `x`: on `W ⊆ σ⁻¹(π⁻¹V)`, `σ|_W = M f` and
`f = G σ|_W` in the local coordinates of the chart `c = (V, b)`, `f` vanishes at `x`, and `f` is
weakly regular on arbitrarily small neighbourhoods of `x`. -/
structure IsLocalRegularPresentation (σ : Y ⟶ totalSpace E) (c : Chart E e)
    (x : UnderlyingSpace ℂ Y) {W : Y.Opens} (hWc : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1))
    (hxW : ⊤ ≤ x.toHom ⁻¹ᵁ W) (M : Fin e → Fin d → Γ(Y, W))
    (G : Fin d → Fin e → Γ(Y, W)) (f : Fin d → Γ(Y, W)) : Prop where
  eq_M (a : Fin e) : sectionCoord σ c hWc a = ∑ b, M a b * f b
  eq_G (b : Fin d) : f b = ∑ a, G b a * sectionCoord σ c hWc a
  eval_eq_zero (b : Fin d) : eval x hxW (f b) = 0
  isWeaklyRegular (W' : Y.Opens) (hW' : W' ≤ W) (hx' : ⊤ ≤ x.toHom ⁻¹ᵁ W') :
    ∃ (W'' : Y.Opens) (hW'' : W'' ≤ W') (_ : ⊤ ≤ x.toHom ⁻¹ᵁ W''),
      RingTheory.Sequence.IsWeaklyRegular Γ(Y, W'')
        (List.ofFn fun b ↦ Y.presheaf.map (homOfLE (hW''.trans hW')).op (f b))

/-- The matrix `M(x)` of values at `x`, as a linear map `ℂⁿ → ℂᵐ`. -/
def evalMatrix (x : UnderlyingSpace ℂ Y) {W : Y.Opens} (hxW : ⊤ ≤ x.toHom ⁻¹ᵁ W) {m n : ℕ}
    (A : Fin m → Fin n → Γ(Y, W)) : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  Matrix.mulVecLin (Matrix.of fun a b ↦ eval x hxW (A a b))

/-- The `a`-th entry of `A(x) v` is `∑ b, A a b (x) * v b`. -/
lemma evalMatrix_apply (x : UnderlyingSpace ℂ Y) {W : Y.Opens} (hxW : ⊤ ≤ x.toHom ⁻¹ᵁ W)
    {m n : ℕ} (A : Fin m → Fin n → Γ(Y, W)) (v : Fin n → ℂ) (a : Fin m) :
    evalMatrix x hxW A v a = ∑ b, eval x hxW (A a b) * v b :=
  rfl

variable {σ : Y ⟶ totalSpace E} {c : Chart E e} {x : UnderlyingSpace ℂ Y} {W : Y.Opens}
  {hWc : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)} {hxW : ⊤ ≤ x.toHom ⁻¹ᵁ W} {f : Fin d → Γ(Y, W)}
  {M : Fin e → Fin d → Γ(Y, W)} {G : Fin d → Fin e → Γ(Y, W)}

/-- `G(x) M(x) = 1` for a local regular presentation. -/
theorem eval_mul_eval_eq_one (h : IsLocalRegularPresentation σ c x hWc hxW M G f) (b c' : Fin d) :
    ∑ a, eval x hxW (G b a) * eval x hxW (M a c') = if b = c' then 1 else 0 := by
  obtain ⟨W'', hW'', hx'', hreg⟩ := h.isWeaklyRegular W le_rfl hxW
  let ρ := Y.presheaf.map (homOfLE hW'').op
  have hρ : ∀ g : Γ(Y, W), eval x hx'' (ρ g) = eval x hxW g := fun g ↦ eval_restrict hW'' x hx'' g
  have := RegularSequenceFibre.ev_mul_ev_eq_one (evalRingHom x hx'')
    (f := fun b ↦ ρ (f b)) (s := fun a ↦ ρ (sectionCoord σ c hWc a))
    (by simpa [ρ] using hreg) (fun b ↦ by simp [hρ, h.eval_eq_zero b])
    (fun a b ↦ ρ (M a b)) (fun a ↦ by rw [h.eq_M a, map_sum]; simp_rw [map_mul])
    (fun b a ↦ ρ (G b a)) (fun b ↦ by rw [h.eq_G b, map_sum]; simp_rw [map_mul]) b c'
  simpa [hρ] using this

/-- **The normal fibre is the range of `M(x)`.** For a local regular presentation
`σ|_W = M f`, `f = G σ|_W` at `x`, the fibre `N_x ⊆ ℂᵉ` of the normal bundle of `Z(σ)` in the
coordinates of the chart `c` is the range of `M(x)`. -/
theorem normalFibre_eq_range (h : IsLocalRegularPresentation σ c x hWc hxW M G f) :
    normalFibre σ c x = LinearMap.range (evalMatrix x hxW M) := by
  apply le_antisymm
  · intro w hw
    rw [mem_normalFibre] at hw
    refine ⟨evalMatrix x hxW G w, funext fun a ↦ ?_⟩
    have hrel : ∀ a, ∑ c, w c * eval x hxW (RegularSequenceFibre.relation M G a c) = 0 :=
      fun a ↦ by
        have := hw W hWc hxW (RegularSequenceFibre.relation M G a)
          (RegularSequenceFibre.sum_relation_mul_eq_zero M h.eq_M G h.eq_G a)
        simpa [smul_eq_mul] using this
    have := RegularSequenceFibre.eq_mulVec_of_forall_relation (evalRingHom x hxW) M G
      (w := w) (by simpa using hrel) a
    rw [evalMatrix_apply]
    simp_rw [evalMatrix_apply]
    simp only [evalRingHom_apply] at this
    rw [this]
  · rintro _ ⟨v, rfl⟩
    rw [mem_normalFibre]
    intro W' hW' hx' g hg
    have hxWW' : ⊤ ≤ x.toHom ⁻¹ᵁ (W ⊓ W') := by
      rw [Scheme.Hom.preimage_inf]; exact le_inf hxW hx'
    obtain ⟨W'', hW'', hx'', hreg⟩ := h.isWeaklyRegular (W ⊓ W') inf_le_left hxWW'
    let ρ := Y.presheaf.map (homOfLE (hW''.trans inf_le_left)).op
    let ρ' := Y.presheaf.map (homOfLE (hW''.trans inf_le_right)).op
    have hρ : ∀ g : Γ(Y, W), eval x hx'' (ρ g) = eval x hxW g := fun g ↦
      eval_restrict _ x hx'' g
    have hρ' : ∀ g : Γ(Y, W'), eval x hx'' (ρ' g) = eval x hx' g := fun g ↦
      eval_restrict _ x hx'' g
    have hs : ∀ a, ρ' (sectionCoord σ c hW' a) = ρ (sectionCoord σ c hWc a) := fun a ↦ by
      simp only [ρ, ρ', map_sectionCoord]
    have hg' : ∑ a, ρ' (g a) * ρ (sectionCoord σ c hWc a) = 0 := by
      have := congrArg ρ' hg
      rw [map_sum, map_zero] at this
      simpa [hs] using this
    have key := fun b ↦ RegularSequenceFibre.sum_ev_mul_ev_eq_zero (evalRingHom x hx'')
      (f := fun b ↦ ρ (f b)) (s := fun a ↦ ρ (sectionCoord σ c hWc a))
      (by simpa [ρ, map_map] using hreg) (fun b ↦ by simp [hρ, h.eval_eq_zero b])
      (fun a b ↦ ρ (M a b)) (fun a ↦ by rw [h.eq_M a, map_sum]; simp_rw [map_mul]) hg' b
    simp only [evalRingHom_apply, hρ, hρ'] at key
    simp_rw [evalMatrix_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    have := key b
    calc ∑ a, eval x hxW (M a b) * v b * eval x hx' (g a)
        = v b * ∑ a, eval x hx' (g a) * eval x hxW (M a b) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ = 0 := by rw [this, mul_zero]

end MMP.Modules
