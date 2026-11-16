module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksPresentation
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksNormalFibreChart

/-!
# Common local regular presentations of two sections of Stacks bundles

Let `i : X → Y` be a regular imbedding of codimension `d` of schemes over `ℂ`, and `σ₁`, `σ₂`
sections of the vector bundles `𝐕(ℰ₁)`, `𝐕(ℰ₂)` on `Y` with zero schemes `Z(σ₁) = Z(σ₂) = X`.
Every complex point of `X` lying in charts `c₁` of `ℰ₁` and `c₂` of `ℰ₂` has an open
neighbourhood `W` with one regular sequence `f` cutting out `X` on `W`, such that at every complex
point of `X` in `W` both `σ₁` and `σ₂` have local regular presentations with this `f`; a relation
`∑ hᵦ fᵦ = 0` near such a point has coefficients vanishing at it; and a presentation in a chart
`c` moves to any other chart `c'` at the point, its matrix multiplied by the transition matrix.

## Main results

* `MMP.Modules.exists_isLocalRegularPresentation_pair`.
* `MMP.Modules.IsLocalRegularPresentation.eval_eq_zero_of_sum_mul`.
* `MMP.Modules.IsLocalRegularPresentation.evalMatrix_eq_comp`.
* `MMP.Modules.IsLocalRegularPresentation.exists_evalMatrix_eq_comp_pair`.
* `MMP.Modules.IsLocalRegularPresentation.exists_chart`: change of chart.

## Implementation notes

The Stacks charts have no transition sections on the overlap `V ∩ V'` of two charts, only on the
basic opens `D(a) ⊆ V ∩ V'` (`MMP.Modules.transitionSection`), so a presentation moved to another
chart lives on a basic open around the point (`IsLocalRegularPresentation.exists_chart`), where
the local coordinates of the section change by the change-of-basis matrix
(`MMP.Modules.sectionCoord_eq_sum_transitionSection`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped Matrix

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim
  isRegularClosedImmersionOfCodim_iff_kerGeneratedBy)

private lemma presheaf_map_map' {Y : Scheme.{0}} {U W W' : Y.Opens} (h : W ≤ U) (h' : W' ≤ W)
    (a : Γ(Y, U)) :
    Y.presheaf.map (homOfLE h').op (Y.presheaf.map (homOfLE h).op a) =
      Y.presheaf.map (homOfLE (h'.trans h)).op a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

section Presentation

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] {e e' d : ℕ}

/-- **A regular sequence on an affine open presents every section cutting out `X`.** Let `rs` be
a regular sequence on an affine open `V` generating the ideal of `X` there, and `D(g) ⊆ V` a basic
open inside `σ⁻¹(π⁻¹V_c)` for a chart `c` of `ℰ`. If `Z(σ) = X`, there are matrices `M`, `G` with
`σ|_{D(g)} = M f`, `f = G σ|_{D(g)}` (`f = rs|_{D(g)}`), a local regular presentation at every
complex point of `X` in `D(g)`. -/
theorem exists_isLocalRegularPresentation_basicOpen (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion i] {E : Y.Modules} [E.IsQuasicoherent] (σ : Y ⟶ totalSpace E)
    (hs : zeroLocus E σ = i.ker) (c : Chart E e) {V : Y.affineOpens} {rs : Fin d → Γ(Y, V)}
    (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, V) (List.ofFn rs))
    (hker : i.ker.ideal V = Ideal.span (Set.range rs)) {g : Γ(Y, V)}
    (hgle : Y.basicOpen g ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) :
    ∃ (M : Fin e → Fin d → Γ(Y, Y.basicOpen g)) (G : Fin d → Fin e → Γ(Y, Y.basicOpen g)),
      ∀ (x : UnderlyingSpace ℂ X) (hxW : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ Y.basicOpen g),
        IsLocalRegularPresentation σ c (mapFun i x) hgle hxW M G
          (fun b ↦ Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op (rs b)) := by
  let ρ := Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op
  let f : Fin d → Γ(Y, Y.basicOpen g) := fun b ↦ ρ (rs b)
  have hW : i.ker.ideal (Y.affineBasicOpen g) = Ideal.span (Set.range f) := by
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, hker, Ideal.map_span]
    congr 1
    rw [← Set.range_comp]
    rfl
  have hS : i.ker.ideal (Y.affineBasicOpen g) =
      Ideal.span (Set.range (sectionCoord σ c (W := Y.basicOpen g) hgle)) :=
    hs ▸ ideal_zeroLocus σ c (Y.affineBasicOpen g) hgle
  have hSW := hS.symm.trans hW
  have hM : ∀ a, ∃ c' : Fin d → Γ(Y, Y.basicOpen g),
      ∑ b, c' b * f b = sectionCoord σ c hgle a := fun a ↦
    Ideal.mem_span_range_iff_exists_fun.1 (show _ ∈ Ideal.span (Set.range f) by
      rw [← hSW]
      exact Ideal.subset_span ⟨a, rfl⟩)
  have hG : ∀ b, ∃ c' : Fin e → Γ(Y, Y.basicOpen g),
      ∑ a, c' a * sectionCoord σ c hgle a = f b := fun b ↦
    Ideal.mem_span_range_iff_exists_fun.1 (show f b ∈ Ideal.span
      (Set.range (sectionCoord σ c (W := Y.basicOpen g) hgle)) by
      rw [hSW]
      exact Ideal.subset_span ⟨b, rfl⟩)
  choose M hM using hM
  choose G hG using hG
  refine ⟨M, G, fun x hxW ↦ ⟨fun a ↦ (hM a).symm, fun b ↦ (hG b).symm, fun b ↦ ?_,
    fun W' hW' hx' ↦ ?_⟩⟩
  · exact eval_mapFun_eq_zero_of_mem_ker i x (W := Y.affineBasicOpen g) _
      (by
        rw [hW]
        exact Ideal.subset_span ⟨b, rfl⟩)
  · set p := x.toHom (IsLocalRing.closedPoint ℂ)
    have hp : ∀ U : Y.Opens, ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ U ↔ i p ∈ U := fun U ↦ by
      rw [top_le_preimage_iff, toHom_mapFun]
      exact Iff.rfl
    obtain ⟨g', hg'le, hpg'⟩ := V.2.exists_basicOpen_le (V := W') ⟨i p, (hp _).1 hx'⟩
      (Y.basicOpen_le g ((hp _).1 hxW))
    refine ⟨Y.basicOpen g', hg'le, (hp _).2 hpg', ?_⟩
    convert isWeaklyRegular_map_basicOpen V.2 hreg g' using 1
    rw [List.map_ofFn]
    congr 1
    funext b
    simp only [Function.comp_apply, presheaf_map_map']

/-- **Common local regular presentations.** Let `i` be a regular closed imbedding of codimension
`d` and `σ₁`, `σ₂` sections of `𝐕(ℰ₁)`, `𝐕(ℰ₂)` with `Z(σ₁) = Z(σ₂) = X`. A complex point `i(x)`
of `X` in the charts `c₁`, `c₂` has an open neighbourhood `W` with a sequence `f` and matrices
`M₁, G₁, M₂, G₂` giving local regular presentations of both `σ₁` and `σ₂` with the same `f`, at
every complex point of `X` in `W`. -/
theorem exists_isLocalRegularPresentation_pair (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d)
    {E₁ E₂ : Y.Modules} [E₁.IsQuasicoherent] [E₂.IsQuasicoherent]
    {σ₁ : Y ⟶ totalSpace E₁} (hσ₁ : σ₁ ≫ proj E₁ = 𝟙 Y) (hs₁ : zeroLocus E₁ σ₁ = i.ker)
    {σ₂ : Y ⟶ totalSpace E₂} (hσ₂ : σ₂ ≫ proj E₂ = 𝟙 Y) (hs₂ : zeroLocus E₂ σ₂ = i.ker)
    (c₁ : Chart E₁ e) (c₂ : Chart E₂ e') (x : UnderlyingSpace ℂ X)
    (hx₁ : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ c₁.1.1) (hx₂ : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ c₂.1.1) :
    ∃ (W : Y.Opens) (hW₁ : W ≤ σ₁ ⁻¹ᵁ (proj E₁ ⁻¹ᵁ c₁.1.1))
      (hW₂ : W ≤ σ₂ ⁻¹ᵁ (proj E₂ ⁻¹ᵁ c₂.1.1)) (_ : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ W)
      (M₁ : Fin e → Fin d → Γ(Y, W)) (G₁ : Fin d → Fin e → Γ(Y, W))
      (M₂ : Fin e' → Fin d → Γ(Y, W)) (G₂ : Fin d → Fin e' → Γ(Y, W)) (f : Fin d → Γ(Y, W)),
      ∀ (x' : UnderlyingSpace ℂ X) (hx'W : ⊤ ≤ (mapFun i x').toHom ⁻¹ᵁ W),
        IsLocalRegularPresentation σ₁ c₁ (mapFun i x') hW₁ hx'W M₁ G₁ f ∧
          IsLocalRegularPresentation σ₂ c₂ (mapFun i x') hW₂ hx'W M₂ G₂ f := by
  set p := x.toHom (IsLocalRing.closedPoint ℂ)
  have hp : ∀ U : Y.Opens, ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ U ↔ i p ∈ U := fun U ↦ by
    rw [top_le_preimage_iff, toHom_mapFun]
    exact Iff.rfl
  obtain ⟨V, hpV, r, rs, hker, rfl, hreg⟩ :=
    (isRegularClosedImmersionOfCodim_iff_kerGeneratedBy i d).1 hi (i p)
      (subset_closure ⟨p, rfl⟩)
  have hker' : i.ker.ideal V = Ideal.span (Set.range rs) := by rw [i.ker_apply, hker]
  have h₁ : c₁.1.1 ≤ σ₁ ⁻¹ᵁ (proj E₁ ⁻¹ᵁ c₁.1.1) :=
    (preimage_preimage_proj_of_comp_eq_id hσ₁ _).ge
  have h₂ : c₂.1.1 ≤ σ₂ ⁻¹ᵁ (proj E₂ ⁻¹ᵁ c₂.1.1) :=
    (preimage_preimage_proj_of_comp_eq_id hσ₂ _).ge
  obtain ⟨g, hgle, hpg⟩ := V.2.exists_basicOpen_le (V := c₁.1.1 ⊓ c₂.1.1)
    ⟨i p, (hp _).1 hx₁, (hp _).1 hx₂⟩ hpV
  obtain ⟨M₁, G₁, k₁⟩ := exists_isLocalRegularPresentation_basicOpen i σ₁ hs₁ c₁ hreg hker'
    ((hgle.trans inf_le_left).trans h₁)
  obtain ⟨M₂, G₂, k₂⟩ := exists_isLocalRegularPresentation_basicOpen i σ₂ hs₂ c₂ hreg hker'
    ((hgle.trans inf_le_right).trans h₂)
  exact ⟨Y.basicOpen g, _, _, (hp _).2 hpg, M₁, G₁, M₂, G₂, _,
    fun x' hx' ↦ ⟨k₁ x' hx', k₂ x' hx'⟩⟩

variable {E : Y.Modules} [E.IsQuasicoherent] {σ : Y ⟶ totalSpace E} {c : Chart E e}
  {x : UnderlyingSpace ℂ Y} {W : Y.Opens} {hWc : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)}
  {hxW : ⊤ ≤ x.toHom ⁻¹ᵁ W} {M : Fin e → Fin d → Γ(Y, W)} {G : Fin d → Fin e → Γ(Y, W)}
  {f : Fin d → Γ(Y, W)}

/-- **Relations among `f` vanish at `x`.** For a local regular presentation at `x`, the
coefficients of a relation `∑ cᵦ fᵦ = 0` on an open `U ∋ x` inside `W` vanish at `x` (they lie in
the ideal `(f)`, by the Koszul property of the regular sequence `f`). -/
theorem IsLocalRegularPresentation.eval_eq_zero_of_sum_mul
    (h : IsLocalRegularPresentation σ c x hWc hxW M G f) {U : Y.Opens} (hU : U ≤ W)
    (hxU : ⊤ ≤ x.toHom ⁻¹ᵁ U) (c' : Fin d → Γ(Y, U))
    (hc : ∑ b, c' b * Y.presheaf.map (homOfLE hU).op (f b) = 0) (b : Fin d) :
    eval x hxU (c' b) = 0 := by
  obtain ⟨W'', hW'', hx'', hreg⟩ := h.isWeaklyRegular U hU hxU
  let ρ := Y.presheaf.map (homOfLE hW'').op
  have hrel : ∑ b, ρ (c' b) * Y.presheaf.map (homOfLE (hW''.trans hU)).op (f b) = 0 := by
    simpa only [map_sum, map_zero, map_mul, ρ, presheaf_map_map'] using congrArg ρ hc
  have hle : Ideal.span (Set.range fun b ↦ Y.presheaf.map (homOfLE (hW''.trans hU)).op (f b)) ≤
      RingHom.ker (evalRingHom x hx'') := by
    rw [Ideal.span_le]
    rintro _ ⟨b', rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, evalRingHom_apply, eval_restrict]
    exact h.eval_eq_zero b'
  simpa only [RingHom.mem_ker, evalRingHom_apply, ρ, eval_restrict] using
    hle (MMP.WeaklyRegular.mem_span_of_sum_mul_eq_zero _ hreg _ hrel b)

/-- **Two presentations at `x` are related at `x` by any change of the regular sequence.** If
`σ|_W = M f` and `σ|_{W'} = M' f'` are local regular presentations at `x` (same chart) and
`f = T f'` on an open `U ∋ x` inside `W ∩ W'`, then `M'(x) = M(x) T(x)`. -/
theorem IsLocalRegularPresentation.evalMatrix_eq_comp
    (hα : IsLocalRegularPresentation σ c x hWc hxW M G f)
    {W' : Y.Opens} {hWc' : W' ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)} {hxW' : ⊤ ≤ x.toHom ⁻¹ᵁ W'}
    {M' : Fin e → Fin d → Γ(Y, W')} {G' : Fin d → Fin e → Γ(Y, W')} {f' : Fin d → Γ(Y, W')}
    (hβ : IsLocalRegularPresentation σ c x hWc' hxW' M' G' f') {U : Y.Opens} (hUα : U ≤ W)
    (hUβ : U ≤ W') (hxU : ⊤ ≤ x.toHom ⁻¹ᵁ U) (T : Fin d → Fin d → Γ(Y, U))
    (hT : ∀ b, Y.presheaf.map (homOfLE hUα).op (f b) =
      ∑ c, T b c * Y.presheaf.map (homOfLE hUβ).op (f' c)) :
    evalMatrix x hxW' M' = evalMatrix x hxW M ∘ₗ evalMatrix x hxU T := by
  let ρ := Y.presheaf.map (homOfLE hUα).op
  let ρ' := Y.presheaf.map (homOfLE hUβ).op
  have key : ∀ a c, eval x hxU (∑ b, ρ (M a b) * T b c - ρ' (M' a c)) = 0 := fun a ↦
    hβ.eval_eq_zero_of_sum_mul hUβ hxU _ (by
      have h1 := congrArg ρ (hα.eq_M a)
      have h2 := congrArg ρ' (hβ.eq_M a)
      rw [map_sum] at h1 h2
      simp only [map_mul, ρ, ρ', map_sectionCoord] at h1 h2
      simp only [ρ, ρ', sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum]
      simp only [← hT]
      rw [← h1, ← h2, sub_self])
  refine LinearMap.ext fun v ↦ funext fun a ↦ ?_
  simp only [LinearMap.comp_apply, evalMatrix_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have := key a c
  rw [← evalRingHom_apply] at this
  simp only [map_sub, map_sum, map_mul, evalRingHom_apply, ρ, ρ', eval_restrict,
    sub_eq_zero] at this
  rw [← this, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

/-- **Two common presentations of a pair of sections differ at `x` by one matrix.** Let
`(M₁, M₂, f)` and `(M₁', M₂', f')` both present `σ₁` (chart `c₁`) and `σ₂` (chart `c₂`) at `x`,
on `W` resp. `W'`. Then there is `T : ℂᵈ → ℂᵈ` with `M₁'(x) = M₁(x) T` and `M₂'(x) = M₂(x) T`. -/
theorem IsLocalRegularPresentation.exists_evalMatrix_eq_comp_pair {E₁ E₂ : Y.Modules}
    [E₁.IsQuasicoherent] [E₂.IsQuasicoherent] {σ₁ : Y ⟶ totalSpace E₁}
    {σ₂ : Y ⟶ totalSpace E₂} {c₁ : Chart E₁ e} {c₂ : Chart E₂ e'} {W W' : Y.Opens}
    {hW₁ : W ≤ σ₁ ⁻¹ᵁ (proj E₁ ⁻¹ᵁ c₁.1.1)} {hW₂ : W ≤ σ₂ ⁻¹ᵁ (proj E₂ ⁻¹ᵁ c₂.1.1)}
    {hW₁' : W' ≤ σ₁ ⁻¹ᵁ (proj E₁ ⁻¹ᵁ c₁.1.1)} {hW₂' : W' ≤ σ₂ ⁻¹ᵁ (proj E₂ ⁻¹ᵁ c₂.1.1)}
    {hxW : ⊤ ≤ x.toHom ⁻¹ᵁ W} {hxW' : ⊤ ≤ x.toHom ⁻¹ᵁ W'}
    {M₁ : Fin e → Fin d → Γ(Y, W)} {G₁ : Fin d → Fin e → Γ(Y, W)}
    {M₂ : Fin e' → Fin d → Γ(Y, W)} {G₂ : Fin d → Fin e' → Γ(Y, W)} {f : Fin d → Γ(Y, W)}
    {M₁' : Fin e → Fin d → Γ(Y, W')} {G₁' : Fin d → Fin e → Γ(Y, W')}
    {M₂' : Fin e' → Fin d → Γ(Y, W')} {G₂' : Fin d → Fin e' → Γ(Y, W')} {f' : Fin d → Γ(Y, W')}
    (h₁ : IsLocalRegularPresentation σ₁ c₁ x hW₁ hxW M₁ G₁ f)
    (h₂ : IsLocalRegularPresentation σ₂ c₂ x hW₂ hxW M₂ G₂ f)
    (h₁' : IsLocalRegularPresentation σ₁ c₁ x hW₁' hxW' M₁' G₁' f')
    (h₂' : IsLocalRegularPresentation σ₂ c₂ x hW₂' hxW' M₂' G₂' f') :
    ∃ T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ), evalMatrix x hxW' M₁' = evalMatrix x hxW M₁ ∘ₗ T ∧
      evalMatrix x hxW' M₂' = evalMatrix x hxW M₂ ∘ₗ T := by
  have hxU : ⊤ ≤ x.toHom ⁻¹ᵁ (W ⊓ W') := by
    rw [Scheme.Hom.preimage_inf]
    exact le_inf hxW hxW'
  let ρ := Y.presheaf.map (homOfLE (inf_le_left : W ⊓ W' ≤ W)).op
  let ρ' := Y.presheaf.map (homOfLE (inf_le_right : W ⊓ W' ≤ W')).op
  -- `f = G₁ σ₁ = G₁ M₁' f'` on `W ∩ W'`
  let T : Fin d → Fin d → Γ(Y, W ⊓ W') := fun b c ↦ ∑ a, ρ (G₁ b a) * ρ' (M₁' a c)
  have hT : ∀ b, ρ (f b) = ∑ c, T b c * ρ' (f' c) := fun b ↦ by
    have h1 := congrArg ρ (h₁.eq_G b)
    simp only [map_sum, map_mul] at h1
    rw [h1]
    simp only [T, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have h2 := congrArg ρ' (h₁'.eq_M a)
    simp only [map_sum, map_mul] at h2
    have hs : ρ (sectionCoord σ₁ c₁ hW₁ a) = ρ' (sectionCoord σ₁ c₁ hW₁' a) := by
      simp only [ρ, ρ', map_sectionCoord]
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [hs, h2]
  exact ⟨evalMatrix x hxU T, h₁.evalMatrix_eq_comp h₁' inf_le_left inf_le_right hxU T hT,
    h₂.evalMatrix_eq_comp h₂' inf_le_left inf_le_right hxU T hT⟩

/-- **Change of chart of a local regular presentation.** If `σ|_W = M f`, `f = G σ|_W` is a local
regular presentation in the chart `c` at `x`, and `x` lies in the chart `c'`, then on a basic open
`U ∋ x` inside `W` and `V ∩ V'` there are matrices `M'`, `G'` giving a local regular presentation
in the chart `c'` with the restriction of `f`, and `M'(x) = g(x) M(x)` for the transition matrix
`g = transition c c'`. -/
theorem IsLocalRegularPresentation.exists_chart (hσ : σ ≫ proj E = 𝟙 Y)
    (h : IsLocalRegularPresentation σ c x hWc hxW M G f) (c' : Chart E e)
    (hxc' : ⊤ ≤ x.toHom ⁻¹ᵁ c'.1.1) :
    ∃ (U : Y.Opens) (hUW : U ≤ W) (hUc' : U ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c'.1.1))
      (hxU : ⊤ ≤ x.toHom ⁻¹ᵁ U) (M' : Fin e → Fin d → Γ(Y, U)) (G' : Fin d → Fin e → Γ(Y, U)),
      IsLocalRegularPresentation σ c' x hUc' hxU M' G'
          (fun b ↦ Y.presheaf.map (homOfLE hUW).op (f b)) ∧
        ∀ v, evalMatrix x hxU M' v = transition c c' x *ᵥ evalMatrix x hxW M v := by
  set p := x.toHom (IsLocalRing.closedPoint ℂ)
  have hp : ∀ U : Y.Opens, ⊤ ≤ x.toHom ⁻¹ᵁ U ↔ p ∈ U := top_le_preimage_iff x
  have hWV : W ≤ c.1.1 := hWc.trans (preimage_preimage_proj_of_comp_eq_id hσ _).le
  have hpW : p ∈ W := (hp W).1 hxW
  obtain ⟨a, ha, hpa⟩ := (isAffineOpen_affineOpens c.1).exists_basicOpen_le (V := c'.1.1)
    ⟨p, (hp _).1 hxc'⟩ (hWV hpW)
  obtain ⟨a', ha', hpa'⟩ := (isAffineOpen_affineOpens c'.1).exists_basicOpen_le
    (V := Y.basicOpen a ⊓ W) ⟨p, hpa, hpW⟩ ((hp _).1 hxc')
  set U := Y.basicOpen a'
  have hUa : U ≤ Y.basicOpen a := ha'.trans inf_le_left
  have hUW : U ≤ W := ha'.trans inf_le_right
  have hU₁ : U ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1) := hUW.trans hWc
  have hU₂ : U ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c'.1.1) :=
    (Y.basicOpen_le a').trans (preimage_preimage_proj_of_comp_eq_id hσ _).ge
  have hxU : ⊤ ≤ x.toHom ⁻¹ᵁ U := (hp _).2 hpa'
  let ρ := Y.presheaf.map (homOfLE hUW).op
  let T : Fin e → Fin e → Γ(Y, U) := fun j i ↦
    Y.presheaf.map (homOfLE hUa).op (transitionSection c c' a ha j i)
  let S : Fin e → Fin e → Γ(Y, U) := fun i k ↦
    Y.presheaf.map (homOfLE (le_refl U)).op
      (transitionSection c' c a' (hUa.trans (Y.basicOpen_le a)) i k)
  have hT : ∀ j, sectionCoord σ c' hU₂ j = ∑ i, T j i * sectionCoord σ c hU₁ i := fun j ↦
    sectionCoord_eq_sum_transitionSection hσ c c' a ha hUa j
  have hS : ∀ i, sectionCoord σ c hU₁ i = ∑ k, S i k * sectionCoord σ c' hU₂ k := fun i ↦
    sectionCoord_eq_sum_transitionSection hσ c' c a' _ le_rfl i
  have hρ : ∀ i, sectionCoord σ c hU₁ i = ρ (sectionCoord σ c hWc i) := fun i ↦
    (map_sectionCoord σ c hWc hUW i).symm
  refine ⟨U, hUW, hU₂, hxU, fun j b ↦ ∑ i, T j i * ρ (M i b),
    fun b k ↦ ∑ i, ρ (G b i) * S i k, ⟨fun j ↦ ?_, fun b ↦ ?_, fun b ↦ ?_,
      fun W' hW' hx' ↦ ?_⟩, fun v ↦ ?_⟩
  · simp_rw [hT, hρ, h.eq_M, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
  · change ρ (f b) = _
    rw [h.eq_G b, map_sum]
    simp_rw [map_mul, ← hρ, hS, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
  · simpa only [eval_restrict] using h.eval_eq_zero b
  · obtain ⟨W'', hW'', hx'', hreg⟩ := h.isWeaklyRegular W' (hW'.trans hUW) hx'
    refine ⟨W'', hW'', hx'', ?_⟩
    convert hreg using 2
    funext b
    simp only [presheaf_map_map']
  · rw [transition_eq_of_basicOpen c c' a ha x ((hp _).2 hpa)]
    funext j
    simp only [evalMatrix_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
    simp only [← evalRingHom_apply x hxU, map_sum, map_mul]
    simp only [evalRingHom_apply, T, ρ, eval_restrict, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

end Presentation

end MMP.Modules
