module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import Mathlib.Topology.FiberBundle.Constructions

/-!
# Fibre squares of complex schemes and points of pull-back bundles

Complex points of a fibre square of schemes over `ℂ`, composites of `appLE` maps, and points of
the pull-back `h^* Q` of a bundle along a continuous map `h`.

## Main results

* `MMP.range_map_eq_preimage_of_isPullback`: in a fibre square `X' = X ×_Y Y'`,
  `X'(ℂ) = f⁻¹(X(ℂ))`.
* `MMP.mapFun_comp_of_isPullback`: the square commutes on complex points.
* `MMP.appLE_appLE_eq`: two composites of `appLE` along maps with the same composite agree.
* `MMP.pullbackMk`, `MMP.pullback_totalSpace_ext`: points of a pull-back `h^* Q` of a bundle.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Bundle Topology

namespace MMP

open UnderlyingSpace

section FibreSquare

variable {X Y X' Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [X'.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))]

/-- **The points of a fibre product.** In a fibre square `X' = X ×_Y Y'` of schemes over `ℂ`,
`X'(ℂ) ⊆ Y'(ℂ)` is the inverse image of `X(ℂ) ⊆ Y(ℂ)`. -/
theorem range_map_eq_preimage_of_isPullback {i : X ⟶ Y} {i' : X' ⟶ Y'} {f : Y' ⟶ Y}
    {g : X' ⟶ X} [i.IsOver (Spec (.of ℂ))] [i'.IsOver (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] (sq : IsPullback i' g f i) :
    range (UnderlyingSpace.map (K := ℂ) i') =
      mapFun f ⁻¹' range (UnderlyingSpace.map (K := ℂ) i) := by
  ext y'
  constructor
  · rintro ⟨x', rfl⟩
    refine ⟨mapFun g x', UnderlyingSpace.ext ?_⟩
    change (x'.toHom ≫ g) ≫ i = (x'.toHom ≫ i') ≫ f
    rw [Category.assoc, Category.assoc, sq.w]
  · rintro ⟨x, hx⟩
    have hw : y'.toHom ≫ f = x.toHom ≫ i := (congrArg UnderlyingSpace.toHom hx).symm
    let l : Spec (.of ℂ) ⟶ X' := sq.lift y'.toHom x.toHom hw
    have hl : l ≫ X' ↘ Spec (.of ℂ) = 𝟙 _ := by
      rw [← comp_over i' (Spec (.of ℂ)), ← Category.assoc, sq.lift_fst]
      exact y'.toHom_comp_over
    exact ⟨⟨l, hl⟩, UnderlyingSpace.ext (sq.lift_fst _ _ _)⟩

variable {i : X ⟶ Y} {i' : X' ⟶ Y'} {f : Y' ⟶ Y} {g : X' ⟶ X} [i.IsOver (Spec (.of ℂ))]
  [i'.IsOver (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))]

/-- In a fibre square `X' = X ×_Y Y'` of schemes over `ℂ`, the two composites `X'(ℂ) → Y(ℂ)`
agree. -/
lemma mapFun_comp_of_isPullback (sq : IsPullback i' g f i) (x' : UnderlyingSpace ℂ X') :
    mapFun f (mapFun i' x') = mapFun i (mapFun g x') :=
  UnderlyingSpace.ext (by
    change (x'.toHom ≫ i') ≫ f = (x'.toHom ≫ g) ≫ i
    rw [Category.assoc, Category.assoc, sq.w])

end FibreSquare

/-- Equal morphisms of schemes induce equal maps `appLE U W` on sections. -/
lemma appLE_congr_hom {A B : Scheme.{0}} {φ ψ : A ⟶ B} (h : φ = ψ) {U : B.Opens} {W : A.Opens}
    (e : W ≤ φ ⁻¹ᵁ U) (e' : W ≤ ψ ⁻¹ᵁ U) :
    ConcreteCategory.hom (φ.appLE U W e) = ConcreteCategory.hom (ψ.appLE U W e') := by
  subst h
  rfl

/-- If `φ₁ ≫ φ₂ = ψ₁ ≫ ψ₂`, then the composites of the induced maps `appLE` on sections agree. -/
lemma appLE_appLE_eq {A B B' C : Scheme.{0}} {φ₁ : A ⟶ B} {φ₂ : B ⟶ C} {ψ₁ : A ⟶ B'}
    {ψ₂ : B' ⟶ C} (h : φ₁ ≫ φ₂ = ψ₁ ≫ ψ₂) {U : C.Opens} {V : B.Opens} {V' : B'.Opens}
    {W : A.Opens} (e₂ : V ≤ φ₂ ⁻¹ᵁ U) (e₁ : W ≤ φ₁ ⁻¹ᵁ V) (e₂' : V' ≤ ψ₂ ⁻¹ᵁ U)
    (e₁' : W ≤ ψ₁ ⁻¹ᵁ V') (c : Γ(C, U)) :
    φ₁.appLE V W e₁ (φ₂.appLE U V e₂ c) = ψ₁.appLE V' W e₁' (ψ₂.appLE U V' e₂' c) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]
  exact DFunLike.congr_fun (appLE_congr_hom h _ _) c

/-! ### Points of pull-back bundles -/

section PullbackPoint

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {B B' : Type*} [TopologicalSpace B]
  [TopologicalSpace B'] {Q : B → Type*} [∀ x, TopologicalSpace (Q x)]
  [TopologicalSpace (TotalSpace F Q)] (h : C(B', B))

/-- The point `(b, q)` of `h^* Q` over `b ∈ B'`, for `q ∈ Q` over `h(b)`. -/
def pullbackMk (b : B') (q : TotalSpace F Q) (hq : q.proj = h b) : TotalSpace F (h *ᵖ Q) :=
  ⟨b, (cast (congrArg Q hq) q.2 : Q (h b))⟩

/-- The image of the point `pullbackMk h b q hq` of `h^* Q` in `Q` is `q`. -/
lemma lift_pullbackMk (b : B') (q : TotalSpace F Q) (hq : q.proj = h b) :
    Pullback.lift h (pullbackMk h b q hq) = q := by
  obtain ⟨x, v⟩ := q
  change x = h b at hq
  subst hq
  rfl

/-- Two points of `h^* Q` with the same base point and the same image in `Q` are equal. -/
lemma pullback_totalSpace_ext {p₁ p₂ : TotalSpace F (h *ᵖ Q)} (h₁ : p₁.proj = p₂.proj)
    (h₂ : Pullback.lift h p₁ = Pullback.lift h p₂) : p₁ = p₂ := by
  obtain ⟨b, v⟩ := p₁
  obtain ⟨b', v'⟩ := p₂
  change b = b' at h₁
  subst h₁
  have h₃ : (TotalSpace.mk (h b) v : TotalSpace F Q) = TotalSpace.mk (h b) v' := h₂
  cases eq_of_heq (TotalSpace.mk.inj h₃).2
  rfl

end PullbackPoint

end MMP
