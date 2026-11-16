module

public import MMP.AlgebraicTopology.OrientationClass.Point

/-!
# Real bases attached to complex bases (Fulton, §19.1)

For a complex basis `c = (c₁, …, c_r)` of a complex vector space `V`, the real basis
`c₁, i c₁, …, c_r, i c_r` (`MMP.complexRealBasis c`) defines the orientation of `V`
given by its complex structure: an injective complex linear map `L : V → W` between spaces of the
same dimension has positive real determinant for any two such bases. `complexOrientationBasisOf V`
is the case `c = Module.finBasis ℂ V`.

## Main definitions

* `MMP.complexRealBasis`: the real basis `c₁, i c₁, …, c_r, i c_r` of a complex basis `c`.

## Main results

* `MMP.complexRealBasis_det_pos`: an injective complex linear map has positive real determinant
  for such bases.
* `MMP.prod_complexRealBasis`: products of complex-oriented bases.
-/

@[expose] public noncomputable section

namespace MMP

open ThomClass

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {r : ℕ}

/-- The real basis `c₁, i c₁, …, c_r, i c_r` of a complex vector space with complex basis `c`. -/
def complexRealBasis (c : Module.Basis (Fin r) ℂ V) : Module.Basis (Fin (2 * r)) ℝ V :=
  (complexOrientationBasis r).map (c.equivFun.symm.restrictScalars ℝ)

/-- `complexOrientationBasisOf V` is `complexRealBasis` of the basis `Module.finBasis ℂ V`. -/
lemma complexOrientationBasisOf_eq_complexRealBasis [FiniteDimensional ℂ V] :
    complexOrientationBasisOf V = complexRealBasis (Module.finBasis ℂ V) :=
  rfl

/-- The `(2j + b)`-th vector of `complexRealBasis c` is `c_j` for `b = 0` and `i c_j` for
`b = 1`. -/
lemma complexRealBasis_apply (c : Module.Basis (Fin r) ℂ V) (j : Fin r) (b : Fin 2) :
    complexRealBasis c (finCongr (Nat.mul_comm r 2) (finProdFinEquiv (j, b))) =
      Complex.basisOneI b • c j := by
  rw [complexRealBasis, Module.Basis.map_apply, complexOrientationBasis_apply]
  simp

/-- **Complex linear isomorphisms preserve complex orientations**: for complex bases `c₁` of `V`
and `c₂` of `W` of the same length and an injective complex linear `L : V → W`, the real
determinant of `L` for the bases `complexRealBasis c₁` and `complexRealBasis c₂` is positive. -/
theorem complexRealBasis_det_pos (c₁ : Module.Basis (Fin r) ℂ V)
    (c₂ : Module.Basis (Fin r) ℂ W) {L : V →ₗ[ℂ] W} (hL : Function.Injective L) :
    0 < (complexRealBasis c₂).det ((L.restrictScalars ℝ) ∘ complexRealBasis c₁) := by
  set A₁ := c₁.equivFun
  set A₂ := c₂.equivFun
  have hcomp : ⇑(A₂.symm.restrictScalars ℝ).symm ∘ ((L.restrictScalars ℝ) ∘ complexRealBasis c₁) =
      ⇑(((A₂ : W →ₗ[ℂ] _) ∘ₗ L ∘ₗ (A₁.symm : (Fin r → ℂ) →ₗ[ℂ] V)).restrictScalars ℝ) ∘
        complexOrientationBasis r := by
    funext i
    simp [complexRealBasis, A₁, A₂]
  rw [complexRealBasis, Module.Basis.det_map, hcomp, Module.Basis.det_comp,
    Module.Basis.det_self, mul_one, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_pos]
  have hinj : Function.Injective
      ((A₂ : W →ₗ[ℂ] (Fin r → ℂ)) ∘ₗ L ∘ₗ (A₁.symm : (Fin r → ℂ) →ₗ[ℂ] V)) :=
    A₂.injective.comp (hL.comp A₁.symm.injective)
  exact (LinearEquiv.isUnit_det' (LinearEquiv.ofInjectiveEndo _ hinj)).ne_zero

/-- **The product of complex-oriented bases is complex oriented**: for complex bases `c₁` of `V`
and `c₂` of `W`, the product (in the order `V` then `W`) of the real bases `complexRealBasis c₁`
and `complexRealBasis c₂` is `complexRealBasis` of the product complex basis. -/
theorem prod_complexRealBasis {m k : ℕ} (c₁ : Module.Basis (Fin m) ℂ V)
    (c₂ : Module.Basis (Fin k) ℂ W) :
    ((complexRealBasis c₁).prod (complexRealBasis c₂)).reindex finSumFinEquiv =
      (complexRealBasis ((c₁.prod c₂).reindex finSumFinEquiv)).reindex
        (finCongr (by ring : 2 * (m + k) = 2 * m + 2 * k)) := by
  refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
  obtain ⟨⟨j, β⟩, rfl⟩ : ∃ p : Fin (m + k) × Fin 2,
      finCongr (by ring : 2 * (m + k) = 2 * m + 2 * k)
        (finCongr (Nat.mul_comm (m + k) 2) (finProdFinEquiv p)) = i := by
    refine ⟨finProdFinEquiv.symm ((finCongr (Nat.mul_comm (m + k) 2)).symm
      ((finCongr (by ring : 2 * (m + k) = 2 * m + 2 * k)).symm i)), ?_⟩
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [Module.Basis.reindex_apply (complexRealBasis _), Equiv.symm_apply_apply,
    complexRealBasis_apply, Module.Basis.reindex_apply]
  induction j using Fin.addCases with
  | left j₁ =>
    have hi : (finCongr (by ring : 2 * (m + k) = 2 * m + 2 * k)
        (finCongr (Nat.mul_comm (m + k) 2) (finProdFinEquiv (Fin.castAdd k j₁, β)))) =
        finSumFinEquiv (Sum.inl (finCongr (Nat.mul_comm m 2) (finProdFinEquiv (j₁, β)))) :=
      Fin.ext (by simp [finProdFinEquiv])
    rw [hi, Equiv.symm_apply_apply, Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
      complexRealBasis_apply, Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
      Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply]
    ext <;> simp
  | right j₂ =>
    have hi : (finCongr (by ring : 2 * (m + k) = 2 * m + 2 * k)
        (finCongr (Nat.mul_comm (m + k) 2) (finProdFinEquiv (Fin.natAdd m j₂, β)))) =
        finSumFinEquiv (Sum.inr (finCongr (Nat.mul_comm k 2) (finProdFinEquiv (j₂, β)))) :=
      Fin.ext (by simp [finProdFinEquiv]; ring)
    rw [hi, Equiv.symm_apply_apply, Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
      complexRealBasis_apply, Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd,
      Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply]
    ext <;> simp

end MMP
