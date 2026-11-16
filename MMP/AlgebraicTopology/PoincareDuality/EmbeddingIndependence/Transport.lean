module

public import MMP.AlgebraicTopology.PoincareDuality.AlexanderGeneral
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.BorelMoore.ProperHomotopy
public import MMP.Topology.Algebra.Matrix.DetPosPath

/-!
# Transport of the duality map along maps of the ambient space

For two closed imbeddings of a space `X` into euclidean spaces `ℝ^N` and `ℝ^{N'}`, the canonical
isomorphism `H^{N-i}(ℝ^N, ℝ^N - X) ≅ H^{N'-i}(ℝ^{N'}, ℝ^{N'} - X)` is a composite of suspensions
and of pull-backs along homeomorphisms of euclidean spaces which are properly homotopic to the
identity: shears `z ↦ z + F z` and linear automorphisms of positive determinant. This file shows
that the duality map `c ↦ c ∩ μ` is compatible with such pull-backs.

## Main definitions

* `shearHomeomorph`: The shear `z ↦ z + F z`, for `F` with `F (z + s • F z) = F z`.
* `shearHomotopy`: The homotopy `(t, z) ↦ z + (1 - t) • F z` from the shear to the identity.
* `matrixPathHomotopy`: The homotopy `(t, z) ↦ γ (1 - t) *ᵥ z` attached to a path of matrices `γ`
  from `1` to `M`.

## Main results

* `pushforward_dualityMap_pullback`: The duality map commutes with pull-back along a proper map
  `f`, read through the restriction `f⁻¹ A → A`.
* `isProperMap_of_inverse_family`: A continuous family of homeomorphisms with continuous inverse
  family, over a compact parameter space, is proper.
* `pushforward_apply_eq_self_of_properHomotopy`: A proper self-map properly homotopic to the
  identity fixes every Borel–Moore class.
* `isProperMap_shearHomotopy`: The shear homotopy is proper.
* `isProperMap_matrixPathHomotopy`: The homotopy along a path of invertible matrices is proper.
* `pushforward_shearHomeomorph_apply`: A shear fixes every Borel–Moore class.
* `pushforward_mulVec_apply_of_det_pos`: A linear automorphism of `ℝ^m` of positive determinant
  fixes every Borel–Moore class.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Set Matrix

universe u

namespace MMP

namespace borelMooreHomology

open BorelMooreCross

variable (R : Type u) [CommRing R]

/-- **The duality map and pull-back.** For a proper map `f : M → M'`, a closed `A ⊆ M'` and
`c ∈ H^{n-k}(M', M' - A)`: `(f|)_* ((f^* c) ∩ μ) = c ∩ f_* μ` in `H_k A`, where
`f| : f⁻¹ A → A` is the restriction. -/
theorem pushforward_dualityMap_pullback {M M' : TopCat.{u}} (f : M ⟶ M') (hf : IsProperMap f)
    {A : Set M'} (hA : IsClosed A) (hAd : HasProperNeighbourhoodDeformations A)
    (hA'd : HasProperNeighbourhoodDeformations (f ⁻¹' A)) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) M n) (k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) M' A (n - k)) :
    (pushforward R (ModuleCat.of R R) (TopCat.ofHom (f.hom.restrictPreimage A))
        (hf.restrictPreimage A) k).hom
      (dualityMap R (hA.preimage f.hom.continuous) hA'd μ k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f A (n - k)).hom c)) =
      dualityMap R hA hAd ((pushforward R (ModuleCat.of R R) f hf n).hom μ) k c := by
  have key : ∀ (j : ℤ) (h : j = k)
      (x : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (f ⁻¹' A)) j),
      (pushforward R (ModuleCat.of R R) (TopCat.ofHom (f.hom.restrictPreimage A))
          (hf.restrictPreimage A) k).hom (congrDegree R _ h x) =
        congrDegree R (TopCat.of A) h ((pushforward R (ModuleCat.of R R)
          (TopCat.ofHom (f.hom.restrictPreimage A)) (hf.restrictPreimage A) j).hom x) := by
    rintro _ rfl x
    rfl
  rw [dualityMap_apply, dualityMap_apply, key,
    ← pushforward_restrictPreimage_capProductSupportPullback R f hf hA hAd hA'd]
  rfl

/-- A proper self-map properly homotopic to the identity fixes every Borel–Moore class. -/
theorem pushforward_apply_eq_self_of_properHomotopy {Y : TopCat.{u}} {f : Y ⟶ Y}
    (hf : IsProperMap f) (H : TopCat.Homotopy f (𝟙 Y)) (hH : IsProperMap H) (k : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) f hf k).hom a = a := by
  rw [pushforward_eq_of_properHomotopy R (ModuleCat.of R R) hf (by simp)
    H hH k, pushforward_id]
  rfl

section family

variable {E : Type*} [TopologicalSpace E]

/-- A continuous family `G t` of homeomorphisms of `E`, indexed by a compact space `K`, with
continuous inverse family, is a proper map `K × E → E`. -/
theorem isProperMap_of_inverse_family {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (G Ginv : K × E → E) (hG : Continuous G) (hGi : Continuous Ginv)
    (h₁ : ∀ t z, Ginv (t, G (t, z)) = z) (h₂ : ∀ t z, G (t, Ginv (t, z)) = z) :
    IsProperMap G := by
  let Ψ : K × E ≃ₜ K × E :=
    { toFun := fun p ↦ (p.1, G p)
      invFun := fun p ↦ (p.1, Ginv p)
      left_inv := fun p ↦ Prod.ext rfl (h₁ p.1 p.2)
      right_inv := fun p ↦ Prod.ext rfl (h₂ p.1 p.2)
      continuous_toFun := continuous_fst.prodMk hG
      continuous_invFun := continuous_fst.prodMk hGi }
  exact isProperMap_snd_of_compactSpace.comp Ψ.isProperMap

end family

section shear

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] (F : C(E, E)) (hF : ∀ z (s : ℝ), F (z + s • F z) = F z)

/-- The shear `z ↦ z + F z`, for `F` constant along its own values. -/
@[simps]
def shearHomeomorph : E ≃ₜ E where
  toFun z := z + F z
  invFun z := z - F z
  left_inv z := by
    have := hF z 1
    simp only [one_smul] at this
    simp [this]
  right_inv z := by
    have := hF z (-1)
    simp only [neg_smul, one_smul, ← sub_eq_add_neg] at this
    simp [this]
  continuous_toFun := continuous_id.add F.continuous
  continuous_invFun := continuous_id.sub F.continuous

/-- The homotopy `(t, z) ↦ z + (1 - t) • F z` from the shear to the identity. -/
def shearHomotopy :
    TopCat.Homotopy (TopCat.ofHom (shearHomeomorph F hF : C(E, E))) (𝟙 (TopCat.of E)) where
  toFun p := p.2 + ((1 : ℝ) - p.1) • F p.2
  continuous_toFun := continuous_snd.add
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst))).smul
      (F.continuous.comp continuous_snd))
  map_zero_left z := by simp
  map_one_left z := by simp

/-- The homotopy `(t, z) ↦ z + (1 - t) • F z` is a proper map `[0, 1] × E → E`. -/
theorem isProperMap_shearHomotopy : IsProperMap (shearHomotopy F hF) :=
  isProperMap_of_inverse_family _ (fun p ↦ p.2 - ((1 : ℝ) - p.1) • F p.2)
    (shearHomotopy F hF).continuous
    (continuous_snd.sub
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst))).smul
        (F.continuous.comp continuous_snd)))
    (fun t z ↦ by
      change z + ((1 : ℝ) - t) • F z - ((1 : ℝ) - t) • F (z + ((1 : ℝ) - t) • F z) = z
      rw [hF]; abel)
    (fun t z ↦ by
      change z - ((1 : ℝ) - t) • F z + ((1 : ℝ) - t) • F (z - ((1 : ℝ) - t) • F z) = z
      have := hF z (-((1 : ℝ) - t))
      rw [neg_smul, ← sub_eq_add_neg] at this
      rw [this]; abel)

/-- A shear fixes every Borel–Moore class. -/
theorem pushforward_shearHomeomorph_apply (k : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of E) k) :
    (pushforward R (ModuleCat.of R R) (TopCat.ofHom (shearHomeomorph F hF : C(E, E)))
      (shearHomeomorph F hF).isProperMap k).hom a = a :=
  pushforward_apply_eq_self_of_properHomotopy R _ (shearHomotopy F hF)
    (isProperMap_shearHomotopy F hF) k a

end shear

section linear

variable {m : ℕ}

/-- A path of real matrices `γ` from `1` to `M` gives the homotopy `(t, z) ↦ γ (1 - t) *ᵥ z` from
`z ↦ M z` to the identity. -/
def matrixPathHomotopy {M : Matrix (Fin m) (Fin m) ℝ} (γ : Path (1 : Matrix (Fin m) (Fin m) ℝ) M) :
    TopCat.Homotopy (TopCat.ofHom (⟨fun z ↦ M *ᵥ z, by fun_prop⟩ : C(Fin m → ℝ, Fin m → ℝ)))
      (𝟙 (TopCat.of (Fin m → ℝ))) where
  toFun p := γ (unitInterval.symm p.1) *ᵥ p.2
  continuous_toFun := by
    have hγ : Continuous fun p : unitInterval × (Fin m → ℝ) ↦ γ (unitInterval.symm p.1) :=
      γ.continuous.comp (unitInterval.continuous_symm.comp continuous_fst)
    exact Continuous.matrix_mulVec hγ continuous_snd
  map_zero_left z := by simp
  map_one_left z := by simp

/-- For a path `γ` of invertible matrices, the homotopy `(t, z) ↦ γ (1 - t) *ᵥ z` is a
proper map `[0, 1] × ℝ^m → ℝ^m`. -/
theorem isProperMap_matrixPathHomotopy {M : Matrix (Fin m) (Fin m) ℝ}
    (γ : Path (1 : Matrix (Fin m) (Fin m) ℝ) M) (hγ : ∀ t, (γ t).det ≠ 0) :
    IsProperMap (matrixPathHomotopy γ) := by
  have hγc : Continuous fun p : unitInterval × (Fin m → ℝ) ↦ γ (unitInterval.symm p.1) :=
    γ.continuous.comp (unitInterval.continuous_symm.comp continuous_fst)
  have hinv : Continuous fun p : unitInterval × (Fin m → ℝ) ↦ (γ (unitInterval.symm p.1))⁻¹ := by
    have : (fun p : unitInterval × (Fin m → ℝ) ↦ (γ (unitInterval.symm p.1))⁻¹) =
        fun p ↦ ((γ (unitInterval.symm p.1)).det)⁻¹ • (γ (unitInterval.symm p.1)).adjugate := by
      funext p
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    exact ((hγc.matrix_det).inv₀ fun p ↦ hγ _).smul hγc.matrix_adjugate
  refine isProperMap_of_inverse_family _ (fun p ↦ (γ (unitInterval.symm p.1))⁻¹ *ᵥ p.2)
    (matrixPathHomotopy γ).continuous (Continuous.matrix_mulVec hinv continuous_snd)
    (fun t z ↦ ?_) (fun t z ↦ ?_)
  · change (γ (unitInterval.symm t))⁻¹ *ᵥ (γ (unitInterval.symm t) *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hγ _).isUnit, Matrix.one_mulVec]
  · change γ (unitInterval.symm t) *ᵥ ((γ (unitInterval.symm t))⁻¹ *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hγ _).isUnit, Matrix.one_mulVec]

/-- **A linear automorphism of positive determinant fixes every Borel–Moore class of `ℝ^m`.** -/
theorem pushforward_mulVec_apply_of_det_pos (R : Type) [CommRing R]
    {M : Matrix (Fin m) (Fin m) ℝ} (hM : 0 < M.det)
    (hf : IsProperMap (fun z : Fin m → ℝ ↦ M *ᵥ z)) (k : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (Fin m → ℝ)) k) :
    (pushforward R (ModuleCat.of R R)
      (TopCat.ofHom (⟨fun z ↦ M *ᵥ z, by fun_prop⟩ : C(Fin m → ℝ, Fin m → ℝ))) hf k).hom a = a := by
  have h := MMP.MatrixDetPos.joinedIn_one_of_det_pos hM
  exact pushforward_apply_eq_self_of_properHomotopy R _ (matrixPathHomotopy h.somePath)
    (isProperMap_matrixPathHomotopy _ fun t ↦ (h.somePath_mem t).ne') k a

end linear

end borelMooreHomology

end MMP
