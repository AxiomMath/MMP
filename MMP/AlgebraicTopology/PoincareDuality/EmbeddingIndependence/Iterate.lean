module

public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Embedded
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderCocycleDuality

/-!
# Iterated euclidean suspensions

For closed `A ⊆ ℝ^m` the `K`-fold euclidean suspension
`σ_K : H^j(ℝ^m, ℝ^m - A) → H^{j+K}(ℝ^{m+K}, ℝ^{m+K} - A × 0)` commutes with the imbedded duality
maps (`embeddedDualityMap_iterSuspension`), and, for `A` locally contractible, it is bijective,
because the duality maps are (`bijective_embeddedDualityMap`, Alexander duality
`bijective_dualityMap_of_isFundamentalClass`).

## Main definitions

* `cohomologyCongrDegree`: The identification `H^j(M, M - A) = H^{j'}(M, M - A)` for `j = j'`.
* `iterSuspensionSet`: The set `A × 0 ⊆ ℝ^{m+K}` for `A ⊆ ℝ^m`.
* `iterSuspensionHomeomorph`: The homeomorphism `X ≅ A × 0` induced by `ψ : X ≅ A`.
* `iterSuspension`: The `K`-fold euclidean suspension
  `H^j(ℝ^m, ℝ^m - A) → H^{j+K}(ℝ^{m+K}, ℝ^{m+K} - A × 0)`.

## Main results

* `embeddedDualityMap_iterSuspension`: The imbedded duality map of `A × 0` at `σ_K c` equals that
  of `A` at `c`.
* `bijective_embeddedDualityMap`: The imbedded duality map of a closed `A ⊆ ℝ^N` with arbitrarily
  small proper neighbourhood deformations is bijective.
* `bijective_iterSuspension`: The iterated suspension is bijective for `A` homeomorphic to a
  locally contractible space.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology MMP.BorelMooreCross MMP.BorelMooreCap
  MMP.FundamentalClass

universe u

namespace MMP

namespace borelMooreHomology

variable (R : Type u) [CommRing R]

/-- The identification `H^j(M, M - A) = H^{j'}(M, M - A)` for `j = j'`. -/
abbrev cohomologyCongrDegree (M : TopCat.{u}) (A : Set M) {j j' : ℤ} (h : j = j') :
    cohomologyWithSupports R (ModuleCat.of R R) M A j ⟶
      cohomologyWithSupports R (ModuleCat.of R R) M A j' :=
  eqToHom (by rw [h])

/-- The imbedded duality map commutes with the degree identification `cohomologyCongrDegree`. -/
lemma embeddedDualityMap_cohomologyCongrDegree {M : TopCat.{u}} {A : Set M} (hA : IsClosed A)
    (hAd : HasProperNeighbourhoodDeformations A) {X : TopCat.{u}} (ψ : X ≃ₜ A) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) M n) {j j' : ℤ} (hj : j = j') (k : ℤ)
    (h : j' + k = n) (h' : j + k = n) (c : cohomologyWithSupports R (ModuleCat.of R R) M A j) :
    embeddedDualityMap R hA hAd ψ μ j' k h ((cohomologyCongrDegree R M A hj).hom c) =
      embeddedDualityMap R hA hAd ψ μ j k h' c := by
  subst hj
  rfl

section iterate

variable {m : ℕ}

/-- `A × 0 ⊆ ℝ^{m+K}` for `A ⊆ ℝ^m`. -/
def iterSuspensionSet (A : Set (Fin m → ULift.{u} ℝ)) :
    (K : ℕ) → Set (Fin (m + K) → ULift.{u} ℝ)
  | 0 => A
  | K + 1 => suspensionSet (iterSuspensionSet A K)

@[simp]
lemma iterSuspensionSet_zero (A : Set (Fin m → ULift.{u} ℝ)) : iterSuspensionSet A 0 = A := rfl

@[simp]
lemma iterSuspensionSet_succ (A : Set (Fin m → ULift.{u} ℝ)) (K : ℕ) :
    iterSuspensionSet A (K + 1) = suspensionSet (iterSuspensionSet A K) := rfl

/-- `X ≅ A ≅ A × 0 ⊆ ℝ^{m+K}` for `ψ : X ≅ A`. -/
def iterSuspensionHomeomorph {A : Set (Fin m → ULift.{u} ℝ)} {X : TopCat.{u}} (ψ : X ≃ₜ A) :
    (K : ℕ) → X ≃ₜ iterSuspensionSet A K
  | 0 => ψ
  | K + 1 => suspensionHomeomorph (iterSuspensionHomeomorph ψ K)

/-- The `i`-th coordinate of `iterSuspensionHomeomorph ψ K x ∈ ℝ^{m+K}` is the `i`-th coordinate
of `ψ x` for `i < m`, and `0` otherwise. -/
lemma coe_iterSuspensionHomeomorph_apply {A : Set (Fin m → ULift.{u} ℝ)} {X : TopCat.{u}}
    (ψ : X ≃ₜ A) (K : ℕ) (x : X) (i : Fin (m + K)) :
    (iterSuspensionHomeomorph ψ K x : Fin (m + K) → ULift.{u} ℝ) i =
      if hi : (i : ℕ) < m then (ψ x : Fin m → ULift.{u} ℝ) ⟨i, hi⟩ else 0 := by
  induction K with
  | zero => simp only [show (i : ℕ) < m from i.2, ↓reduceDIte]; rfl
  | succ K ih =>
    revert i
    change ∀ i : Fin (m + K + 1), (Fin.snoc (α := fun _ ↦ ULift.{u} ℝ)
      (iterSuspensionHomeomorph ψ K x : Fin (m + K) → ULift.{u} ℝ) 0 : Fin (m + K + 1) → _) i =
        if hi : (i : ℕ) < m then (ψ x : Fin m → ULift.{u} ℝ) ⟨i, hi⟩ else 0
    refine Fin.lastCases ?_ (fun l ↦ ?_)
    · simp
    · rw [Fin.snoc_castSucc, ih]
      rfl

/-- For closed `A ⊆ ℝ^m`, the set `A × 0 ⊆ ℝ^{m+K}` is closed. -/
theorem isClosed_iterSuspensionSet {A : Set (Fin m → ULift.{u} ℝ)} (hA : IsClosed A) :
    ∀ K, IsClosed (iterSuspensionSet A K)
  | 0 => hA
  | K + 1 => (((isClosed_iterSuspensionSet hA K).preimage (prFst _ _).hom.continuous).inter
      (isClosed_singleton.preimage (prSnd _ _).hom.continuous)).preimage
        (snocHomeomorph (m + K)).symm.continuous

/-- The `K`-fold euclidean suspension `H^j(ℝ^m, ℝ^m - A) → H^{j+K}(ℝ^{m+K}, ℝ^{m+K} - A × 0)`. -/
def iterSuspension {A : Set (Fin m → ULift.{u} ℝ)} (hA : IsClosed A) (j : ℤ) :
    (K : ℕ) →
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin m → ULift.{u} ℝ)) A j →ₗ[R]
        cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin (m + K) → ULift.{u} ℝ))
          (iterSuspensionSet A K) (j + K)
  | 0 => (cohomologyCongrDegree R (TopCat.of (Fin m → ULift.{u} ℝ)) A
      (by simp : j = j + ((0 : ℕ) : ℤ))).hom
  | K + 1 => (cohomologyCongrDegree R (TopCat.of (Fin (m + K + 1) → ULift.{u} ℝ))
        (suspensionSet (iterSuspensionSet A K))
        (by push_cast; ring : j + (K : ℕ) + (1 : ℕ) = j + (K + 1 : ℕ))).hom ∘ₗ
      euclideanSuspension R (isClosed_iterSuspensionSet hA K) (pointDual R) (j + K) ∘ₗ
        iterSuspension hA j K

/-- **Iterated suspension and the duality maps.** For a locally contractible `X`, a
homeomorphism `ψ : X ≅ A ⊆ ℝ^m` with `A` closed, and `c ∈ H^j(ℝ^m, ℝ^m - A)`: the imbedded
duality map of `A × 0 ⊆ ℝ^{m+K}` at `σ_K c` is that of `A` at `c`. -/
theorem embeddedDualityMap_iterSuspension {A : Set (Fin m → ULift.{u} ℝ)} (hA : IsClosed A)
    (hAd : HasProperNeighbourhoodDeformations A) {X : TopCat.{u}} (ψ : X ≃ₜ A)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id)
    (K : ℕ) (hKd : HasProperNeighbourhoodDeformations (iterSuspensionSet A K)) (j k : ℤ)
    (h : j + k = m) (hK : j + K + k = (m + K : ℕ))
    (c : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin m → ULift.{u} ℝ)) A j) :
    embeddedDualityMap R (isClosed_iterSuspensionSet hA K) hKd (iterSuspensionHomeomorph ψ K)
        (euclideanClass R (m + K)) (j + K) k hK (iterSuspension R hA j K c) =
      embeddedDualityMap R hA hAd ψ (euclideanClass R m) j k h c := by
  induction K with
  | zero =>
    change embeddedDualityMap R hA hKd ψ (euclideanClass R m) (j + ((0 : ℕ) : ℤ)) k hK
      ((cohomologyCongrDegree R (TopCat.of (Fin m → ULift.{u} ℝ)) A
        (by simp : j = j + ((0 : ℕ) : ℤ))).hom c) = _
    rw [embeddedDualityMap_cohomologyCongrDegree R hA hKd ψ (euclideanClass R m)
      (by simp : j = j + ((0 : ℕ) : ℤ)) k hK h c]
  | succ K ih =>
    have hc := hasBasis_contractible_of_homeomorph (iterSuspensionHomeomorph ψ K) hXc
    have hBd : HasProperNeighbourhoodDeformations (iterSuspensionSet A K) :=
      hasProperNeighbourhoodDeformations_of_finiteDimensional
        (V := Fin (m + K) → ULift.{u} ℝ) (isClosed_iterSuspensionSet hA K)
        hc
    have hK' : j + K + (1 : ℕ) + k = (m + K + 1 : ℕ) := by push_cast; omega
    change embeddedDualityMap R (isClosed_iterSuspensionSet hA (K + 1)) hKd
        (suspensionHomeomorph (iterSuspensionHomeomorph ψ K)) (euclideanClass R (m + K + 1))
        (j + (K + 1 : ℕ)) k hK ((cohomologyCongrDegree R
          (TopCat.of (Fin (m + K + 1) → ULift.{u} ℝ)) (suspensionSet (iterSuspensionSet A K))
          (by push_cast; ring : j + (K : ℕ) + (1 : ℕ) = j + (K + 1 : ℕ))).hom
          (euclideanSuspension R (isClosed_iterSuspensionSet hA K) (pointDual R) (j + K)
            (iterSuspension R hA j K c))) = _
    rw [embeddedDualityMap_cohomologyCongrDegree R (isClosed_iterSuspensionSet hA (K + 1)) hKd
        (suspensionHomeomorph (iterSuspensionHomeomorph ψ K)) (euclideanClass R (m + K + 1))
        (by push_cast; ring : j + (K : ℕ) + (1 : ℕ) = j + (K + 1 : ℕ)) k hK hK',
      embeddedDualityMap_euclideanSuspension R (m + K) (isClosed_iterSuspensionSet hA K)
        hc hBd (isClosed_iterSuspensionSet hA (K + 1)) hKd
        (iterSuspensionHomeomorph ψ K) (j + K) k (by push_cast; omega) hK']
    exact ih hBd (by push_cast; omega)

/-- Push-forward along a homeomorphism is bijective. -/
lemma bijective_pushforward_homeomorph {Y Y' : TopCat.{u}} (φ : Y ≃ₜ Y') (i : ℤ) :
    Function.Bijective
      (pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(Y, Y'))) φ.isProperMap i).hom :=
  bijective_pushforward_of_comp_eq_id R _ (TopCat.ofHom (φ.symm : C(Y', Y))) _ φ.symm.isProperMap
    (by ext x; exact φ.symm_apply_apply x) (by ext x; exact φ.apply_symm_apply x) i

/-- **Alexander duality for the imbedded duality map in `ℝ^N`.** For closed `A ⊆ ℝ^N` with
arbitrarily small proper neighbourhood deformations and `ψ : X ≅ A`,
`H^j(ℝ^N, ℝ^N - A) → H_k X` is bijective (`j + k = N`). -/
theorem bijective_embeddedDualityMap {N : ℕ} {A : Set (Fin N → ULift.{u} ℝ)} (hA : IsClosed A)
    (hAd : HasProperNeighbourhoodDeformations A) {X : TopCat.{u}} (ψ : X ≃ₜ A) (j k : ℤ)
    (h : j + k = N) :
    Function.Bijective (embeddedDualityMap R hA hAd ψ (euclideanClass R N) j k h) := by
  obtain rfl : j = N - k := by omega
  have hd : Function.Bijective (dualityMap R hA hAd (euclideanClass R N) k) :=
    bijective_dualityMap_of_isFundamentalClass (liftEuclideanBasis N) (euclideanClass R N)
      (isFundamentalClass_euclideanClass R N) hA hAd k
  have hp := bijective_pushforward_homeomorph R (Y := TopCat.of A) (Y' := X) ψ.symm k
  refine ⟨fun c c' hcc' ↦ hd.1 (hp.1 hcc'), fun y ↦ ?_⟩
  obtain ⟨z, hz⟩ := hp.2 y
  obtain ⟨c, hc⟩ := hd.2 z
  refine ⟨c, ?_⟩
  rw [embeddedDualityMap_eq_dualityMap, hc]
  exact hz

/-- **The iterated suspension is bijective** for closed `A ⊆ ℝ^m` homeomorphic to a locally
contractible `X`. -/
theorem bijective_iterSuspension {A : Set (Fin m → ULift.{u} ℝ)} (hA : IsClosed A)
    {X : TopCat.{u}} (ψ : X ≃ₜ A)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id)
    (K : ℕ) (j : ℤ) : Function.Bijective (iterSuspension R hA j K) := by
  have hAd := hasProperNeighbourhoodDeformations_of_finiteDimensional hA
    (hasBasis_contractible_of_homeomorph ψ hXc)
  have hKd := hasProperNeighbourhoodDeformations_of_finiteDimensional
    (isClosed_iterSuspensionSet hA K)
    (hasBasis_contractible_of_homeomorph (iterSuspensionHomeomorph ψ K) hXc)
  have h1 := bijective_embeddedDualityMap R hA hAd ψ j (m - j) (by ring)
  have h2 := bijective_embeddedDualityMap R (isClosed_iterSuspensionSet hA K) hKd
    (iterSuspensionHomeomorph ψ K) (j + K) (m - j) (by push_cast; ring)
  have he : (embeddedDualityMap R (isClosed_iterSuspensionSet hA K) hKd
      (iterSuspensionHomeomorph ψ K) (euclideanClass R (m + K)) (j + K) (m - j)
      (by push_cast; ring)) ∘ (iterSuspension R hA j K) =
      embeddedDualityMap R hA hAd ψ (euclideanClass R m) j (m - j) (by ring) :=
    funext fun c ↦ embeddedDualityMap_iterSuspension R hA hAd ψ hXc K hKd j (m - j) (by ring)
      (by push_cast; ring) c
  exact (Function.Bijective.of_comp_iff' h2 _).1 (he ▸ h1)

end iterate

end borelMooreHomology

end MMP
