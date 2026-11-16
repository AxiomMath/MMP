module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.PullbackMap.RationalExpansion
public import MMP.AlgebraicGeometry.Divisor.RationalFunctionGerm

/-!
# The quotient `g^N / ψ` at a point

Let `N M = Bn + div ψ` on a normal integral scheme `X` with `M` Cartier, `Bn ≥ 0` supported on the
relative simple normal crossing divisor `D`, and `u` the function `ψ` on `U' = X ∖ (D ∪ Supp M)`.
For a section `g` of `𝒪_X(-M)` near a point `x`, the rational function `g^N / ψ` lies in the local
ring `𝒪_{X,x}`, and in its maximal ideal when `x` lies on a component `E` with `Bn_E ≠ 0`: near
`x` the section `g` is `h g₀` for the local generator `g₀` of
`MMP.FourfoldProofs.FractionalLogComplexProof.exists_generator_factorization`, with
`g₀^N = u · v · ∏ τₖ^{Bn(jₖ)}`, `v` a unit and `τₖ` local equations of the components `jₖ` of `D`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_stalk_mul_eq_pow`: the quotient at a point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

variable {X : Scheme.{u}}

/-- A section of the ideal sheaf `I` over an affine open `W` has germ in the maximal ideal at every
point of `W` lying in the support of `I`. -/
theorem germ_mem_maximalIdeal_of_mem_ideal {I : X.IdealSheafData} {W : X.affineOpens}
    {x : X} (hx : x ∈ (W : X.Opens)) (hI : x ∈ I.support) {a : Γ(X, W)} (ha : a ∈ I.ideal W) :
    X.presheaf.germ (W : X.Opens) x hx a ∈ maximalIdeal (X.presheaf.stalk x) := by
  have h := notMem_basicOpen_of_mem_support hx hI ha
  rw [Scheme.mem_basicOpen _ _ _ hx] at h
  exact (mem_maximalIdeal _).2 h

/-- **The quotient `g^N / ψ` at a point.** For a section `g` of `𝒪_X(-M)` over `W₃ ∩ U'`, `x ∈ W₃`,
there is `h ∈ 𝒪_{X,x}` with `h · ψ = g^N` in `k(X)`, in the maximal ideal if `x` lies on a prime
divisor `F` with `Bn_F ≠ 0`. -/
theorem exists_stalk_mul_eq_pow [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (n : ℕ) {T : Scheme.{u}} (f : X ⟶ T) [SmoothOfRelativeDimension n f]
    (D : MMP.Mori.Divisor X) (hD : D.IsRelativeSNC n f) (M : MMP.Mori.Divisor X)
    (uu : Γ(X, cU' D M)) (hMC : M.IsCartier) (Bn : MMP.Mori.Divisor X) (N : ℕ)
    (ψ : (MMP.Mori.RationalFunctions X)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ)
    (hu : (MMP.Mori.toRationalFunctionsPresheaf X).app (op (cU' D M)) uu = ratRes (cU' D M) ψ)
    (hBn : ∀ E, 0 ≤ Bn E) (hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support) {x : X} {W₃ : X.Opens}
    (hx : x ∈ W₃) (g₁ : Γ(X, W₃ ⊓ cU' D M)) (hg₁ : DivCond (D := D) (M := M) W₃ g₁) :
    haveI := nonempty_inf_cU' D M (W := W₃) ⟨⟨x, hx⟩⟩
    ∃ h : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField h *
        MMP.Mori.rationalFunctionsEquivFunctionField X ψ = X.germToFunctionField _ g₁ ^ N ∧
      ∀ F : MMP.Mori.PrimeDivisor X, x ∈ F.support → Bn F ≠ 0 →
        h ∈ maximalIdeal (X.presheaf.stalk x) := by
  classical
  have := nonempty_inf_cU' D M (W := W₃) ⟨⟨x, hx⟩⟩
  obtain ⟨W₂, hxW₂, r, τ, j, v, g₀, -, -, hτ, hDW₂, -, -, hgen, hpow⟩ :=
    exists_generator_factorization n f D hD M uu hMC Bn N ψ hψ hu hBn hBD x
  set W₄ : X.Opens := W₃ ⊓ (W₂ : X.Opens)
  have h4 : W₄ ≤ W₂ := inf_le_right
  have hxW₄ : x ∈ W₄ := ⟨hx, hxW₂⟩
  have : Nonempty W₄ := ⟨⟨x, hxW₄⟩⟩
  have : Nonempty (W₂ : X.Opens) := ⟨⟨x, hxW₂⟩⟩
  have : Nonempty (W₄ ⊓ cU' D M : X.Opens) := nonempty_inf_cU' D M ⟨⟨x, hxW₄⟩⟩
  have : Nonempty ((W₂ : X.Opens) ⊓ cU' D M : X.Opens) := nonempty_inf_cU' D M ⟨⟨x, hxW₂⟩⟩
  have : Nonempty (cU' D M) :=
    ‹Nonempty ((W₂ : X.Opens) ⊓ cU' D M : X.Opens)›.map fun z => ⟨z.1, z.2.2⟩
  have hres : W₄ ⊓ cU' D M ≤ W₃ ⊓ cU' D M := inf_le_inf_right _ inf_le_left
  obtain ⟨hh, hhg⟩ := hgen W₄ h4 (X.presheaf.map (homOfLE hres).op g₁)
    (hg₁.restrict D M inf_le_left)
  set P : Γ(X, (W₂ : X.Opens)) := v * ∏ k, τ k ^ (Bn (j k)).toNat with hP
  set a : Γ(X, W₄) := hh ^ N * X.presheaf.map (homOfLE h4).op P with ha
  refine ⟨X.presheaf.germ W₄ x hxW₄ a, ?_, fun F hxF hF => ?_⟩
  · have E0 : X.germToFunctionField (W₃ ⊓ cU' D M) g₁ =
        X.germToFunctionField W₄ hh * X.germToFunctionField ((W₂ : X.Opens) ⊓ cU' D M) g₀ := by
      simpa only [map_mul, germToFunctionField_map] using
        congrArg (X.germToFunctionField (W₄ ⊓ cU' D M)) hhg
    have e2 := congrArg (X.germToFunctionField ((W₂ : X.Opens) ⊓ cU' D M)) hpow
    simp only [map_mul, map_pow, germToFunctionField_map] at e2
    calc algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W₄ x hxW₄ a) *
          MMP.Mori.rationalFunctionsEquivFunctionField X ψ =
        X.germToFunctionField W₄ hh ^ N * X.germToFunctionField (W₂ : X.Opens) P *
          X.germToFunctionField (cU' D M) uu := by
          rw [Scheme.algebraMap_germ_eq_germToFunctionField, ha, map_mul, map_pow,
            germToFunctionField_map,
            rationalFunctionsEquivFunctionField_eq_germ (ψ : MMP.Mori.RationalFunctions X) uu hu]
      _ = (X.germToFunctionField W₄ hh *
          X.germToFunctionField ((W₂ : X.Opens) ⊓ cU' D M) g₀) ^ N := by
        rw [mul_pow, e2]
        ring
      _ = X.germToFunctionField (W₃ ⊓ cU' D M) g₁ ^ N := congrArg (· ^ N) E0.symm
  · obtain ⟨k, rfl⟩ := exists_eq_of_mem_chart (n := r) τ le_rfl j hτ hDW₂
      (hBD F hF) hxW₂ hxF
    have hτk : X.presheaf.germ (W₂ : X.Opens) x hxW₂ (τ k) ∈ maximalIdeal (X.presheaf.stalk x) :=
      germ_mem_maximalIdeal_of_mem_ideal hxW₂ hxF
        (by rw [hτ k]; exact Ideal.mem_span_singleton_self _)
    have hb : 0 < (Bn (j k)).toNat := by have := hBn (j k); omega
    have hPm : X.presheaf.germ (W₂ : X.Opens) x hxW₂ P ∈ maximalIdeal (X.presheaf.stalk x) := by
      rw [hP, map_mul, map_prod]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _
        (Finset.mem_univ k)) ?_)
      simpa only [map_pow] using Ideal.pow_mem_of_mem _ hτk _ hb
    rw [ha, map_mul, TopCat.Presheaf.germ_res_apply]
    exact Ideal.mul_mem_left _ _ hPm

end MMP.FourfoldProofs.FractionalLogComplexProof
