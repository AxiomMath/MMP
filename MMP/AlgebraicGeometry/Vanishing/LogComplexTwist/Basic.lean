module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Model

/-!
# Twists of the fractional logarithmic complex

Let `π : V ⟶ Spec ℂ` be smooth, `D = S + Supp B` a relative snc divisor, `B = Bn/N`, and
`𝒪_V(M)` a root of `𝒪_V(Bn)` through `N M = Bn + div ψ`. The complex
`C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)` with the connection `∇ = d - N⁻¹ dψ/ψ ∧` exists as soon as
`Bn ≥ 0` is supported on `D`: the bound `Bn < N` is used only for its degeneration at `E₁`.
In particular, for every `k ≥ 0`, the twist `C^•(-k Supp B)`, the complex of the same connection
on `𝒪_V(-M - k Supp B) · Ω^•_V(log D)(-S)`, is the fractional logarithmic complex of the datum
`(M + k Supp B, Bn + N k Supp B, ψ)`, whose residue along a component `E` of `Supp B` is
`Bn(E)/N + k`.

## Main definitions

* `MMP.LcBpf.IsTwistInclusion`: the inclusion of the twist, through the embeddings into forms.

## Main results

* `MMP.LcBpf.exists_isCModel_of_nonneg`: a model of `C^•` exists for every `Bn ≥ 0` supported
  on `D`.
* `MMP.LcBpf.exists_isCModel_twist`: a model of the twist `C^•(-k Supp B)` exists.
* `MMP.LcBpf.cU'_twist`: the open `V ∖ (D ∪ Supp M)` on which the forms live does not change
  under the twist.

## References

* [P. Deligne, L. Illusie,
  *Relèvements modulo p² et décomposition du complexe de de Rham*][DeligneIllusie1987]
* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.FourfoldProofs.FractionalLogComplexProof

variable (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]

/-- **The fractional logarithmic complex exists for every `Bn ≥ 0` supported on `D`.** With
`D = S + Supp Bn`, `N M = Bn + div ψ` and `u` the function `ψ` on `V ∖ (D ∪ Supp M)`, the
complex `C^•` of the connection `∇ = d - N⁻¹ du/u ∧` on `𝒪_V(-M) · Ω^•_V(log D)(-S)` has a
model. No upper bound on the coefficients of `Bn` is needed. -/
theorem exists_isCModel_of_nonneg [CompactSpace V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (hS : 0 ≤ S)
    (Bn : MMP.Mori.Divisor V) (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1) (N : ℕ)
    (hN : 0 < N) (hBn : ∀ E, 0 ≤ Bn E) (ψ : (MMP.Mori.RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ) (u : Γ(V, cU' D M))
    (hu : (MMP.Mori.toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ) :
    ∃ K F e ι, IsCModel n π D hD S M N u K F e ι := by
  classical
  have hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support := by
    intro E hE
    have hSE : 0 ≤ S E := Finsupp.le_def.1 hS E
    rw [Finsupp.mem_support_iff, hSB E, ite_eq_right hE]
    omega
  have hSD : ∀ E ∈ S.support, E ∈ D.support := by
    intro E hE
    have hSE : 0 ≤ S E := Finsupp.le_def.1 hS E
    rw [Finsupp.mem_support_iff] at hE ⊢
    rw [hSB E]
    split_ifs <;> omega
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  have hsm : MMP.Mori.IsSmoothScheme π := (MMP.Mori.isSmoothScheme_iff π).2 this
  have hMC : M.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm M
  -- `N` is invertible
  have hNW : ∀ W : V.Opens, IsUnit (N : Γ(V, W)) := fun W => by
    simpa only [map_natCast] using
      ((Nat.cast_ne_zero.2 hN.ne').isUnit : IsUnit (N : ℂ)).map
        ((V.presheaf.map (homOfLE le_top).op).hom.comp
          (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom))
  -- `u` is a unit
  have hunit : IsUnit u := by
    refine isUnit_of_ord_eq_zero u ψ hu fun E hE => ?_
    obtain ⟨y, hyE, hyU⟩ := hE
    have hM : M E = 0 := by
      by_contra h
      exact hyU (Or.inr (MMP.Mori.DivisorWithCoeffs.support_subset_supp h hyE))
    have hB0 : Bn E = 0 := by
      by_contra h
      exact hyU (Or.inl (MMP.Mori.DivisorWithCoeffs.support_subset_supp
        (Finsupp.mem_support_iff.1 (hBD E h)) hyE))
    have h := congrArg (fun F => F E) hψ
    simp only [Finsupp.smul_apply, Finsupp.add_apply, hM, hB0, smul_zero, zero_add] at h
    rw [← MMP.Mori.coeff_principalDivisor]
    exact h.symm
  have hNu : IsUnit ((N : Γ(V, cU' D M)) * u) := (hNW _).mul hunit
  have hcc : (↑hNu.unit⁻¹ : Γ(V, cU' D M)) * ((N : Γ(V, cU' D M)) * u) = 1 :=
    hNu.val_inv_mul
  have hst : NabStable n π D hD S M u ↑hNu.unit⁻¹ :=
    nabStable_of_genData n π D hD S M u _ hSD fun y =>
      exists_genData n π D hD M u _ hMC Bn N ψ hψ hu hcc hNW (by omega) hBn hBD y
  have hloc : LocMon n π D hD S M :=
    fun p W ω hω y hy => Cond.exists_monSet (hω := hω) (hy := hy)
  exact ⟨_, _, _, _, isCModel_cCx n π D hD S M N u _ hcc hst hloc
    (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one π D M N hcc)⟩

omit [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V] in
/-- **The twist does not move `V ∖ (D ∪ Supp M)`.** For `D = S + Supp Bn` with `S ≥ 0`, the
divisor `D - S = Supp Bn` is supported on `D`, so `D ∪ Supp (M + k (D - S)) = D ∪ Supp M`. -/
theorem cU'_twist (D S M Bn : MMP.Mori.Divisor V) (hS : 0 ≤ S)
    (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1) (k : ℤ) :
    cU' D (M + k • (D - S)) = cU' D M := by
  have hsub : (D - S).supp ≤ D.supp := by
    intro x hx
    obtain ⟨E, hE, hx⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mp hx
    refine MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, ?_, hx⟩
    have hSE : 0 ≤ S E := Finsupp.le_def.1 hS E
    have h := hSB E
    simp only [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply] at hE ⊢
    split_ifs at h <;> omega
  have hsm : (k • (D - S)).supp ≤ D.supp := by
    intro x hx
    obtain ⟨E, hE, hx⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mp hx
    refine hsub (MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, ?_, hx⟩)
    intro h0
    apply hE
    simp only [MMP.Mori.DivisorWithCoeffs.coeff_apply] at h0 ⊢
    rw [Finsupp.smul_apply, h0, smul_zero]
  have hle : M.supp ≤ (M + k • (D - S)).supp ⊔ D.supp := by
    have h := MMP.Mori.DivisorWithCoeffs.supp_add_le (M + k • (D - S)) (-(k • (D - S)))
    rw [add_neg_cancel_right, MMP.Mori.DivisorWithCoeffs.supp_neg] at h
    exact h.trans (sup_le_sup_left hsm _)
  have heq : D.supp ⊔ (M + k • (D - S)).supp = D.supp ⊔ M.supp := by
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · exact (MMP.Mori.DivisorWithCoeffs.supp_add_le _ _).trans
        (sup_le le_sup_right (hsm.trans le_sup_left))
    · exact hle.trans (sup_le le_sup_right le_sup_left)
  simp only [cU', heq]

/-- **The twist `C^•(-k Supp B)` is a fractional logarithmic complex.** For `k ≥ 0`, the complex
of the connection `∇ = d - N⁻¹ du/u ∧` on `𝒪_V(-M - k Supp Bn) · Ω^•_V(log D)(-S)` has a model:
it is `C^•` for the datum `(M + k Supp Bn, Bn + N k Supp Bn, ψ)`, with `Supp Bn = D - S`. -/
theorem exists_isCModel_twist [CompactSpace V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (hS : 0 ≤ S)
    (Bn : MMP.Mori.Divisor V) (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1) (N : ℕ)
    (hN : 0 < N) (hBn : ∀ E, 0 ≤ Bn E) (ψ : (MMP.Mori.RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ) (k : ℕ)
    (u : Γ(V, cU' D (M + (k : ℤ) • (D - S))))
    (hu : (MMP.Mori.toRationalFunctionsPresheaf V).app (op (cU' D (M + (k : ℤ) • (D - S)))) u =
      ratRes (cU' D (M + (k : ℤ) • (D - S))) ψ) :
    ∃ K F e ι, IsCModel n π D hD S (M + (k : ℤ) • (D - S)) N u K F e ι := by
  have hDS : ∀ E, (D - S) E = if Bn E = 0 then 0 else 1 := fun E => by
    rw [Finsupp.sub_apply, hSB E]
    ring
  refine exists_isCModel_of_nonneg n π D hD S _ hS (Bn + ((N * k : ℕ) : ℤ) • (D - S))
    (fun E => ?_) N hN (fun E => ?_) ψ ?_ u hu
  · rw [hSB E]
    have h1 := hBn E
    simp only [Finsupp.add_apply, Finsupp.smul_apply, hDS E, smul_eq_mul]
    by_cases h2 : Bn E = 0
    · simp [h2]
    · have h3 : Bn E + ((N * k : ℕ) : ℤ) * 1 ≠ 0 := by positivity
      rw [if_neg h2, if_neg h3]
  · have h1 := hBn E
    simp only [Finsupp.add_apply, Finsupp.smul_apply, hDS E, smul_eq_mul]
    split_ifs <;> positivity
  · rw [smul_add, hψ, smul_smul]
    push_cast
    abel

/-- **The inclusion of a twist, read on forms.** For divisors `M, M'` with
`V ∖ (D ∪ Supp M') = V ∖ (D ∪ Supp M)` (as for `M' = M + k (D - S)`, `MMP.LcBpf.cU'_twist`), a
model `K'` of `C^•` for `M'` and a model `K` for `M`, a morphism `φ : K' ⟶ K` is the inclusion if
it commutes with the embeddings into the forms on `U ∩ W ∩ U'`: `ι (φ x) = ι' x`, the two opens
`U ∩ W ∩ U'` being identified. -/
def IsTwistInclusion (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M)
    {K K' : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
    {F F' : ℕ → V.Modules}
    (e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p))
    (e' : ∀ p, K'.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F' p))
    (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W)))
    (ι' : ∀ (p : ℕ) (W : V.Opens), (F' p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M' W)))
    (φ : K' ⟶ K) : Prop :=
  ∀ (p : ℕ) (W : V.Opens) (x : (K'.X p).val.obj (op W)),
    ι p W ((e p).hom.val.app (op W) ((φ.f p).val.app (op W) x)) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.map
        (homOfLE (show OO D M W ≤ OO D M' W by simp [OO, hM])).op
        (ι' p W ((e' p).hom.val.app (op W) x))

end MMP.LcBpf
