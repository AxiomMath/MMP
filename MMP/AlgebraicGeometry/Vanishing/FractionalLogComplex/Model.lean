module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Retract.Defs

/-!
# The model of the fractional logarithmic complex

Let `π : V ⟶ Spec ℂ` carry the data of the fractional logarithmic complex
`C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)`, let `u` be a function on `U' = V ∖ (D ∪ Supp M)` and `c` a
function with `c · N u = 1`. If the connection `∇ = d - c du ∧` preserves `C^•`, the complex
`MMP.FourfoldProofs.FractionalLogComplexProof.cCx` of the sheaves `C^p` with differential `∇`, with
its terms embedded into the forms on `U'` by `MMP.FourfoldProofs.FractionalLogComplexProof.tr`, is a
model of `C^•` (`MMP.FourfoldProofs.FractionalLogComplexProof.IsCModel`): `tr` is injective,
`𝒪_V`-linear and compatible with restrictions, its image is `𝒪_V(-M) · Ω^p_V(log D)(-S)`, and it
carries `∇` to `d - (N u)⁻¹ du ∧`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one`: `dc ∧ du = 0`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.isCModel_cCx`: the model.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_modelData`: `c = (N u)⁻¹`, and `∇` preserves
  `C^•`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

variable (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
  (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V)

/-- **`dc ∧ du = 0`** for `c · N u = 1`, on every `U ∩ W ∩ U'`. -/
theorem δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one {X T : Scheme.{u}} (f : X ⟶ T)
    (D M : MMP.Mori.Divisor X) (N : ℕ) {uu cc : Γ(X, cU' D M)}
    (hcc : cc * ((N : Γ(X, cU' D M)) * uu) = 1) (W : X.Opens) :
    δ ((cU D).ι ≫ f) (OO D M W) (resU W cc) * δ ((cU D).ι ≫ f) (OO D M W) (resU W uu) = 0 := by
  let φ : Γ(X, cU' D M) →+* Γ((cU D).toScheme, OO D M W) :=
    ((cU D).ι.app (W ⊓ cU' D M)).hom.comp (X.presheaf.map (homOfLE inf_le_right).op).hom
  have h1 : resU W cc * ((N : Γ((cU D).toScheme, OO D M W)) * resU W uu) = 1 := by
    have := congrArg φ hcc
    rwa [map_mul, map_mul, map_natCast, map_one] at this
  exact δ_mul_δ_of_mul_natCast_mul_eq_one N h1

/-- **The model of `C^•`.** -/
theorem isCModel_cCx (N : ℕ) (uu cc : Γ(V, cU' D M))
    (hcc : cc * ((N : Γ(V, cU' D M)) * uu) = 1) (hst : NabStable n π D hD S M uu cc)
    (hloc : LocMon n π D hD S M)
    (hcu : ∀ W : V.Opens, δ ((cU D).ι ≫ π) (OO D M W) (resU W cc) *
      δ ((cU D).ι ≫ π) (OO D M W) (resU W uu) = 0) :
    IsCModel n π D hD S M N uu (cCx n π D hD S M uu cc hst hloc hcu) (cMod n π D hD S M)
      (fun _ => Iso.refl _) (fun p W x => tr π D M (p : ℤ) W x.1) := by
  refine ⟨fun p W x y h => Subtype.ext (tr_injective π D M (p : ℤ) W h),
    fun p W x y => tr_add π D M (p : ℤ) x.1 y.1, fun p W r x => ?_, fun p W W' h x => ?_,
    fun p W ω => ?_, fun p W x => ?_⟩
  · change (TB ((cU D).ι ≫ π)).incl (p : ℤ) (tr π D M (p : ℤ) W (r • x.1)) = _
    rw [tr_smul]
    exact (sm_mul_incl _ _ _).symm
  · exact tr_restrict π D M (p : ℤ) h x.1
  · constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hω
      refine ⟨⟨trInv π D M (p : ℤ) W ω, ?_⟩, tr_trInv π D M (p : ℤ) W ω⟩
      change Cond n π D hD S M p W (tr π D M (p : ℤ) W (trInv π D M (p : ℤ) W ω))
      rw [tr_trInv]
      exact hω
  · refine Eq.trans ?_ (nsmul_mul_incl_nab π D M uu cc N hcc p W (tr π D M (p : ℤ) W x.1))
    rw [cCx_d]
    exact congrArg (fun y => N • ((TB ((cU D).ι ≫ π)).structureMap (op (OO D M W)) (resU W uu) *
      (TB ((cU D).ι ≫ π)).incl ((p + 1 : ℕ) : ℤ) y)) (tr_nabA π D M uu cc p W _)

/-- **The data of the model**: for `u` on `U'` restricting to `ψ`, there is `c` with
`c · (N u) = 1`, and the connection `∇ = d - c du ∧` preserves `C^•`. -/
theorem exists_modelData [CompactSpace V] (hS : 0 ≤ S) (Bn : MMP.Mori.Divisor V)
    (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1) (N : ℕ) (hN : 0 < N)
    (hB : ∀ E, 0 ≤ Bn E) (ψ : (MMP.Mori.RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ) (u : Γ(V, cU' D M))
    (hu : (MMP.Mori.toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ) :
    ∃ cc : Γ(V, cU' D M), cc * ((N : Γ(V, cU' D M)) * u) = 1 ∧
      NabStable n π D hD S M u cc := by
  classical
  have hS' : ∀ E, 0 ≤ S E := Finsupp.le_def.1 hS
  have hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support := by
    intro E hE
    have hSE := hS' E
    rw [Finsupp.mem_support_iff, hSB E, ite_eq_right hE]
    omega
  have hSD : ∀ E ∈ S.support, E ∈ D.support := by
    intro E hE
    have hSE := hS' E
    rw [Finsupp.mem_support_iff] at hE
    rw [Finsupp.mem_support_iff, hSB E]
    split_ifs <;> omega
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  have hMC : M.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme ((MMP.Mori.isSmoothScheme_iff π).2 this) M
  -- `N` is invertible
  have hNW : ∀ W : V.Opens, IsUnit (N : Γ(V, W)) := by
    intro W
    let φ : ℂ →+* Γ(V, W) := (V.presheaf.map (homOfLE le_top).op).hom.comp
      (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)
    simpa only [map_natCast] using ((Nat.cast_ne_zero.2 hN.ne' : (N : ℂ) ≠ 0).isUnit.map φ)
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
  exact ⟨↑hNu.unit⁻¹, hNu.val_inv_mul, nabStable_of_genData n π D hD S M u _ hSD fun y =>
    exists_genData n π D hD M u _ hMC Bn N ψ hψ hu hNu.val_inv_mul hNW (by omega)
      hB hBD y⟩

end MMP.FourfoldProofs.FractionalLogComplexProof
