module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Residue.LocalGenerators
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts

/-!
# The residue of the connection of the model of `C^•`

Let `π : V ⟶ Spec ℂ` be smooth, `D = S + Supp Bn` a relative simple normal crossing divisor with
`0 ≤ Bn` and `N M = Bn + div ψ`, and let `u = ψ` on `U' = V ∖ (D ∪ Supp M)` and `c = (N u)⁻¹`.
The connection of the model `MMP.FourfoldProofs.FractionalLogComplexProof.cCx` of
`C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)` is `∇ = d - c du ∧`. Along a component `E` of `Supp Bn`
its residue is `Bn(E)/N`: on an affine open `W` meeting no other component of `D`, with local
equation `t` of `E`, the form `t (N ∇a - Bn(E) a dt/t)` is regular for every section `a` of
`C^0`.

The computation is local. Near a point of `W`, `𝒪_V(-M)` has a generator `g₀` with
`g₀^N = u v t^b`, `b = Bn(E)`, and `v` invertible off `D ∪ Supp M`, and `a = g₀ H` with `H`
regular. Then `∇ g₀ = g₀ N⁻¹ (dv/v + b dt/t)`, and
`t (N ∇a - b a dt/t) = t (g₀ N dH + g₀ H v⁻¹ dv)`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.nsmul_incl_nab_sub_zsmul_eq`: the local identity
  `t (N ∇(g₀ H) - b g₀ H dt/t) = t (g₀ N dH + g₀ H v⁻¹ dv)`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.residueSpec`: the residue of `∇` along `E` is
  `Bn(E)/N`, as `MMP.FourfoldProofs.FractionalLogComplexProof.ResidueSpec`.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de
  de Rham*][DeligneIllusie1987]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

/-- **The residue identity.** If `ω = g H` on `U ∩ W' ∩ U'` with `g^N = u v t^b`, `t` a unit and
`v` of inverse `vi` there, then `t (N ∇ω - b ω dt/t) = t (g N dH + g H vi dv)`. -/
theorem nsmul_incl_nab_sub_zsmul_eq {X T : Scheme.{u}} (f : X ⟶ T) (D M : MMP.Mori.Divisor X)
    (uu cc : Γ(X, cU' D M)) (N : ℕ) (hN : N ≠ 0) (hcc : cc * ((N : Γ(X, cU' D M)) * uu) = 1)
    {W W' : X.Opens} (h : W' ≤ W)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((0 : ℕ) : ℤ)).val.obj (op (OO D M W)))
    {gg tt : Γ((cU D).toScheme, OO D M W')} {H v vi : Γ(X, W')} (b : ℕ)
    (hH : (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) (rO f (D := D) (M := M) ((0 : ℕ) : ℤ) h ω) =
      sm ((cU D).ι ≫ f) (OO D M W') (gg * resO D M W' H))
    (htu : IsUnit tt) (hvv : resO D M W' vi * resO D M W' v = 1)
    (hrel : gg ^ N = resU W' uu * resO D M W' v * tt ^ b) :
    sm ((cU D).ι ≫ f) (OO D M W') tt * (N • (TB ((cU D).ι ≫ f)).incl ((0 + 1 : ℕ) : ℤ)
        (rO f (D := D) (M := M) ((0 + 1 : ℕ) : ℤ) h
          (nab ((cU D).ι ≫ f) 0 (θW f D M uu cc W) ω))) -
      (b : ℤ) • ((TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) (rO f (D := D) (M := M) ((0 : ℕ) : ℤ) h ω) *
        δ ((cU D).ι ≫ f) (OO D M W') tt) =
    sm ((cU D).ι ≫ f) (OO D M W') tt *
      (sm ((cU D).ι ≫ f) (OO D M W') (gg * resO D M W' (N : Γ(X, W'))) *
          δ ((cU D).ι ≫ f) (OO D M W') (resO D M W' H) +
        sm ((cU D).ι ≫ f) (OO D M W') (gg * resO D M W' (H * vi)) *
          δ ((cU D).ι ≫ f) (OO D M W') (resO D M W' v)) := by
  -- `c · N u = 1` on `U ∩ W' ∩ U'`, `c = cc` and `u = uu` there
  have h1 : resU W' cc * ((N : Γ((cU D).toScheme, OO D M W')) * resU W' uu) = 1 := by
    have := congrArg (((cU D).ι.app (W' ⊓ cU' D M)).hom.comp
      (X.presheaf.map (homOfLE inf_le_right).op).hom) hcc
    rwa [map_mul, map_mul, map_natCast, map_one] at this
  -- `∇ ω` restricted to `W'`
  have hrO : rO f (D := D) (M := M) ((0 + 1 : ℕ) : ℤ) h
      (nab ((cU D).ι ≫ f) 0 (θW f D M uu cc W) ω) =
      nab ((cU D).ι ≫ f) 0 (θW f D M uu cc W') (rO f (D := D) (M := M) ((0 : ℕ) : ℤ) h ω) :=
    (nab_map _ 0 _ _).trans
      (congrArg (fun θ => nab ((cU D).ι ≫ f) 0 θ _) (θW_restrict f D M uu cc h))
  rw [hrO, incl_nab, hH, Δ_zero_sm, incl_θW, natCast_zsmul]
  obtain ⟨s, hs⟩ := htu.exists_left_inv
  have hu' : (N * resU W' cc) * resU W' uu = 1 := by linear_combination h1
  have hNi : (resU W' cc * resU W' uu) * (N : Γ((cU D).toScheme, OO D M W')) = 1 := by
    linear_combination h1
  have hc : resU W' cc = (resU W' cc * resU W' uu) * (N * resU W' cc) := by
    linear_combination (-resU W' cc) * h1
  have hβ : s ^ b * tt ^ b = 1 := by rw [← mul_pow, hs, one_pow]
  have hgu : IsUnit gg := by
    rw [← isUnit_pow_iff hN, hrel]
    exact ((IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hu')).mul
      (IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hvv))).mul (htu.pow b)
  have key := dlog_twist_identity (g := (cU D).ι ≫ f) (O := OO D M W') N hu' hvv hβ
    hgu.unit.inv_mul hNi hc hrel
  rw [dl_pow hs] at key
  let ρ : Γ(X, W') →+* Γ((cU D).toScheme, OO D M W') :=
    ((cU D).ι.app (W' ⊓ cU' D M)).hom.comp (X.presheaf.map (homOfLE inf_le_left).op).hom
  rw [show resO D M W' (N : Γ(X, W')) = N from map_natCast ρ N,
    show resO D M W' (H * vi) = resO D M W' H * resO D M W' vi from map_mul ρ H vi]
  exact residue_identity N b hs hNi key

/-- The residue identity, in the form of the residue clause: `ω₁ = ∇ω₀` on `W`, both restricted to
`W' ⊆ W`, and the right side a sum of two terms `g₀ fᵢ dhᵢ`. -/
theorem nsmul_incl_nab_sub_zsmul_eq_sum {X T : Scheme.{u}} (f : X ⟶ T) (D M : MMP.Mori.Divisor X)
    (uu cc : Γ(X, cU' D M)) (N : ℕ) (hN : N ≠ 0) (hcc : cc * ((N : Γ(X, cU' D M)) * uu) = 1)
    {W W' : X.Opens} (h : W' ≤ W)
    (ω₀ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((0 : ℕ) : ℤ)).val.obj (op (OO D M W)))
    (ω₁ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((1 : ℕ) : ℤ)).val.obj (op (OO D M W)))
    (hω₁ : ω₁ = nab ((cU D).ι ≫ f) 0 (θW f D M uu cc W) ω₀)
    (g₀ : Γ(X, W' ⊓ cU' D M)) (H v vi t : Γ(X, W')) (z : ℤ) (b : ℕ) (hz : z = b)
    (hH : (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) (rO f (D := D) (M := M) ((0 : ℕ) : ℤ) h ω₀) =
      sm ((cU D).ι ≫ f) (OO D M W') (((cU D).ι.app (W' ⊓ cU' D M)).hom g₀ * resO D M W' H))
    (htu : IsUnit (resO D M W' t)) (hvv : resO D M W' vi * resO D M W' v = 1)
    (hrel : ((cU D).ι.app (W' ⊓ cU' D M)).hom g₀ ^ N =
      resU W' uu * resO D M W' v * resO D M W' t ^ b) :
    sm ((cU D).ι ≫ f) (OO D M W') (resO D M W' t) *
        (N • (TB ((cU D).ι ≫ f)).incl ((1 : ℕ) : ℤ)
          (rO f (D := D) (M := M) ((1 : ℕ) : ℤ) h ω₁)) -
      z • ((TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) (rO f (D := D) (M := M) ((0 : ℕ) : ℤ) h ω₀) *
        δ ((cU D).ι ≫ f) (OO D M W') (resO D M W' t)) =
    sm ((cU D).ι ≫ f) (OO D M W') (resO D M W' t) *
      ∑ i : Fin 2, sm ((cU D).ι ≫ f) (OO D M W')
          (((cU D).ι.app (W' ⊓ cU' D M)).hom ((fun _ => g₀) i) *
            resO D M W' (![(N : Γ(X, W')), H * vi] i)) *
        δ ((cU D).ι ≫ f) (OO D M W') (resO D M W' (![H, v] i)) := by
  subst hω₁ hz
  rw [Fin.sum_univ_two]
  exact nsmul_incl_nab_sub_zsmul_eq f D M uu cc N hN hcc h ω₀ b hH htu hvv hrel

/-- **The residue of `∇` along a component `E` of `Supp Bn` is `Bn(E)/N`**, for the model `cCx`
of `C^•`. -/
theorem residueSpec (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S Bn : MMP.Mori.Divisor V) (hS : 0 ≤ S)
    (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1)
    (N : ℕ) (hN : 0 < N) (hBn : ∀ E, 0 ≤ Bn E)
    (M : MMP.Mori.Divisor V) (ψ : (MMP.Mori.RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ)
    (uu cc : Γ(V, cU' D M))
    (hu : (MMP.Mori.toRationalFunctionsPresheaf V).app (op (D.supp ⊔ M.supp).compl) uu =
      (MMP.Mori.rationalFunctionsPresheaf V).map (homOfLE le_top).op
        ((MMP.Mori.rationalFunctionsPresheafTopEquiv V).symm ψ))
    (hcc : cc * ((N : Γ(V, cU' D M)) * uu) = 1)
    (hst : NabStable n π D hD S M uu cc) (hloc : LocMon n π D hD S M)
    (hcu : ∀ W : V.Opens, δ ((cU D).ι ≫ π) (OO D M W) (resU W cc) *
      δ ((cU D).ι ≫ π) (OO D M W) (resU W uu) = 0) :
    ResidueSpec n π D hD S Bn M N uu cc hst hloc hcu := by
  classical
  have hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support := by
    intro E hE
    have hSE : 0 ≤ S E := Finsupp.le_def.1 hS E
    rw [Finsupp.mem_support_iff, hSB E, ite_eq_right hE]
    omega
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  have hMC : M.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme ((MMP.Mori.isSmoothScheme_iff π).2 this) M
  intro E hE0 W t ht hmiss x y hy
  obtain ⟨W₂, hy₂, g₀, hg₀div, hgen, hchart⟩ := exists_residue_chart n π D hD M uu hMC Bn N ψ
    hψ hu hBn hBD (hBD E hE0) hmiss y
  have hω : Cond n π D hD S M 0 W (tr π D M ((0 : ℕ) : ℤ) W x.1) := x.2
  obtain ⟨W', h, h₂, hy', H, hH⟩ :=
    exists_incl_zero_eq_sm_mul n π D hD S M hω hy hy₂ g₀ hgen
  have ht' : E.idealSheaf.ideal W' = Ideal.span {V.presheaf.map (homOfLE h).op t} := by
    have e := E.idealSheaf.map_ideal h
    rw [ht, Ideal.map_span, Set.image_singleton] at e
    exact e.symm
  obtain ⟨v, vi, hvv, htu, hrel⟩ := hchart W' h₂ h _ ht'
  have hd : tr π D M ((1 : ℕ) : ℤ) W
      (((Iso.refl ((cCx n π D hD S M uu cc hst hloc hcu).X 1)).hom.val.app (op (W : V.Opens))
        (((cCx n π D hD S M uu cc hst hloc hcu).d 0 1).val.app (op (W : V.Opens)) x)).1) =
      nab ((cU D).ι ≫ π) 0 (θW π D M uu cc W) (tr π D M ((0 : ℕ) : ℤ) W x.1) := by
    rw [cCx_d n π D hD S M uu cc hst hloc hcu 0]
    exact tr_nabA π D M uu cc 0 W x.1
  have key := nsmul_incl_nab_sub_zsmul_eq_sum π D M uu cc N (by omega) hcc h _ _ hd _ H v vi _
    (Bn E) (Bn E).toNat (Int.toNat_of_nonneg (hBn E)).symm hH htu hvv hrel
  exact ⟨W', h, hy', 2, fun _ => V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₂)).op g₀,
    ![N, H * vi], ![H, v], fun _ => hg₀div.restrict D M h₂, key⟩

end MMP.FourfoldProofs.FractionalLogComplexProof
