module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.ChartGenerators

/-!
# Local data of the twist inclusion near a point

Let `π : V ⟶ Spec ℂ` be smooth, `D = Supp Bn` a relative simple normal crossing divisor, `N M =
Bn + div ψ`, `E` a component of `D` with `Bn(E) ≠ 0` and `M' = M + E`. Near every point of `V`
there are an affine open `W` inside a chart of `D`, a generator `g₀` of `𝒪_V(-M)` and a generator
`g₁ = g₀ m` of `𝒪_V(-M')` on every open of `W`; near a point of `E`, `m = w t` with `w` a unit and
`t` an equation of `E`, and the connection form of `∇` has residue `λ = Bn(E)/N ≠ 0` along `E`;
off `E`, `m` is a unit.

## Main definitions

* `MMP.LcBpf.TwistChartForms.LocalData`: the local data near a point.

## Main results

* `MMP.LcBpf.TwistChartForms.nonempty_localData`: the local data exist near every point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.Mori MMP.FourfoldProofs.FractionalLogComplexProof

namespace TwistChartForms

open MMP.Mori.Divisor.LogSpreadingProof.G1 (SNCChart nonempty_sncChart)

variable (d : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension d π] [IsLocallyNoetherian V] [IsNormal V]
  (D : Divisor V) (M M' : Divisor V) (hM : cU' D M' = cU' D M) (N : ℕ) (u : Γ(V, cU' D M))
  (E : MMP.Mori.PrimeDivisor V)

/-- **Local data of the twist inclusion near a point `pt`**, on an affine open inside `W₀`. -/
structure LocalData (pt : V) (W₀ : V.Opens) where
  /-- The affine open. -/
  W : V.affineOpens
  /-- The affine open lies inside `W₀`. -/
  hW₀ : (W : V.Opens) ≤ W₀
  /-- The point `pt` lies in the affine open. -/
  hpt : pt ∈ (W : V.Opens)
  /-- A chart of `D` at `pt`. -/
  c : SNCChart d π D pt
  /-- The affine open lies inside the chart's open `c.W`. -/
  hWc : (W : V.Opens) ≤ c.W
  /-- The generator of `𝒪_V(-M)`. -/
  g₀ : Γ(V, (W : V.Opens) ⊓ cU' D M)
  /-- `g₀` satisfies the divisor condition `DivCond` for `M` on `W`. -/
  div₀ : DivCond (D := D) (M := M) (W : V.Opens) g₀
  /-- `g₀` generates: every section satisfying `DivCond` for `M` on an open `W₃ ≤ W` is a
  multiple of the restriction of `g₀`. -/
  gen₀ : ∀ (W₃ : V.Opens) (h₃ : W₃ ≤ W) (g : Γ(V, W₃ ⊓ cU' D M)),
    DivCond (D := D) (M := M) W₃ g → ∃ h : Γ(V, W₃),
      g = V.presheaf.map (homOfLE inf_le_left).op h *
        V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g₀
  /-- The image of `g₀` on `cU D` is a unit. -/
  unit₀ : IsUnit ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g₀)
  /-- The generator of `𝒪_V(-M')`. -/
  g₁ : Γ(V, (W : V.Opens) ⊓ cU' D M')
  /-- `g₁` satisfies the divisor condition `DivCond` for `M'` on `W`. -/
  div₁ : DivCond (D := D) (M := M') (W : V.Opens) g₁
  /-- `g₁` generates: every section satisfying `DivCond` for `M'` on an open `W₃ ≤ W` is a
  multiple of the restriction of `g₁`. -/
  gen₁ : ∀ (W₃ : V.Opens) (h₃ : W₃ ≤ W) (g : Γ(V, W₃ ⊓ cU' D M')),
    DivCond (D := D) (M := M') W₃ g → ∃ h : Γ(V, W₃),
      g = V.presheaf.map (homOfLE inf_le_left).op h *
        V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M') h₃)).op g₁
  /-- The image of `g₁` on `cU D` is a unit. -/
  unit₁ : IsUnit ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M') g₁)
  /-- The ratio `g₁ / g₀`. -/
  m : Γ(V, W)
  /-- `g₁ = g₀ * m` on `W ⊓ cU' D M`. -/
  rel : V.presheaf.map (homOfLE (inf_le_inf_left (W : V.Opens) hM.ge)).op g₁ =
    g₀ * V.presheaf.map (homOfLE inf_le_left).op m
  /-- Near a point of `E`, `m = w * t` with `w` a unit and `t` the chart equation of `E`, and
  the connection form of `g₀` has an invertible residue along `E`. -/
  onE : pt ∈ E.support → ∃ (i₀ : Fin c.r) (w : Γ(V, W)), c.j i₀ = E ∧ IsUnit w ∧
    m = w * tW c hWc (Fin.castLE c.hr i₀) ∧
    ∃ (ξ : (TB ((cU D).ι ≫ π)).Total (op (OO D M W))) (cO : Γ((cU D).toScheme, OO D M W)),
      cO * ((N : Γ((cU D).toScheme, OO D M W)) * resU W u) = 1 ∧
      δ ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g₀) -
          sm ((cU D).ι ≫ π) (OO D M W) cO * δ ((cU D).ι ≫ π) (OO D M W) (resU W u) *
            sm ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g₀) =
        sm ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g₀) * ξ ∧
      ∃ lam lamInv : Γ(V, W), lamInv * lam = 1 ∧
        (letI := chartAlgebra (f := π) (D := D) M (W := W);
          (∀ (q : ℕ) (z : (TB ((cU D).ι ≫ π)).Total (op (OO D M W))),
            Δ ((cU D).ι ≫ π) (OO D M W) q (lamInv • z) =
              lamInv • Δ ((cU D).ι ≫ π) (OO D M W) q z) ∧
          ResForm (θO c M hWc) (Fin.castLE c.hr i₀) (tW c hWc (Fin.castLE c.hr i₀)) lam ξ)
  /-- Away from `E`, `m` is a unit. -/
  offE : pt ∉ E.support → IsUnit m

omit [SmoothOfRelativeDimension d π] [IsLocallyNoetherian V] [IsNormal V] in
include π in
/-- For a scheme `V` over `Spec ℂ`, a nonzero natural number is a unit in `Γ(V, W)` for every
open `W`. -/
theorem isUnit_natCast_sections (m : ℕ) (hm : m ≠ 0) (W : V.Opens) : IsUnit (m : Γ(V, W)) := by
  let φ : ℂ →+* Γ(V, W) := (V.presheaf.map (homOfLE le_top).op).hom.comp
    (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)
  simpa only [map_natCast] using ((Nat.cast_ne_zero.2 hm : (m : ℂ) ≠ 0).isUnit.map φ)

variable {d π D M M' N u E}

/-- A generator property of `g₀` on `W₂` restricts to every open `W ≤ W₂`. -/
theorem exists_eq_mul_map_of_le {W W₂ : V.Opens} (hW : W ≤ W₂) {g₀ : Γ(V, W₂ ⊓ cU' D M)}
    (hgen : ∀ (W₃ : V.Opens) (h₃ : W₃ ≤ W₂) (g : Γ(V, W₃ ⊓ cU' D M)),
      DivCond (D := D) (M := M) W₃ g → ∃ h : Γ(V, W₃),
        g = V.presheaf.map (homOfLE inf_le_left).op h *
          V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g₀)
    (W₃ : V.Opens) (h₃ : W₃ ≤ W) (g : Γ(V, W₃ ⊓ cU' D M))
    (hg : DivCond (D := D) (M := M) W₃ g) : ∃ h : Γ(V, W₃),
      g = V.presheaf.map (homOfLE inf_le_left).op h *
        V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op
          (V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW)).op g₀) := by
  obtain ⟨h, hh⟩ := hgen W₃ (h₃.trans hW) g hg
  exact ⟨h, hh.trans (congrArg (_ * ·) (presheaf_map_map _ _ _ _).symm)⟩

omit [SmoothOfRelativeDimension d π] [IsLocallyNoetherian V] [IsNormal V] in
/-- On an affine open `W` inside a chart of `D`, the ideal of a chart component is generated by
its chart equation. -/
theorem ideal_eq_span_tW {pt : V} (c : SNCChart d π D pt) {W : V.affineOpens}
    (hWc : (W : V.Opens) ≤ c.W) (i₀ : Fin c.r) :
    (c.j i₀).idealSheaf.ideal W = Ideal.span {tW c hWc (Fin.castLE c.hr i₀)} := by
  rw [← (c.j i₀).idealSheaf.map_ideal hWc, (c.hjD i₀).2.2, Ideal.map_span, Set.image_singleton]
  rfl

/-- If `N M = Bn + div ψ` with `Supp Bn ⊆ Supp D` and `u` restricts to `ψ` on `cU' D M`, then `u`
is a unit. -/
theorem isUnit_of_smul_eq_add_principalDivisor [IsIntegral V] [CompactSpace V] {Bn : Divisor V}
    {ψ : (RationalFunctions V)ˣ} (hBD : ∀ E', Bn E' ≠ 0 → E' ∈ D.support)
    (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (hu : (toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ) :
    IsUnit u := by
  refine isUnit_of_ord_eq_zero u ψ hu fun P hP => ?_
  obtain ⟨y, hyP, hyU⟩ := hP
  have hMP : M P = 0 := by
    by_contra h
    exact hyU (Or.inr (MMP.Mori.DivisorWithCoeffs.support_subset_supp h hyP))
  have hB0 : Bn P = 0 := by
    by_contra h
    exact hyU (Or.inl (MMP.Mori.DivisorWithCoeffs.support_subset_supp
      (Finsupp.mem_support_iff.1 (hBD P h)) hyP))
  have h := congrArg (fun F => F P) hψ
  simp only [Finsupp.smul_apply, Finsupp.add_apply, hMP, hB0, smul_zero, zero_add] at h
  rw [← MMP.Mori.coeff_principalDivisor]
  exact h.symm

omit [SmoothOfRelativeDimension d π] in
open Classical in
/-- Let `φ` be a rational function whose divisor on an affine open `W` inside a chart of `D` is
`E`. Then `φ` is the restriction of a section `m₀` on `W`; near a point of `E`, `m₀ = w t` with
`w` a unit and `t` the chart equation of `E`, and off `E`, `m₀` is a unit. -/
theorem exists_eq_mul_tW_of_ord [IsIntegral V] [CompactSpace V] {pt : V}
    (c : SNCChart d π D pt) {W : V.affineOpens} (hWc : (W : V.Opens) ≤ c.W) (hE : E ∈ D.support)
    {φ : (RationalFunctions V)ˣ}
    (hord : ∀ P : MMP.Mori.PrimeDivisor V, (P.support ∩ (W : V.Opens)).Nonempty →
      P.ord φ = if P = E then 1 else 0)
    (hoff : pt ∉ E.support → ∀ y ∈ (W : V.Opens), y ∉ E.support) :
    ∃ m₀ : Γ(V, W), (toRationalFunctionsPresheaf V).app (op (W : V.Opens)) m₀ =
        ratRes (W : V.Opens) φ ∧
      (pt ∈ E.support → ∃ (i₀ : Fin c.r) (w : Γ(V, W)), c.j i₀ = E ∧ IsUnit w ∧
        m₀ = w * tW c hWc (Fin.castLE c.hr i₀)) ∧ (pt ∉ E.support → IsUnit m₀) := by
  by_cases hptE : pt ∈ E.support
  · obtain ⟨i₀, hi₀⟩ := exists_eq_of_mem_chart c.t c.hr c.j (fun i => (c.hjD i).2.2) c.hDW hE
      c.hx hptE
    have hEt : E.idealSheaf.ideal W = Ideal.span {tW c hWc (Fin.castLE c.hr i₀)} := by
      rw [← hi₀]
      exact ideal_eq_span_tW c hWc i₀
    obtain ⟨w, hw, hwrat⟩ := exists_isUnit_mul_prod_pow W
      (fun _ : Fin 1 => tW c hWc (Fin.castLE c.hr i₀)) (fun _ => E) (fun _ => hEt) (fun _ => 1)
      φ fun P hP => by simp [hord P hP]
    exact ⟨w * tW c hWc (Fin.castLE c.hr i₀), by simpa using hwrat,
      fun _ => ⟨i₀, w, hi₀, hw, rfl⟩, absurd hptE⟩
  · obtain ⟨w, hw, hwrat⟩ := exists_isUnit_mul_prod_pow W (Fin.elim0 : Fin 0 → Γ(V, W))
      (Fin.elim0 : Fin 0 → MMP.Mori.PrimeDivisor V) (fun k => k.elim0) Fin.elim0
      φ fun P hP => by
        rw [hord P hP, ite_eq_right]
        · simp
        · rintro rfl
          obtain ⟨y, hyP, hyW⟩ := hP
          exact hoff hptE y hyW hyP
    exact ⟨w, by simpa using hwrat, fun h => absurd h hptE, fun _ => hw⟩

open Classical in
/-- If `M'` is `M + E` and `φa`, `φb` are local equations of `M`, `M'` on `W`, then `φb / φa` has
order `1` along `E` and `0` along every other prime divisor meeting `W`. -/
theorem ord_mul_inv_eq_ite {W : V.Opens} {φa φb : (RationalFunctions V)ˣ}
    (hφa : M.IsLocalEquation W φa) (hφb : M'.IsLocalEquation W φb)
    (hM' : M' = M + Finsupp.single E 1) (P : MMP.Mori.PrimeDivisor V)
    (hP : (P.support ∩ W).Nonempty) : P.ord (φb * φa⁻¹) = if P = E then 1 else 0 := by
  rw [MMP.Mori.PrimeDivisor.ord_mul, MMP.Mori.PrimeDivisor.ord_inv, ← hφb P hP, ← hφa P hP, hM']
  simp only [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h : P = E
  · subst h
    simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]; ring

omit [IsLocallyNoetherian V] [IsNormal V] in
/-- Near a point `pt` of `E` where `g₀ ^ N = u v ∏ τₖ ^ Bn(jₖ)`, the connection form of `g₀` on an
affine open `W` of a chart has residue `Bn(E) / N`, an invertible scalar, along `E`. -/
theorem exists_connection_of_mem [IsIntegral V] {pt : V} (c : SNCChart d π D pt)
    {W : V.affineOpens} (hWc : (W : V.Opens) ≤ c.W) (i₀ : Fin c.r) (hi₀ : c.j i₀ = E)
    (hptW : pt ∈ (W : V.Opens)) (hptE : pt ∈ E.support) (hE : E ∈ D.support) (hN0 : N ≠ 0)
    (hunit : IsUnit u) {Bn : Divisor V} (hBn : ∀ E, 0 ≤ Bn E) (hBE : Bn E ≠ 0)
    {W₂ : V.affineOpens} (hW₂ : (W : V.Opens) ≤ W₂) (hy₂ : pt ∈ (W₂ : V.Opens)) {r : ℕ}
    {τ : Fin r → Γ(V, W₂)} {j : Fin r → MMP.Mori.PrimeDivisor V} (hj : Function.Injective j)
    (hjD : ∀ k, j k ∈ D.support) (hτ : ∀ k, (j k).idealSheaf.ideal W₂ = Ideal.span {τ k})
    (hDW₂ : D.suppIdeal.ideal W₂ = Ideal.span {∏ k, τ k}) {v : Γ(V, W₂)} (hv : IsUnit v)
    (g₀ : Γ(V, (W₂ : V.Opens) ⊓ cU' D M))
    (hX : g₀ ^ N = V.presheaf.map (homOfLE inf_le_right).op u *
      V.presheaf.map (homOfLE inf_le_left).op (v * ∏ k, τ k ^ (Bn (j k)).toNat)) :
    let g := (cU D).ι.app ((W : V.Opens) ⊓ cU' D M)
      (V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW₂)).op g₀)
    ∃ (ξ : (TB ((cU D).ι ≫ π)).Total (op (OO D M W))) (cO : Γ((cU D).toScheme, OO D M W)),
      cO * ((N : Γ((cU D).toScheme, OO D M W)) * resU W u) = 1 ∧
      δ ((cU D).ι ≫ π) (OO D M W) g - sm ((cU D).ι ≫ π) (OO D M W) cO *
          δ ((cU D).ι ≫ π) (OO D M W) (resU W u) * sm ((cU D).ι ≫ π) (OO D M W) g =
        sm ((cU D).ι ≫ π) (OO D M W) g * ξ ∧
      ∃ lam lamInv : Γ(V, W), lamInv * lam = 1 ∧
        (letI := chartAlgebra (f := π) (D := D) M (W := W);
          (∀ (q : ℕ) (z : (TB ((cU D).ι ≫ π)).Total (op (OO D M W))),
            Δ ((cU D).ι ≫ π) (OO D M W) q (lamInv • z) =
              lamInv • Δ ((cU D).ι ≫ π) (OO D M W) q z) ∧
          ResForm (θO c M hWc) (Fin.castLE c.hr i₀) (tW c hWc (Fin.castLE c.hr i₀)) lam ξ) := by
  intro g
  obtain ⟨k₀, hk₀⟩ := exists_eq_of_mem_chart τ le_rfl j hτ hDW₂ hE hy₂ hptE
  obtain ⟨Ni, hNi⟩ := (isUnit_natCast_sections π N hN0 (W : V.Opens)).exists_left_inv
  have hNO : IsUnit ((N : Γ((cU D).toScheme, OO D M W))) := by
    simpa only [map_natCast] using
      (isUnit_natCast_sections π N hN0 (W : V.Opens)).map (ρ (D := D) M)
  obtain ⟨cO, hcO⟩ := (hNO.mul (hunit.map (((cU D).ι.app ((W : V.Opens) ⊓ cU' D M)).hom.comp
    (V.presheaf.map (homOfLE inf_le_right).op).hom))).exists_left_inv
  obtain ⟨-, ξ, hres, hξ⟩ := exists_resForm_connection c M hWc i₀
    ⟨pt, hptW, by rwa [hi₀]⟩ hW₂ τ j hj hjD hτ v hv g₀
    (fun k => (Bn (j k)).toNat) u hunit N Ni hNi hX k₀ (hk₀.trans hi₀.symm) cO hcO
  have hb0 : (Bn (j k₀)).toNat ≠ 0 := by
    have := hBn E
    rw [hk₀]
    omega
  obtain ⟨binv, hbinv⟩ :=
    (isUnit_natCast_sections π (Bn (j k₀)).toNat hb0 (W : V.Opens)).exists_left_inv
  refine ⟨ξ, cO, hcO, hξ, Ni * ((Bn (j k₀)).toNat : Γ(V, W)), (N : Γ(V, W)) * binv, ?_, ?_⟩
  · linear_combination binv * ((Bn (j k₀)).toNat : Γ(V, W)) * hNi + hbinv
  · let _ := chartAlgebra (f := π) (D := D) M (W := W)
    exact ⟨fun q z => ChartAlgebra.map_smul_of_mul_eq_one (Δ ((cU D).ι ≫ π) (OO D M W) q) N
      (Bn (j k₀)).toNat hbinv z, hres⟩

omit [SmoothOfRelativeDimension d π] [IsLocallyNoetherian V] [IsNormal V] in
/-- If `m₀ = w t` with `w` a unit and `t` the chart equation of `E ∈ Supp D` near a point of `E`,
and `m₀` is a unit off `E`, then the restriction of `m₀` to `W ∩ U'` is a unit. -/
theorem isUnit_ρ_of_eq_mul_tW {pt : V} (c : SNCChart d π D pt) {W : V.affineOpens}
    (hWc : (W : V.Opens) ≤ c.W) (hE : E ∈ D.support) {m₀ : Γ(V, W)}
    (hm₀E : pt ∈ E.support → ∃ (i₀ : Fin c.r) (w : Γ(V, W)), c.j i₀ = E ∧ IsUnit w ∧
      m₀ = w * tW c hWc (Fin.castLE c.hr i₀)) (hm₀off : pt ∉ E.support → IsUnit m₀) :
    IsUnit (ρ (D := D) M m₀) := by
  by_cases hptE : pt ∈ E.support
  · obtain ⟨i₀, w, hi₀, hw, rfl⟩ := hm₀E hptE
    rw [map_mul]
    exact (hw.map _).mul (isUnit_ρ_of_ideal_eq M hE (hi₀ ▸ ideal_eq_span_tW c hWc i₀))
  · exact (hm₀off hptE).map _

omit [SmoothOfRelativeDimension d π] [IsLocallyNoetherian V] [IsNormal V] in
/-- If `g₁ = g₀ m` on `W ∩ U'` with `g₀` and the restriction of `m` units, then `g₁` is a unit. -/
theorem isUnit_ι_app_of_eq_mul {W : V.affineOpens} {g₀ : Γ(V, (W : V.Opens) ⊓ cU' D M)}
    {g₁ : Γ(V, (W : V.Opens) ⊓ cU' D M')} {m : Γ(V, W)}
    (unit₀ : IsUnit ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g₀))
    (rel : V.presheaf.map (homOfLE (inf_le_inf_left (W : V.Opens) hM.ge)).op g₁ =
      g₀ * V.presheaf.map (homOfLE inf_le_left).op m)
    (hm : IsUnit (ρ (D := D) M m)) : IsUnit ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M') g₁) := by
  have hOO : OO D M W = OO D M' W := by simp only [OO, hM]
  refine isUnit_of_isUnit_map hOO _ ?_
  have e : (cU D).toScheme.presheaf.map (homOfLE hOO.le).op
      ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M') g₁) =
      (cU D).ι.app ((W : V.Opens) ⊓ cU' D M)
        (V.presheaf.map (homOfLE (inf_le_inf_left (W : V.Opens) hM.ge)).op g₁) :=
    G1.app_restrict (inf_le_inf_left (W : V.Opens) hM.ge) g₁
  rw [e, rel, map_mul]
  exact unit₀.mul hm

omit [SmoothOfRelativeDimension d π] [IsLocallyNoetherian V] [IsNormal V] in
/-- On an irreducible scheme, every nonempty open meets `U' = V \ (Supp D ∪ Supp M)`. -/
theorem nonempty_inf_cU' [IrreducibleSpace V] {W : V.Opens} (hW : (W : Set V).Nonempty) :
    Nonempty (W ⊓ cU' D M : V.Opens) := by
  obtain ⟨pt, hpt⟩ := hW
  obtain ⟨y, hyW, hyU⟩ := nonempty_preirreducible_inter W.isOpen (cU' D M).isOpen ⟨pt, hpt⟩
    ⟨_, componentGenericPoint_mem_cU' D M
      ⟨irreducibleComponent pt, irreducibleComponent_mem_irreducibleComponents pt⟩⟩
  exact ⟨⟨y, hyW, hyU⟩⟩

/-- **The local data exist near every point.** -/
theorem nonempty_localData [IsIntegral V] [CompactSpace V] (hD : D.IsRelativeSNC d π)
    (Bn : Divisor V) (hSB : ∀ E, D E = (0 : Divisor V) E + if Bn E = 0 then 0 else 1)
    (hN : 0 < N) (hBn : ∀ E, 0 ≤ Bn E) (ψ : (RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (hu : (toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ)
    (hBE : Bn E ≠ 0) (hM' : M' = M + Finsupp.single E 1) (pt : V) (W₀ : V.Opens)
    (hpt : pt ∈ W₀) : Nonempty (LocalData d π D M M' hM N u E pt W₀) := by
  classical
  have hBD : ∀ E', Bn E' ≠ 0 → E' ∈ D.support := fun E' h => by
    rw [Finsupp.mem_support_iff, hSB E', ite_eq_right h]
    simp
  have hE : E ∈ D.support := hBD E hBE
  have : Smooth π := SmoothOfRelativeDimension.smooth d π
  have hsm : MMP.Mori.IsSmoothScheme π := (MMP.Mori.isSmoothScheme_iff π).2 this
  have hMC : M.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm M
  have hMC' : M'.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm M'
  have hN0 : N ≠ 0 := hN.ne'
  have hunit : IsUnit u := isUnit_of_smul_eq_add_principalDivisor hBD hψ hu
  obtain ⟨c⟩ := nonempty_sncChart hD pt
  obtain ⟨W₂, hy₂, r, τ, j, v, g₀, hj, hjD, hτ, hDW₂, hv, hg₀div, hg₀gen, hX⟩ :=
    exists_generator_factorization d π D hD M u hMC Bn N ψ hψ hu hBn hBD pt
  obtain ⟨Wa, hpta, φa, hφa⟩ := hMC pt
  obtain ⟨Wb, hptb, φb, hφb⟩ := hMC' pt
  obtain ⟨g₂, hg₂rat, hg₂div, hg₂gen⟩ := exists_generator D M hφa
  obtain ⟨g₁, hg₁rat, hg₁div, hg₁gen⟩ := exists_generator D M' hφb
  obtain ⟨Wx, hptx, hWxE⟩ : ∃ Wx : V.Opens, pt ∈ Wx ∧
      (pt ∉ E.support → ∀ y ∈ Wx, y ∉ E.support) := by
    by_cases h : pt ∈ E.support
    · exact ⟨⊤, trivial, absurd h⟩
    · exact ⟨E.idealSheaf.support.compl, h, fun _ y hy => hy⟩
  obtain ⟨W', hW'a, hptW, hW'le⟩ := Opens.isBasis_iff_nbhd.mp V.isBasis_affineOpens
    (show pt ∈ W₀ ⊓ (c.W : V.Opens) ⊓ (W₂ : V.Opens) ⊓ Wa ⊓ Wb ⊓ Wx from
      ⟨⟨⟨⟨⟨hpt, c.hx⟩, hy₂⟩, hpta⟩, hptb⟩, hptx⟩)
  simp only [le_inf_iff] at hW'le
  obtain ⟨⟨⟨⟨⟨hW₀, hWc⟩, hWW₂⟩, hWa⟩, hWb⟩, hWx⟩ := hW'le
  let W : V.affineOpens := ⟨W', hW'a⟩
  have : Nonempty ((W : V.Opens) ⊓ cU' D M : V.Opens) :=
    nonempty_inf_cU' (D := D) (M := M) ⟨pt, hptW⟩
  let g₀W := V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hWW₂)).op g₀
  have div₀ : DivCond (D := D) (M := M) (W : V.Opens) g₀W := DivCond.restrict D M hWW₂ hg₀div
  have gen₀ := exists_eq_mul_map_of_le hWW₂ hg₀gen
  have unit₀ : IsUnit ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g₀W) :=
    isUnit_genO_of_rel (W := W) hWW₂ τ j hjD hτ v hv g₀ (fun k => (Bn (j k)).toNat) u hunit N
      hN0 hX
  let g₂W := V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hWa)).op g₂
  have div₂ : DivCond (D := D) (M := M) (W : V.Opens) g₂W := DivCond.restrict D M hWa hg₂div
  have gen₂ := exists_eq_mul_map_of_le hWa hg₂gen
  let g₁W := V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M') hWb)).op g₁
  have div₁ : DivCond (D := D) (M := M') (W : V.Opens) g₁W := DivCond.restrict D M' hWb hg₁div
  have gen₁ := exists_eq_mul_map_of_le hWb hg₁gen
  obtain ⟨h₀, hh₀u, hh₀⟩ := exists_isUnit_eq_mul_of_generators div₀ div₂ gen₀ gen₂ unit₀
  obtain ⟨m₀, hm₀rat, hm₀E, hm₀off⟩ :=
    exists_eq_mul_tW_of_ord (W := W) c hWc hE
      (ord_mul_inv_eq_ite (hφa.mono hWa) (hφb.mono hWb) hM') fun hptE y hy => hWxE hptE y (hWx hy)
  rw [Units.val_mul] at hm₀rat
  have rel : V.presheaf.map (homOfLE (inf_le_inf_left (W : V.Opens) hM.ge)).op g₁W =
      g₀W * V.presheaf.map (homOfLE inf_le_left).op (h₀ * m₀) := by
    calc V.presheaf.map (homOfLE (inf_le_inf_left (W : V.Opens) hM.ge)).op g₁W =
        V.presheaf.map (homOfLE (inf_le_inf hWb hM.ge)).op g₁ := presheaf_map_map _ _ _ _
      _ = g₂W * V.presheaf.map (homOfLE inf_le_left).op m₀ :=
        map_eq_mul_of_ratRes hM hWb hWa hg₁rat hg₂rat hm₀rat
      _ = _ := by rw [hh₀, map_mul]; ring
  have unit₁ : IsUnit ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M') g₁W) :=
    isUnit_ι_app_of_eq_mul hM unit₀ rel <| by
      rw [map_mul]
      exact (hh₀u.map _).mul (isUnit_ρ_of_eq_mul_tW c hWc hE hm₀E hm₀off)
  refine ⟨⟨W, hW₀, hptW, c, hWc, g₀W, div₀, gen₀, unit₀, g₁W, div₁, gen₁, unit₁, h₀ * m₀, rel,
    fun hptE => ?_, fun hptE => hh₀u.mul (hm₀off hptE)⟩⟩
  obtain ⟨i₀, w, hi₀, hw, hm₀eq⟩ := hm₀E hptE
  exact ⟨i₀, h₀ * w, hi₀, hh₀u.mul hw, by rw [hm₀eq, mul_assoc], exists_connection_of_mem c hWc i₀
    hi₀ hptW hptE hE hN0 hunit hBn hBE hWW₂ hy₂ hj hjD hτ hDW₂ hv g₀ hX⟩

end TwistChartForms

end MMP.LcBpf
