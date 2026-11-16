module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.ChartResidue

/-!
# Generators of `𝒪_X(-M)` and of a twist on a chart

Two generators of `𝒪_X(-M)` on every open of `W` differ by a unit of `Γ(X, W)`. If `M'` is a
divisor with the same open `U' = X ∖ (D ∪ Supp M)` and `φ₁`, `φ₂` are local equations of `M'` and
`M` with `φ₁ / φ₂ = m` a function on `W`, then the generators given by `φ₁` and `φ₂` differ by
`m` on `W ∩ U'`. Forms and combinations on `U ∩ W ∩ U'` for `M'` restrict to those for `M`.

## Main results

* `MMP.LcBpf.TwistChartForms.exists_isUnit_eq_mul_of_generators`: two generators differ by a unit.
* `MMP.LcBpf.TwistChartForms.map_eq_mul_of_ratRes`: generators from local equations.
* `MMP.LcBpf.TwistChartForms.totalRestrict_combo_twist`: combinations restrict.
* `MMP.LcBpf.TwistChartForms.isUnit_genO_of_rel`: a generator with `g^N = u v ∏ τₖ^{bₖ}` is a
  unit on `U ∩ W ∩ U'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.Mori MMP.FourfoldProofs.FractionalLogComplexProof

universe u

namespace TwistChartForms

open MMP.Mori.Divisor.LogSpreadingProof.G1 (SNCChart)

section Twist

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n : ℕ}
  [SmoothOfRelativeDimension n f] {D : Divisor X} {x₀ : X} (c : SNCChart n f D x₀)
  {M M' : Divisor X} (hM : cU' D M' = cU' D M)

include hM in
/-- If `M` and `M'` have the same open `U' = X ∖ (D ∪ Supp M)`, the trace `U ∩ W ∩ U'` for `M` lies
in the one for `M'`. -/
theorem OO_le_twist (W : X.Opens) : OO D M W ≤ OO D M' W :=
  Scheme.Hom.preimage_mono _ (inf_le_inf_left W hM.ge)

omit [SmoothOfRelativeDimension n f] in
/-- The combination `∑_K a_K θ_K` of the chart forms for `M'` restricts to the combination with
the same coefficients of the chart forms for `M`. -/
theorem totalRestrict_combo_twist {W : X.affineOpens} (hW : (W : X.Opens) ≤ c.W) (q : ℕ)
    (a : {K : Finset (Fin n) // K.card = q} → Γ(X, W)) :
    (TB ((cU D).ι ≫ f)).totalRestrict (homOfLE (OO_le_twist hM W)).op
        (letI := chartAlgebra (f := f) (D := D) M' (W := W);
          ChartAlgebra.combo (θO c M' hW) q a) =
      (letI := chartAlgebra (f := f) (D := D) M (W := W);
        ChartAlgebra.combo (θO c M hW) q a) := by
  rw [← totalRestrict_logCombo c M' hW, ← totalRestrict_logCombo c M hW,
    totalRestrict_totalRestrict]

/-- The structure map `sm` for `M'` applied to `g` restricts to the structure map for `M` applied
to the restriction of `g`. -/
theorem totalRestrict_sm_twist (W : X.Opens) (g : Γ(X, W ⊓ cU' D M')) :
    (TB ((cU D).ι ≫ f)).totalRestrict (homOfLE (OO_le_twist hM W)).op
        (sm ((cU D).ι ≫ f) (OO D M' W) ((cU D).ι.app (W ⊓ cU' D M') g)) =
      sm ((cU D).ι ≫ f) (OO D M W) ((cU D).ι.app (W ⊓ cU' D M)
        (X.presheaf.map (homOfLE (inf_le_inf_left W hM.ge)).op g)) := by
  rw [totalRestrict_sm]
  exact congrArg _ (G1.app_restrict (inf_le_inf_left W hM.ge) g)

end Twist

section Generators

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {D M : Divisor X}

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Restriction from an open to itself is the identity. -/
theorem presheaf_map_self {A : X.Opens} (h : A ≤ A) (a : Γ(X, A)) :
    X.presheaf.map (homOfLE h).op a = a := by
  rw [show (homOfLE h).op = 𝟙 (op A) from Subsingleton.elim _ _, X.presheaf.map_id]
  rfl

/-- **Two generators of `𝒪_X(-M)` on every open of `W` differ by a unit.** -/
theorem exists_isUnit_eq_mul_of_generators [IsIntegral X] {W : X.Opens}
    [Nonempty (W ⊓ cU' D M : X.Opens)] {g g' : Γ(X, W ⊓ cU' D M)}
    (hg : DivCond (D := D) (M := M) W g) (hg' : DivCond (D := D) (M := M) W g')
    (hgen : ∀ (W₃ : X.Opens) (h₃ : W₃ ≤ W) (g'' : Γ(X, W₃ ⊓ cU' D M)),
      DivCond (D := D) (M := M) W₃ g'' → ∃ h : Γ(X, W₃),
        g'' = X.presheaf.map (homOfLE inf_le_left).op h *
          X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g)
    (hgen' : ∀ (W₃ : X.Opens) (h₃ : W₃ ≤ W) (g'' : Γ(X, W₃ ⊓ cU' D M)),
      DivCond (D := D) (M := M) W₃ g'' → ∃ h : Γ(X, W₃),
        g'' = X.presheaf.map (homOfLE inf_le_left).op h *
          X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g')
    (hgu : IsUnit ((cU D).ι.app (W ⊓ cU' D M) g)) :
    ∃ h : Γ(X, W), IsUnit h ∧ g' = X.presheaf.map (homOfLE inf_le_left).op h * g := by
  obtain ⟨h, hh⟩ := hgen W le_rfl g' hg'
  obtain ⟨h', hh'⟩ := hgen' W le_rfl g hg
  rw [presheaf_map_self] at hh hh'
  refine ⟨h, ?_, hh⟩
  have e1 : ((cU D).ι.app (W ⊓ cU' D M)).hom (X.presheaf.map (homOfLE inf_le_left).op (h' * h)) *
      ((cU D).ι.app (W ⊓ cU' D M)).hom g = 1 * ((cU D).ι.app (W ⊓ cU' D M)).hom g := by
    rw [one_mul, ← map_mul]
    congr 1
    rw [map_mul, mul_assoc, ← hh, ← hh']
  have e3 : X.presheaf.map (homOfLE (inf_le_left : W ⊓ cU' D M ≤ W)).op (h' * h) =
      X.presheaf.map (homOfLE (inf_le_left : W ⊓ cU' D M ≤ W)).op 1 :=
    (ι_app_bijective (cU D) _ (inf_le_right.trans (cU'_le_cU D M))).1
      (by rw [hgu.mul_right_cancel e1, map_one, map_one])
  exact IsUnit.of_mul_eq_one h'
    ((mul_comm _ _).trans (map_injective_of_isIntegral X (homOfLE inf_le_left) e3))

omit [IsLocallyNoetherian X] in
/-- **Generators from local equations.** If `g₁` and `g₂` are the functions `φ₁` and `φ₂` on
`W₁ ∩ U'` and `W₂ ∩ U'`, and `φ₁ / φ₂ = m` on `W`, then `g₁ = g₂ m` on `W ∩ U'`. -/
theorem map_eq_mul_of_ratRes {M' : Divisor X} (hM : cU' D M' = cU' D M) {W W₁ W₂ : X.Opens}
    (h₁ : W ≤ W₁) (h₂ : W ≤ W₂) {φ₁ φ₂ : (RationalFunctions X)ˣ}
    {g₁ : Γ(X, W₁ ⊓ cU' D M')}
    (hg₁ : (toRationalFunctionsPresheaf X).app (op (W₁ ⊓ cU' D M')) g₁ =
      ratRes (W₁ ⊓ cU' D M') φ₁)
    {g₂ : Γ(X, W₂ ⊓ cU' D M)}
    (hg₂ : (toRationalFunctionsPresheaf X).app (op (W₂ ⊓ cU' D M)) g₂ = ratRes (W₂ ⊓ cU' D M) φ₂)
    {m : Γ(X, W)} (hm : (toRationalFunctionsPresheaf X).app (op W) m = ratRes W (φ₁ * φ₂⁻¹)) :
    X.presheaf.map (homOfLE (inf_le_inf h₁ hM.ge : W ⊓ cU' D M ≤ W₁ ⊓ cU' D M')).op g₁ =
      X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₂)).op g₂ *
        X.presheaf.map (homOfLE inf_le_left).op m := by
  apply toRationalFunctionsPresheaf_app_injective
  rw [map_mul, toRationalFunctionsPresheaf_app_map, toRationalFunctionsPresheaf_app_map,
    toRationalFunctionsPresheaf_app_map, hg₁, hg₂, hm]
  funext Z
  change (φ₁ : RationalFunctions X) Z.1 =
    (φ₂ : RationalFunctions X) Z.1 * (↑(φ₁ * φ₂⁻¹) : RationalFunctions X) Z.1
  rw [Units.val_mul, Pi.mul_apply, mul_left_comm, ← Pi.mul_apply (↑φ₂ : RationalFunctions X),
    Units.mul_inv, Pi.one_apply, mul_one]

end Generators

section Units

variable {X : Scheme.{u}} {D M : Divisor X}

/-- **A generator with `g^N = u v ∏ τₖ^{bₖ}` is a unit on `U ∩ W ∩ U'`.** -/
theorem isUnit_genO_of_rel {W W₂ : X.affineOpens} (hW₂ : (W : X.Opens) ≤ W₂) {r : ℕ}
    (τ : Fin r → Γ(X, W₂)) (j : Fin r → MMP.Mori.PrimeDivisor X)
    (hjD : ∀ k, j k ∈ D.support) (hτ : ∀ k, (j k).idealSheaf.ideal W₂ = Ideal.span {τ k})
    (v : Γ(X, W₂)) (hv : IsUnit v) (g₀ : Γ(X, (W₂ : X.Opens) ⊓ cU' D M)) (b : Fin r → ℕ)
    (uu : Γ(X, cU' D M)) (huu : IsUnit uu) (N : ℕ) (hN0 : N ≠ 0)
    (hrel : g₀ ^ N = X.presheaf.map (homOfLE inf_le_right).op uu *
      X.presheaf.map (homOfLE inf_le_left).op (v * ∏ k, τ k ^ b k)) :
    IsUnit (genO M g₀ hW₂) := by
  set ρ₂ : Γ(X, W₂) →+* Γ(X, W) := (X.presheaf.map (homOfLE hW₂).op).hom
  have e2 : X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW₂)).op
      (X.presheaf.map (homOfLE inf_le_left).op (v * ∏ k, τ k ^ b k)) =
      X.presheaf.map (homOfLE inf_le_left).op (ρ₂ (v * ∏ k, τ k ^ b k)) :=
    (presheaf_map_map _ _ (homOfLE (inf_le_left.trans hW₂)).op _).trans
      (presheaf_map_map _ _ _ _).symm
  have hrelO : genO M g₀ hW₂ ^ N = resU (D := D) (M := M) W uu *
      ρ (D := D) M (ρ₂ (v * ∏ k, τ k ^ b k)) := by
    simp only [genO, ← map_pow]
    rw [hrel, map_mul, map_mul, e2, presheaf_map_map]
    rfl
  refine (isUnit_pow_iff hN0).mp ?_
  rw [hrelO, map_mul, map_mul, map_prod, map_prod]
  refine (huu.map (((cU D).ι.app ((W : X.Opens) ⊓ cU' D M)).hom.comp
    (X.presheaf.map (homOfLE inf_le_right).op).hom)).mul (((hv.map ρ₂).map _).mul ?_)
  refine Finset.prod_induction _ IsUnit (fun a c ha hc => ha.mul hc) isUnit_one fun k _ => ?_
  rw [map_pow, map_pow]
  have hτW : (j k).idealSheaf.ideal W = Ideal.span {ρ₂ (τ k)} := by
    rw [← (j k).idealSheaf.map_ideal hW₂, hτ k, Ideal.map_span, Set.image_singleton]
    rfl
  exact (isUnit_ρ_of_ideal_eq M (hjD k) hτW).pow _

/-- A function on an open is a unit if its restriction to an equal open is. -/
theorem isUnit_of_isUnit_map {Y : Scheme.{u}} {A B : Y.Opens} (hAB : A = B) (x : Γ(Y, B))
    (h : IsUnit (Y.presheaf.map (homOfLE hAB.le).op x)) : IsUnit x := by
  have h2 := h.map (Y.presheaf.map (homOfLE hAB.ge).op).hom
  rwa [show (Y.presheaf.map (homOfLE hAB.ge).op).hom ((Y.presheaf.map (homOfLE hAB.le).op) x) = x
    from (presheaf_map_map _ _ (𝟙 _) x).trans (by rw [Y.presheaf.map_id]; rfl)] at h2

end Units

end TwistChartForms

end MMP.LcBpf
