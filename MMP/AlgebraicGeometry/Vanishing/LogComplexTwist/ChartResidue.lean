module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.ChartRepresentation

/-!
# The connection form of the fractional logarithmic complex on a chart

Let `W` be an affine open inside a chart `c` of the relative simple normal crossing divisor `D`,
`E = D_{c.j i₀}` a component of `D` meeting `W`, with equation `t = t_{i₀}` and `θ = dt/t`. If
`g₀^N = u v ∏ τₖ^{bₖ}` on `U ∩ W ∩ U'`, with `v` a unit and `τₖ` local equations of components
`jₖ` of `D`, then the connection form `ξ = g₀⁻¹ (dg₀ - (N u)⁻¹ du g₀)` of `∇ = d - (N u)⁻¹ du ∧` is
`N⁻¹ (dv/v + ∑ bₖ dτₖ/τₖ)`; its `θ`-coefficient is `b/N + t μ` with `b` the exponent of the
equation of `E`, and its other part is a logarithmic form free of `θ`. A form `g₀ z` with `z` a
combination of the `θ_K` then has `∇(g₀ z) = g₀ (ξ ∧ z + dz)`.

## Main definitions

* `MMP.LcBpf.TwistChartForms.ResForm`: a `1`-form `λ θ + ξ' + t μ θ` with `ξ'` free of `θ`.

## Main results

* `MMP.LcBpf.TwistChartForms.resForm_dl`: the logarithmic derivative of a local equation of a
  component of `D`.
* `MMP.LcBpf.TwistChartForms.exists_resForm_connection`: the connection form.
* `MMP.LcBpf.TwistChartForms.incl_eq_sm_mul_nabla`: `∇(g₀ z) = g₀ (ξ ∧ z + dz)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.Mori MMP.FourfoldProofs.FractionalLogComplexProof

universe u

namespace TwistChartForms

open MMP.Mori.Divisor.LogSpreadingProof.G1 (SNCChart)

section ResForm

variable {R Λ : Type*} [CommRing R] [Ring Λ] [Algebra R Λ] {n : ℕ} (θ : Fin n → Λ) (i₀ : Fin n)
  (t : R)

/-- A `1`-form `λ θ + ξ' + t μ θ` with `ξ'` free of `θ = θ_{i₀}`. -/
def ResForm (lam : R) (x : Λ) : Prop :=
  ∃ a₀ ∈ ChartAlgebra.L (R := R) θ i₀ 1, ∃ a₁ : R, x = lam • θ i₀ + a₀ + (t * a₁) • θ i₀

variable {θ i₀ t}

/-- A sum of forms of the shape `ResForm` with coefficients `l` and `l'` has coefficient
`l + l'`. -/
theorem ResForm.add {l l' : R} {x y : Λ} (hx : ResForm θ i₀ t l x) (hy : ResForm θ i₀ t l' y) :
    ResForm θ i₀ t (l + l') (x + y) := by
  obtain ⟨a₀, ha₀, a₁, rfl⟩ := hx
  obtain ⟨b₀, hb₀, b₁, rfl⟩ := hy
  exact ⟨a₀ + b₀, add_mem ha₀ hb₀, a₁ + b₁, by
    rw [add_smul, mul_add, add_smul]
    abel⟩

/-- Scaling a form of the shape `ResForm` with coefficient `l` by `r` gives coefficient `r * l`. -/
theorem ResForm.smul {l : R} {x : Λ} (r : R) (hx : ResForm θ i₀ t l x) :
    ResForm θ i₀ t (r * l) (r • x) := by
  obtain ⟨a₀, ha₀, a₁, rfl⟩ := hx
  exact ⟨r • a₀, Submodule.smul_mem _ _ ha₀, r * a₁, by
    rw [smul_add, smul_add, smul_smul, smul_smul, mul_left_comm]⟩

/-- The coefficient in `ResForm` may be replaced by an equal one. -/
theorem ResForm.congr_lam {l l' : R} {x : Λ} (h : ResForm θ i₀ t l x) (e : l = l') :
    ResForm θ i₀ t l' x := e ▸ h

/-- A form in `ChartAlgebra.L θ i₀ 1` has the shape `ResForm` with coefficient `0`. -/
theorem ResForm.of_mem {a : Λ} (ha : a ∈ ChartAlgebra.L (R := R) θ i₀ 1) :
    ResForm θ i₀ t 0 a := ⟨a, ha, 0, by simp⟩

/-- The form `θ i₀` has the shape `ResForm` with coefficient `1`. -/
theorem ResForm.self : ResForm θ i₀ t 1 (θ i₀) := ⟨0, zero_mem _, 0, by simp⟩

/-- The zero form has the shape `ResForm` with coefficient `0`. -/
theorem ResForm.zero : ResForm θ i₀ t 0 0 := ⟨0, zero_mem _, 0, by simp⟩

/-- A finite sum of forms of the shape `ResForm` has as coefficient the sum of the coefficients. -/
theorem ResForm.sum {ι : Type*} (s : Finset ι) (l : ι → R) (x : ι → Λ)
    (h : ∀ i ∈ s, ResForm θ i₀ t (l i) (x i)) : ResForm θ i₀ t (∑ i ∈ s, l i) (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (ResForm.zero : ResForm θ i₀ t 0 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end ResForm

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n : ℕ}
  [SmoothOfRelativeDimension n f] {D : Divisor X} {x₀ : X} (c : SNCChart n f D x₀)
  (M : Divisor X) {W : X.affineOpens} (hW : (W : X.Opens) ≤ c.W)

/-- A multiple of `Dr a` has no residue. -/
theorem resForm_smul_Dr {i₀ : Fin n} (hi₀ : (i₀ : ℕ) < c.r) (ai a : Γ(X, W)) :
    letI := chartAlgebra (f := f) (D := D) M (W := W)
    ResForm (θO c M hW) i₀ (tW c hW i₀) 0 (ai • Dr (f := f) (D := D) M a) := by
  let _ := chartAlgebra (f := f) (D := D) M (W := W)
  obtain ⟨a₀, ha₀, a₁, he⟩ := exists_Dr_eq c M hW hi₀ a
  refine (ResForm.smul ai ⟨a₀, ha₀, a₁, ?_⟩).congr_lam (mul_zero ai)
  rw [he, zero_smul, zero_add]

/-- The logarithmic derivative of a function invertible on `W` has no residue. -/
theorem resForm_dl_unit {i₀ : Fin n} (hi₀ : (i₀ : ℕ) < c.r) {a ai : Γ(X, W)} (h : ai * a = 1)
    (s : Γ((cU D).toScheme, OO D M W)) (hs : s * ρ M a = 1) :
    letI := chartAlgebra (f := f) (D := D) M (W := W)
    ResForm (θO c M hW) i₀ (tW c hW i₀) 0 (dl ((cU D).ι ≫ f) (OO D M W) (ρ M a) s) := by
  let _ := chartAlgebra (f := f) (D := D) M (W := W)
  have e : dl ((cU D).ι ≫ f) (OO D M W) (ρ M a) s = ai • Dr (f := f) (D := D) M a := by
    rw [dl_congr hs (by rw [← map_mul, h, map_one] : ρ M ai * ρ M a = 1), chartAlgebra_smul]
    rfl
  rw [e]
  exact resForm_smul_Dr c M hW hi₀ ai a

variable [IsIntegral X]

open Classical in
/-- **The logarithmic derivative of a local equation of a component of `D`** has residue `1`
along that component and no residue along the others. -/
theorem resForm_dl (i₀ : Fin c.r) (hE : ∃ y ∈ (W : X.Opens), y ∈ (c.j i₀).support)
    {P : MMP.Mori.PrimeDivisor X} (hP : P ∈ D.support) {τ : Γ(X, W)}
    (hτ : P.idealSheaf.ideal W = Ideal.span {τ}) (s : Γ((cU D).toScheme, OO D M W))
    (hs : s * ρ M τ = 1) :
    letI := chartAlgebra (f := f) (D := D) M (W := W)
    ResForm (θO c M hW) (Fin.castLE c.hr i₀) (tW c hW (Fin.castLE c.hr i₀))
      (if P = c.j i₀ then 1 else 0) (dl ((cU D).ι ≫ f) (OO D M W) (ρ M τ) s) := by
  let _ := chartAlgebra (f := f) (D := D) M (W := W)
  have hi₀ : ((Fin.castLE c.hr i₀ : Fin n) : ℕ) < c.r := i₀.2
  obtain ⟨y₀, hy₀W, hy₀E⟩ := hE
  have : Nonempty (W : X.Opens) := ⟨⟨y₀, hy₀W⟩⟩
  by_cases hmeet : ∃ y ∈ (W : X.Opens), y ∈ P.support
  · obtain ⟨y, hyW, hyP⟩ := hmeet
    obtain ⟨i', hi'⟩ := exists_eq_of_mem_chart c.t c.hr c.j (fun i => (c.hjD i).2.2) c.hDW hP
      (hW hyW) hyP
    have hτ' : P.idealSheaf.ideal W = Ideal.span {tW c hW (Fin.castLE c.hr i')} := by
      rw [← hi', ← (c.j i').idealSheaf.map_ideal hW, (c.hjD i').2.2, Ideal.map_span,
        Set.image_singleton]
      rfl
    obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp (hτ'.symm.trans hτ)
    have hσ := σO_mul_tO c M hW (i := Fin.castLE c.hr i') i'.2
    have hwi : ρ (D := D) M (↑w⁻¹ : Γ(X, W)) * ρ (D := D) M (↑w : Γ(X, W)) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have e : dl ((cU D).ι ≫ f) (OO D M W) (ρ M τ) s =
        θO c M hW (Fin.castLE c.hr i') + (↑w⁻¹ : Γ(X, W)) • Dr (f := f) (D := D) M ↑w := by
      have e1 : ρ M τ = tO c M hW (Fin.castLE c.hr i') * ρ M ↑w := by
        rw [← hw, map_mul, tO_eq]
      have hs' : (σO c M hW (Fin.castLE c.hr i') * ρ M ↑w⁻¹) *
          (tO c M hW (Fin.castLE c.hr i') * ρ M ↑w) = 1 := by
        rw [mul_mul_mul_comm, hσ, hwi, one_mul]
      rw [e1, dl_congr (e1 ▸ hs) hs', dl_mul hσ hwi, chartAlgebra_smul]
      rfl
    rw [e]
    have hu := resForm_smul_Dr c M hW hi₀ (↑w⁻¹ : Γ(X, W)) (↑w : Γ(X, W))
    by_cases hPE : P = c.j i₀
    · obtain rfl : i' = i₀ := c.hj (hi'.trans hPE)
      rw [ite_eq_left hPE]
      exact (ResForm.self.add hu).congr_lam (add_zero 1)
    · rw [ite_eq_right hPE]
      have hne : Fin.castLE c.hr i' ≠ Fin.castLE c.hr i₀ := fun h =>
        hPE (hi'.symm.trans (congrArg c.j (Fin.castLE_injective c.hr h)))
      refine ((ResForm.of_mem ?_).add hu).congr_lam (add_zero 0)
      rw [← ChartAlgebra.θK_singleton (θO c M hW)]
      exact ChartAlgebra.θK_mem_L _ (Finset.card_singleton _)
        fun h => hne (Finset.mem_singleton.mp h).symm
  · have htop := ideal_eq_top_of_disjoint P.idealSheaf W fun y hy hyP => hmeet ⟨y, hy, hyP⟩
    rw [hτ, Ideal.span_singleton_eq_top] at htop
    obtain ⟨τi, hτi⟩ := htop.exists_left_inv
    have hPE : P ≠ c.j i₀ := by
      rintro rfl
      exact hmeet ⟨y₀, hy₀W, hy₀E⟩
    rw [ite_eq_right hPE]
    exact resForm_dl_unit c M hW hi₀ hτi s hs

omit [IsIntegral X] in
/-- A local equation of a component of `D` is invertible on `O`. -/
theorem isUnit_ρ_of_ideal_eq {P : MMP.Mori.PrimeDivisor X} (hP : P ∈ D.support) {τ : Γ(X, W)}
    (hτ : P.idealSheaf.ideal W = Ideal.span {τ}) : IsUnit (ρ (D := D) M τ) := by
  have h := (B1.isUnit_res_of_ideal_eq D hP hτ).map ((cU D).toScheme.presheaf.map
    ((Opens.map (cU D).ι.base).map (homOfLE (inf_le_left : (W : X.Opens) ⊓ cU' D M ≤ W))).op).hom
  have e : ρ (D := D) M τ = (cU D).toScheme.presheaf.map ((Opens.map (cU D).ι.base).map
      (homOfLE (inf_le_left : (W : X.Opens) ⊓ cU' D M ≤ W))).op ((cU D).ι.app W τ) :=
    (G1.app_restrict inf_le_left τ).symm
  exact e ▸ h

omit [IsIntegral X] in
/-- The relation `g₀ ^ N = u v ∏ τₖ ^ bₖ` on `W₂ ∩ U'`, restricted to `O`. -/
theorem genO_pow_eq {W₂ : X.affineOpens} (hW₂ : (W : X.Opens) ≤ W₂) {r : ℕ}
    (τ : Fin r → Γ(X, W₂)) (v : Γ(X, W₂)) (g₀ : Γ(X, (W₂ : X.Opens) ⊓ cU' D M)) (b : Fin r → ℕ)
    (uu : Γ(X, cU' D M)) (N : ℕ)
    (hrel : g₀ ^ N = X.presheaf.map (homOfLE inf_le_right).op uu *
      X.presheaf.map (homOfLE inf_le_left).op (v * ∏ k, τ k ^ b k)) :
    genO M g₀ hW₂ ^ N = resU (D := D) (M := M) W uu *
      ρ (D := D) M ((X.presheaf.map (homOfLE hW₂).op).hom v) *
        ∏ k, ρ (D := D) M ((X.presheaf.map (homOfLE hW₂).op).hom (τ k)) ^ b k := by
  set ρ₂ : Γ(X, W₂) →+* Γ(X, W) := (X.presheaf.map (homOfLE hW₂).op).hom
  have e2 : X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW₂)).op
      (X.presheaf.map (homOfLE inf_le_left).op (v * ∏ k, τ k ^ b k)) =
      X.presheaf.map (homOfLE inf_le_left).op (ρ₂ (v * ∏ k, τ k ^ b k)) :=
    (presheaf_map_map _ _ (homOfLE (inf_le_left.trans hW₂)).op _).trans
      (presheaf_map_map _ _ _ _).symm
  have e3 : X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW₂)).op
      (X.presheaf.map (homOfLE inf_le_right).op uu) =
      X.presheaf.map (homOfLE inf_le_right).op uu := presheaf_map_map _ _ _ _
  calc genO M g₀ hW₂ ^ N = ((cU D).ι.app ((W : X.Opens) ⊓ cU' D M)).hom
        (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW₂)).op (g₀ ^ N)) := by
        simp only [genO, map_pow]
    _ = ((cU D).ι.app ((W : X.Opens) ⊓ cU' D M)).hom
          (X.presheaf.map (homOfLE inf_le_right).op uu) *
        ((cU D).ι.app ((W : X.Opens) ⊓ cU' D M)).hom
          (X.presheaf.map (homOfLE inf_le_left).op (ρ₂ (v * ∏ k, τ k ^ b k))) := by
        rw [hrel, map_mul, map_mul, e2, e3]
    _ = resU (D := D) (M := M) W uu *
          (ρ (D := D) M (ρ₂ v) * ρ (D := D) M (ρ₂ (∏ k, τ k ^ b k))) := by
        rw [map_mul ρ₂]
        exact congrArg (resU (D := D) (M := M) W uu * ·) (map_mul (ρ (D := D) M) _ _)
    _ = _ := by simp only [map_prod, map_pow, mul_assoc]

/-- **The connection form on the chart.** If `g₀^N = u v ∏ τₖ^{bₖ}` with `v` a unit and the `τₖ`
local equations of distinct components `jₖ` of `D`, `j k₀ = E`, then `g₀` is a unit on `O` and
`dg₀ - (N u)⁻¹ du g₀ = g₀ ξ` with `ξ = (b_{k₀}/N) θ + ξ' + t μ θ`, `ξ'` free of `θ`. -/
theorem exists_resForm_connection (i₀ : Fin c.r) (hE : ∃ y ∈ (W : X.Opens), y ∈ (c.j i₀).support)
    {W₂ : X.affineOpens} (hW₂ : (W : X.Opens) ≤ W₂) {r : ℕ} (τ : Fin r → Γ(X, W₂))
    (j : Fin r → MMP.Mori.PrimeDivisor X) (hj : Function.Injective j)
    (hjD : ∀ k, j k ∈ D.support) (hτ : ∀ k, (j k).idealSheaf.ideal W₂ = Ideal.span {τ k})
    (v : Γ(X, W₂)) (hv : IsUnit v) (g₀ : Γ(X, (W₂ : X.Opens) ⊓ cU' D M)) (b : Fin r → ℕ)
    (uu : Γ(X, cU' D M)) (huu : IsUnit uu) (N : ℕ) (Ni : Γ(X, W)) (hNi : Ni * (N : Γ(X, W)) = 1)
    (hrel : g₀ ^ N = X.presheaf.map (homOfLE inf_le_right).op uu *
      X.presheaf.map (homOfLE inf_le_left).op (v * ∏ k, τ k ^ b k))
    (k₀ : Fin r) (hk₀ : j k₀ = c.j i₀) (cO : Γ((cU D).toScheme, OO D M W))
    (hcO : cO * ((N : Γ((cU D).toScheme, OO D M W)) * resU W uu) = 1) :
    letI := chartAlgebra (f := f) (D := D) M (W := W)
    IsUnit (genO M g₀ hW₂) ∧ ∃ ξ, ResForm (θO c M hW) (Fin.castLE c.hr i₀)
        (tW c hW (Fin.castLE c.hr i₀)) (Ni * (b k₀ : Γ(X, W))) ξ ∧
      δ ((cU D).ι ≫ f) (OO D M W) (genO M g₀ hW₂) -
          sm ((cU D).ι ≫ f) (OO D M W) cO * δ ((cU D).ι ≫ f) (OO D M W) (resU W uu) *
            sm ((cU D).ι ≫ f) (OO D M W) (genO M g₀ hW₂) =
        sm ((cU D).ι ≫ f) (OO D M W) (genO M g₀ hW₂) * ξ := by
  let _ := chartAlgebra (f := f) (D := D) M (W := W)
  classical
  obtain ⟨y₀, hy₀W, hy₀E⟩ := hE
  have : Nonempty (W : X.Opens) := ⟨⟨y₀, hy₀W⟩⟩
  set ρ₂ : Γ(X, W₂) →+* Γ(X, W) := (X.presheaf.map (homOfLE hW₂).op).hom
  set gg := genO M g₀ hW₂
  set uO := resU (D := D) (M := M) W uu
  set vO := ρ (D := D) M (ρ₂ v)
  set βO := ∏ k, ρ (D := D) M (ρ₂ (τ k)) ^ b k
  have hrelO : gg ^ N = uO * vO * βO := genO_pow_eq M hW₂ τ v g₀ b uu N hrel
  obtain ⟨ui, hui₀⟩ := (huu.map (((cU D).ι.app ((W : X.Opens) ⊓ cU' D M)).hom.comp
    (X.presheaf.map (homOfLE inf_le_right).op).hom)).exists_left_inv
  have hui : ui * uO = 1 := hui₀
  obtain ⟨vWi, hvWi⟩ := (hv.map ρ₂).exists_left_inv
  have hvi : ρ (D := D) M vWi * vO = 1 := by rw [← map_mul, hvWi, map_one]
  have hτW : ∀ k, (j k).idealSheaf.ideal W = Ideal.span {ρ₂ (τ k)} := fun k => by
    rw [← (j k).idealSheaf.map_ideal hW₂, hτ k, Ideal.map_span, Set.image_singleton]
    rfl
  choose s hs using fun k => (isUnit_ρ_of_ideal_eq M (hjD k) (hτW k)).exists_left_inv
  have hβ : (∏ k, s k ^ b k) * βO = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [← mul_pow, hs k, one_pow]
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hNi
  have hgu : IsUnit gg := by
    refine (isUnit_pow_iff hN0).mp ?_
    rw [hrelO]
    exact ((IsUnit.of_mul_eq_one_right _ hui).mul (IsUnit.of_mul_eq_one_right _ hvi)).mul
      (IsUnit.of_mul_eq_one_right _ hβ)
  refine ⟨hgu, ?_⟩
  obtain ⟨ggi, hggi⟩ := hgu.exists_left_inv
  have hN' : ρ (D := D) M Ni * (N : Γ((cU D).toScheme, OO D M W)) = 1 := by
    rw [← map_natCast (ρ (D := D) M), ← map_mul, hNi, map_one]
  have hc : cO = ρ (D := D) M Ni * ui :=
    left_inv_eq_right_inv hcO (by linear_combination (ui * uO) * hN' + hui)
  have key := dlog_twist_identity (g := (cU D).ι ≫ f) (O := OO D M W) N hui hvi hβ hggi hN' hc
    hrelO
  refine ⟨_, ?_, key⟩
  rw [dl_prod_pow (g := (cU D).ι ≫ f) (O := OO D M W) Finset.univ
    (fun k => ρ (D := D) M (ρ₂ (τ k))) s hs b, ← chartAlgebra_smul]
  refine ((ResForm.smul Ni ((resForm_dl_unit c M hW i₀.2 hvWi _ hvi).add
    (ResForm.sum Finset.univ (fun k => (b k : Γ(X, W)) * if j k = c.j i₀ then 1 else 0) _
      fun k _ => ?_))).congr_lam ?_)
  · rw [← Nat.cast_smul_eq_nsmul Γ(X, W)]
    exact ResForm.smul _ (resForm_dl c M hW i₀ ⟨y₀, hy₀W, hy₀E⟩ (hjD k) (hτW k) (s k) (hs k))
  · rw [zero_add, Finset.sum_eq_single k₀ (fun k _ hk => by
      rw [ite_eq_right (fun h => hk (hj (h.trans hk₀.symm))), mul_zero]) (by simp),
      ite_eq_left hk₀, mul_one]

omit [IsIntegral X] [SmoothOfRelativeDimension n f] in
/-- **Combinations are homogeneous sums of products of functions and exact forms.** -/
theorem mem_monSet_of_mem_F {q : ℕ} {x : (TB ((cU D).ι ≫ f)).Total (op (OO D M W))}
    (hx : x ∈ (letI := chartAlgebra (f := f) (D := D) M (W := W);
      ChartAlgebra.F (R := Γ(X, W)) (θO c M hW) q)) :
    x ∈ monSet ((cU D).ι ≫ f) (OO D M W) ∧
      (TB ((cU D).ι ≫ f)).incl (q : ℤ)
        ((TB ((cU D).ι ≫ f)).proj (op (OO D M W)) (q : ℤ) x) = x := by
  let _ := chartAlgebra (f := f) (D := D) M (W := W)
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, hK, rfl⟩ := hx
    refine ⟨θK_mem_monSet c M hW K, ?_⟩
    rw [θK_eq_mon]
    have hl : ((K.sort (· ≤ ·)).map (tO c M hW)).length = q := by
      rw [List.length_map, Finset.length_sort, hK]
    rw [← hl]
    exact incl_proj_mon _ _
  | zero =>
    refine ⟨zero_mem _, ?_⟩
    rw [map_zero, (TB ((cU D).ι ≫ f)).incl_zero]
  | add x y _ _ hx hy =>
    refine ⟨add_mem hx.1 hy.1, ?_⟩
    rw [map_add, (TB ((cU D).ι ≫ f)).incl_add, hx.2, hy.2]
  | smul a x _ hx =>
    rw [chartAlgebra_smul]
    refine ⟨mul_mem_monSet (sm_mem_monSet _) hx.1, ?_⟩
    have e : (TB ((cU D).ι ≫ f)).proj (op (OO D M W)) (q : ℤ)
        (sm ((cU D).ι ≫ f) (OO D M W) (ρ M a) * x) =
        (show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
          (op (OO D M W)) from ρ M a) • (TB ((cU D).ι ≫ f)).proj (op (OO D M W)) (q : ℤ) x :=
      (congrArg ((TB ((cU D).ι ≫ f)).proj (op (OO D M W)) (q : ℤ))
        (smul_eq_sm_mul _ x).symm).trans (LinearMap.map_smul _ _ _)
    rw [e, ← sm_mul_incl, hx.2]

omit [IsIntegral X] in
/-- **The connection on the chart**: if `N u ∇ω = N u dω - du ∧ ω` and `ω = g₀ z` with `z` a
homogeneous sum of products of functions and exact forms, and `dg₀ - (N u)⁻¹ du g₀ = g₀ ξ`, then
`∇ω = g₀ (ξ ∧ z + dz)`. -/
theorem incl_eq_sm_mul_nabla (N : ℕ) {uO cO gg : Γ((cU D).toScheme, OO D M W)}
    (hcO : cO * ((N : Γ((cU D).toScheme, OO D M W)) * uO) = 1)
    {ξ : (TB ((cU D).ι ≫ f)).Total (op (OO D M W))}
    (hξ : δ ((cU D).ι ≫ f) (OO D M W) gg -
        sm ((cU D).ι ≫ f) (OO D M W) cO * δ ((cU D).ι ≫ f) (OO D M W) uO *
          sm ((cU D).ι ≫ f) (OO D M W) gg = sm ((cU D).ι ≫ f) (OO D M W) gg * ξ)
    {q : ℕ}
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (q : ℤ)).val.obj
      (op (OO D M W)))
    (ω₁ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((q + 1 : ℕ) : ℤ)).val.obj (op (OO D M W)))
    {z : (TB ((cU D).ι ≫ f)).Total (op (OO D M W))} (hz : z ∈ monSet ((cU D).ι ≫ f) (OO D M W))
    (hzq : (TB ((cU D).ι ≫ f)).incl (q : ℤ)
      ((TB ((cU D).ι ≫ f)).proj (op (OO D M W)) (q : ℤ) z) = z)
    (hω : (TB ((cU D).ι ≫ f)).incl (q : ℤ) ω = sm ((cU D).ι ≫ f) (OO D M W) gg * z)
    (hd : N • (sm ((cU D).ι ≫ f) (OO D M W) uO *
        (TB ((cU D).ι ≫ f)).incl ((q + 1 : ℕ) : ℤ) ω₁) =
      N • (sm ((cU D).ι ≫ f) (OO D M W) uO * (TB ((cU D).ι ≫ f)).incl ((q + 1 : ℕ) : ℤ)
        (((Scheme.Hom.deRhamComplex ((cU D).ι ≫ f)).d q (q + 1)).val.app (op (OO D M W)) ω)) -
        δ ((cU D).ι ≫ f) (OO D M W) uO * (TB ((cU D).ι ≫ f)).incl (q : ℤ) ω) :
    (TB ((cU D).ι ≫ f)).incl ((q + 1 : ℕ) : ℤ) ω₁ =
      sm ((cU D).ι ≫ f) (OO D M W) gg * (ξ * z + Δ ((cU D).ι ≫ f) (OO D M W) q z) := by
  have hΔ : (TB ((cU D).ι ≫ f)).incl ((q + 1 : ℕ) : ℤ)
      (((Scheme.Hom.deRhamComplex ((cU D).ι ≫ f)).d q (q + 1)).val.app (op (OO D M W)) ω) =
      δ ((cU D).ι ≫ f) (OO D M W) gg * z +
        sm ((cU D).ι ≫ f) (OO D M W) gg * Δ ((cU D).ι ≫ f) (OO D M W) q z := by
    rw [← Δ_incl, hω, Δ_sm_mul q gg hz, hzq]
  have key : ∀ A : (TB ((cU D).ι ≫ f)).Total (op (OO D M W)),
      N • (sm ((cU D).ι ≫ f) (OO D M W) uO * A) =
        sm ((cU D).ι ≫ f) (OO D M W) ((N : Γ((cU D).toScheme, OO D M W)) * uO) * A := fun A => by
    rw [nsmul_eq_mul, map_mul, map_natCast, mul_assoc]
  have hu : IsUnit ((N : Γ((cU D).toScheme, OO D M W)) * uO) :=
    IsUnit.of_mul_eq_one_right cO hcO
  have h3 : N • (sm ((cU D).ι ≫ f) (OO D M W) uO *
      (sm ((cU D).ι ≫ f) (OO D M W) cO * δ ((cU D).ι ≫ f) (OO D M W) uO *
        sm ((cU D).ι ≫ f) (OO D M W) gg * z)) =
      δ ((cU D).ι ≫ f) (OO D M W) uO * (sm ((cU D).ι ≫ f) (OO D M W) gg * z) := by
    rw [key, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul, mul_comm _ cO, hcO, map_one,
      one_mul, mul_assoc]
  refine sm_cancel hu ?_
  rw [← key, ← key, hd, hΔ, hω, ← h3, ← smul_sub, ← mul_sub, mul_add, ← mul_assoc _ ξ, ← hξ]
  congr 2
  noncomm_ring

end TwistChartForms

end MMP.LcBpf
