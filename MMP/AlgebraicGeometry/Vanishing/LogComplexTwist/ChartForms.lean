module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.ChartAlgebra
public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.DegreeZero
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.ChartHomogeneity
public import MMP.AlgebraicGeometry.DeRham.Logarithmic.SncPairSpreadingOut

/-!
# The forms of a logarithmic chart on `U ∩ W ∩ U'`

Let `X` be smooth of relative dimension `n` over a field, `D` a relative simple normal crossing
divisor with a chart `c` (coordinates `t₁, …, tₙ` on an affine open `c.W`, the first `r` of which
cut out components of `D`), `M` a divisor and `W ⊆ c.W` an affine open. On the open
`O = U ∩ W ∩ U'` (`U = X ∖ D`, `U' = X ∖ (D ∪ Supp M)`) the logarithmic coordinate forms are
`θᵢ = dtᵢ/tᵢ` (`i < r`) and `θᵢ = dtᵢ` (`i ≥ r`). The total ring of forms on `O` is an algebra over
the functions `Γ(X, W)`. The wedges `θ_K` are independent over `Γ(X, W)` when `X` is integral and
`W` non-empty, the differential of a function `a` on `W` is `∑ ∂ᵢa dtᵢ` with `∂ᵢa` regular on `W`,
and `d(a θ_K) = da ∧ θ_K`, since the `θᵢ` are closed.

## Main definitions

* `MMP.LcBpf.TwistChartForms.θO`: the logarithmic coordinate forms on `O`.
* `MMP.LcBpf.TwistChartForms.chartAlgebra`: the `Γ(X, W)`-algebra structure on the forms on `O`.

## Main results

* `MMP.LcBpf.TwistChartForms.eq_zero_of_combo_eq_zero`: independence of the wedges `θ_K`.
* `MMP.LcBpf.TwistChartForms.exists_δ_eq_sum`: the differential of a function in coordinates.
* `MMP.LcBpf.TwistChartForms.Δ_smul_θK`: `d(a θ_K) = da ∧ θ_K`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.Mori MMP.FourfoldProofs.FractionalLogComplexProof

universe u

namespace TwistChartForms

open MMP.Mori.Divisor.LogSpreadingProof.G1 (SNCChart logθ logCombo)

section Restriction

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} (n : ℕ)
  [SmoothOfRelativeDimension n f] {D : Divisor X} [IsIntegral X] [Nonempty (cU D)]

include n

/-- **Restriction of forms to a non-empty open is injective**, on an integral scheme smooth over a
field. -/
theorem piece_map_injective (q : ℕ) {O₁ O₂ : (cU D).toScheme.Opens} (h : O₂ ≤ O₁)
    (hne : (O₂ : Set (cU D).toScheme).Nonempty) :
    Function.Injective (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (q : ℤ)).val.map (homOfLE h).op) := by
  have : SmoothOfRelativeDimension n ((cU D).ι ≫ f) := by
    have h := (inferInstance : SmoothOfRelativeDimension (0 + n) ((cU D).ι ≫ f))
    rwa [zero_add] at h
  intro y y' hyy
  refine eq_of_ratTotal_eq ((cU D).ι ≫ f) (m := n) q y y' fun A hA _ => ?_
  obtain ⟨⟨a, ha⟩⟩ := ‹Nonempty (A : (cU D).toScheme.Opens)›
  obtain ⟨b, hbA, hbO⟩ := nonempty_preirreducible_inter (A : (cU D).toScheme.Opens).isOpen
    O₂.isOpen ⟨a, ha⟩ hne
  obtain ⟨B₀, hB₀, hbB, hBle⟩ := Opens.isBasis_iff_nbhd.mp (cU D).toScheme.isBasis_affineOpens
    (show b ∈ (A : (cU D).toScheme.Opens) ⊓ O₂ from ⟨hbA, hbO⟩)
  let B : (cU D).toScheme.affineOpens := ⟨B₀, hB₀⟩
  have : Nonempty (B : (cU D).toScheme.Opens) := ⟨⟨b, hbB⟩⟩
  have hBA : (B : (cU D).toScheme.Opens) ≤ A := hBle.trans inf_le_left
  have hBO : (B : (cU D).toScheme.Opens) ≤ O₂ := hBle.trans inf_le_right
  have key : ∀ z : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (q : ℤ)).val.obj (op O₁),
      ratTotal ((cU D).ι ≫ f) A ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hA).op
        ((TB ((cU D).ι ≫ f)).incl (q : ℤ) z)) =
      ratTotal ((cU D).ι ≫ f) B ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hBO).op
        ((TB ((cU D).ι ≫ f)).incl (q : ℤ)
          (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
            (q : ℤ)).val.map (homOfLE h).op z))) := fun z => by
    rw [← ratTotal_totalRestrict ((cU D).ι ≫ f) hBA,
      totalRestrict_totalRestrict _ _ (homOfLE (hBA.trans hA)).op, incl_map f D,
      totalRestrict_totalRestrict _ _ (homOfLE (hBA.trans hA)).op]
  rw [key, key, hyy]

end Restriction

section Algebra

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {D : Divisor X}
  (M : Divisor X) {W : X.affineOpens}

/-- The restriction of the functions on `W` to `O = U ∩ W ∩ U'`. -/
noncomputable def ρ : Γ(X, W) →+* Γ((cU D).toScheme, OO D M W) :=
  ((cU D).ι.app ((W : X.Opens) ⊓ cU' D M)).hom.comp
    (X.presheaf.map (homOfLE inf_le_left).op).hom

/-- The forms on `O` as an algebra over the functions on `W`. -/
@[instance_reducible]
noncomputable def chartAlgebra :
    Algebra Γ(X, W) ((TB ((cU D).ι ≫ f)).Total (op (OO D M W))) :=
  ((sm ((cU D).ι ≫ f) (OO D M W)).comp (ρ M)).toAlgebra' fun _ z => sm_comm _ z

/-- Scalar multiplication by a function `a` on `W` is multiplication by the restriction `ρ a`. -/
theorem chartAlgebra_smul (a : Γ(X, W)) (z : (TB ((cU D).ι ≫ f)).Total (op (OO D M W))) :
    (letI := chartAlgebra (f := f) (D := D) M (W := W); a • z) =
      sm ((cU D).ι ≫ f) (OO D M W) (ρ M a) * z := rfl

end Algebra

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n : ℕ}
  [SmoothOfRelativeDimension n f] {D : Divisor X} {x₀ : X} (c : SNCChart n f D x₀)
  (M : Divisor X) {W : X.affineOpens} (hW : (W : X.Opens) ≤ c.W)

omit [SmoothOfRelativeDimension n f] in
/-- The open `O = U ∩ W ∩ U'` lies in the preimage of the chart domain `c.W`. -/
theorem OO_le_preimage (hW : (W : X.Opens) ≤ c.W) : OO D M W ≤ (cU D).ι ⁻¹ᵁ (c.W : X.Opens) :=
  Scheme.Hom.preimage_mono _ (inf_le_left.trans hW)

/-- The restriction from `U ∩ c.W` to `O`. -/
noncomputable abbrev φO : op ((cU D).ι ⁻¹ᵁ (c.W : X.Opens)) ⟶ op (OO D M W) :=
  (homOfLE (OO_le_preimage c M hW)).op

/-- The coordinates on `O`. -/
noncomputable def tO (i : Fin n) : Γ((cU D).toScheme, OO D M W) :=
  (cU D).toScheme.presheaf.map (φO c M hW) ((cU D).ι.app c.W (c.t i))

/-- The coefficient of `dtᵢ` in `θᵢ` on `O`: `1/tᵢ` for `i < r`, `1` otherwise. -/
noncomputable def σO (i : Fin n) : Γ((cU D).toScheme, OO D M W) :=
  if h : (i : ℕ) < c.r then (cU D).toScheme.presheaf.map (φO c M hW) (c.s ⟨i, h⟩) else 1

/-- The logarithmic coordinate forms `θᵢ = σᵢ dtᵢ` on `O`. -/
noncomputable def θO (i : Fin n) : (TB ((cU D).ι ≫ f)).Total (op (OO D M W)) :=
  sm ((cU D).ι ≫ f) (OO D M W) (σO c M hW i) * δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW i)

/-- For `i < r`, the coefficient `σᵢ = 1/tᵢ` satisfies `σᵢ tᵢ = 1` on `O`. -/
theorem σO_mul_tO {i : Fin n} (h : (i : ℕ) < c.r) : σO c M hW i * tO c M hW i = 1 := by
  rw [σO, dite_eq_left h, tO, ← map_mul]
  have := c.hs ⟨i, h⟩
  rw [show Fin.castLE c.hr ⟨i, h⟩ = i from Fin.ext rfl] at this
  rw [this, map_one]

omit [SmoothOfRelativeDimension n f] in
/-- Each logarithmic coordinate form squares to zero: `θᵢ ∧ θᵢ = 0`. -/
theorem θO_mul_self (i : Fin n) : θO c M hW i * θO c M hW i = 0 := by
  unfold θO
  rw [mul_assoc, ← mul_assoc (δ _ _ _), ← sm_comm, mul_assoc, δ_mul_self, mul_zero, mul_zero]

omit [SmoothOfRelativeDimension n f] in
/-- The logarithmic coordinate forms anticommute: `θᵢ ∧ θⱼ = -(θⱼ ∧ θᵢ)`. -/
theorem θO_anticomm (i j : Fin n) :
    θO c M hW i * θO c M hW j = -(θO c M hW j * θO c M hW i) := by
  unfold θO
  rw [mul_assoc, ← mul_assoc (δ _ _ _), ← sm_comm, mul_assoc, δ_anticomm, mul_assoc,
    ← mul_assoc (δ _ _ (tO c M hW j)), ← sm_comm (c := σO c M hW i), mul_assoc]
  simp only [mul_neg, ← mul_assoc, ← map_mul, mul_comm (σO c M hW i)]

/-- The product `dσᵢ ∧ dtᵢ` vanishes on `O`. -/
theorem δ_σO_mul_δ_tO (i : Fin n) :
    δ ((cU D).ι ≫ f) (OO D M W) (σO c M hW i) * δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW i) = 0 := by
  by_cases h : (i : ℕ) < c.r
  · exact δ_mul_δ_of_mul_eq_one (σO_mul_tO c M hW h)
  · rw [σO, dite_eq_right h, δ_one, zero_mul]

/-- The coordinate `tᵢ` restricted to `W`. -/
noncomputable def tW (i : Fin n) : Γ(X, W) := X.presheaf.map (homOfLE hW).op (c.t i)

omit [SmoothOfRelativeDimension n f] in
/-- The coordinate `tᵢ` on `O` is the restriction of the coordinate `tᵢ` on `W`. -/
theorem tO_eq (i : Fin n) : tO c M hW i = ρ M (tW c hW i) := by
  rw [tO, ρ, tW, RingHom.comp_apply]
  refine (G1.app_restrict (inf_le_left.trans hW) (c.t i)).trans ?_
  exact congrArg _ (presheaf_map_map _ _ _ _).symm

/-- The factor `tᵢ` (`i < r`) or `1` (`i ≥ r`) with `dtᵢ = mᵢ θᵢ`. -/
noncomputable def mW (i : Fin n) : Γ(X, W) := if (i : ℕ) < c.r then tW c hW i else 1

/-- The differential of a coordinate in terms of the logarithmic forms: `dtᵢ = mᵢ θᵢ`. -/
theorem δ_tO_eq (i : Fin n) : δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW i) =
    sm ((cU D).ι ≫ f) (OO D M W) (ρ M (mW c hW i)) * θO c M hW i := by
  unfold θO mW
  by_cases h : (i : ℕ) < c.r
  · rw [ite_eq_left h, ← tO_eq, ← mul_assoc, ← map_mul, mul_comm, σO_mul_tO c M hW h, map_one,
      one_mul]
  · rw [ite_eq_right h, σO, dite_eq_right h, map_one, map_one, one_mul, one_mul]

omit [SmoothOfRelativeDimension n f] in
/-- The chart forms restrict to the forms `θO`. -/
theorem totalRestrict_logθ (i : Fin n) :
    (TB ((cU D).ι ≫ f)).totalRestrict (φO c M hW) (logθ (f := f) c.W c.t c.r c.s i) =
      θO c M hW i := by
  unfold logθ θO σO tO
  by_cases h : (i : ℕ) < c.r
  · rw [dite_eq_left h, dite_eq_left h, Stacks.GradedAlgebra.totalRestrict_mul,
      G1.totalRestrict_structureMap,
      MMP.Mori.Divisor.LogSpreadingProof.G1.totalRestrict_incl_dOne]
    rfl
  · rw [dite_eq_right h, dite_eq_right h,
      MMP.Mori.Divisor.LogSpreadingProof.G1.totalRestrict_incl_dOne, map_one, one_mul]
    rfl

omit [SmoothOfRelativeDimension n f] in
/-- The chart combinations, restricted to `O`. -/
theorem totalRestrict_logCombo (q : ℕ) (a : {K : Finset (Fin n) // K.card = q} → Γ(X, W)) :
    (TB ((cU D).ι ≫ f)).totalRestrict (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
        (inf_le_left : (W : X.Opens) ⊓ cU' D M ≤ W))).op
      (logCombo (f := f) c.W c.t c.r c.s q hW a) =
      (letI := chartAlgebra (f := f) (D := D) M (W := W); ChartAlgebra.combo (θO c M hW) q a) := by
  unfold logCombo ChartAlgebra.combo
  rw [map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Stacks.GradedAlgebra.totalRestrict_mul, chartAlgebra_smul]
  refine congrArg₂ (· * ·) ((totalRestrict_sm _ _).trans (congrArg _ ?_)) ?_
  · exact G1.app_restrict inf_le_left (a K)
  · rw [← (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply, map_list_prod, List.map_map]
    unfold ChartAlgebra.θK
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply]
    rw [totalRestrict_totalRestrict _ _ (φO c M hW)]
    exact totalRestrict_logθ c M hW i

section Independence

variable [IsIntegral X] [Nonempty (cU D)]

/-- **Independence of the wedges `θ_K`** over the functions on a non-empty `W`. -/
theorem eq_zero_of_combo_eq_zero (hD : D.IsRelativeSNC n f) {y : X} (hy : y ∈ (W : X.Opens)) (q : ℕ)
    (a : {K : Finset (Fin n) // K.card = q} → Γ(X, W))
    (ha : (letI := chartAlgebra (f := f) (D := D) M (W := W);
      ChartAlgebra.combo (θO c M hW) q a) = 0) :
    a = 0 := by
  obtain ⟨ω, hω⟩ := (c.toLogChart hD).toLogData.exists_incl_eq_combo q hW a
  have hne : ((OO D M W : (cU D).toScheme.Opens) : Set (cU D).toScheme).Nonempty := by
    obtain ⟨z, hzW, hzU⟩ := nonempty_preirreducible_inter (W : X.Opens).isOpen (cU' D M).isOpen
      ⟨y, hy⟩ ⟨_, componentGenericPoint_mem_cU' D M
        ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩⟩
    exact ⟨⟨z, (cU'_le_cU D M) hzU⟩, ⟨hzW, hzU⟩⟩
  have h1 : (TB ((cU D).ι ≫ f)).incl (q : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (q : ℤ)).val.map
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
          (inf_le_left : (W : X.Opens) ⊓ cU' D M ≤ W))).op ω) = 0 := by
    rw [incl_map f D]
    change (TB ((cU D).ι ≫ f)).totalRestrict _ ((TB ((cU D).ι ≫ f)).incl (q : ℤ) ω) = 0
    rw [hω]
    exact (totalRestrict_logCombo c M hW q a).trans ha
  have h2 : ω = 0 := by
    refine piece_map_injective (f := f) n q (Scheme.Hom.preimage_mono (cU D).ι
      (inf_le_left : (W : X.Opens) ⊓ cU' D M ≤ W)) hne ?_
    rw [map_zero]
    refine formsIncl_injective ((cU D).ι ≫ f) _ (q : ℤ) ?_
    exact h1.trans ((TB ((cU D).ι ≫ f)).incl_zero _).symm
  refine (c.basis hD q hW).1 ?_
  refine hω.symm.trans ?_
  rw [h2, (TB ((cU D).ι ≫ f)).incl_zero]
  unfold logCombo
  refine (Finset.sum_eq_zero fun K _ => ?_).symm
  rw [Pi.zero_apply, map_zero]
  exact (congrArg (· * _) (map_zero (sm ((cU D).ι ≫ f) ((cU D).ι ⁻¹ᵁ (W : X.Opens))))).trans
    (zero_mul _)

end Independence

section Differentials

/-- The restriction between affine opens is formally étale. -/
theorem formallyEtale_presheaf_map {W₁ W₂ : X.affineOpens} (h : (W₂ : X.Opens) ≤ W₁) :
    letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    Algebra.FormallyEtale Γ(X, W₁) Γ(X, W₂) := by
  have := HasRingHomProperty.appLE @Etale (𝟙 X) inferInstance W₁ W₂ h
  rw [MMP.Mori.Divisor.MmpRelativeLogFormsBasisProof.appLE_id] at this
  exact this.formallyEtale

omit [SmoothOfRelativeDimension n f] in
/-- **The differential of a function in the coordinates**, on `U ∩ W`: `d a = ∑ cᵢ dtᵢ` with `cᵢ`
regular on `W`. -/
theorem exists_δ_app_eq_sum (a : Γ(X, W)) :
    ∃ dc : Fin n → Γ(X, W),
      δ ((cU D).ι ≫ f) ((cU D).ι ⁻¹ᵁ (W : X.Opens)) ((cU D).ι.app W a) =
        ∑ i, sm ((cU D).ι ≫ f) ((cU D).ι ⁻¹ᵁ (W : X.Opens)) ((cU D).ι.app W (dc i)) *
          δ ((cU D).ι ≫ f) ((cU D).ι ⁻¹ᵁ (W : X.Opens)) ((cU D).ι.app W (tW c hW i)) := by
  have e₁ : (W : X.Opens) ≤ f ⁻¹ᵁ (c.V : (Spec (.of k)).Opens) := hW.trans c.e
  obtain ⟨b₂, hb₂⟩ := exists_basis_D_of_comp (f.appLE c.V c.W c.e).hom
    (X.presheaf.map (homOfLE hW).op).hom (f.appLE c.V W e₁).hom
    (by rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_map]) (formallyEtale_presheaf_map hW) c.t
    c.hb
  let _ := (f.appLE c.V W e₁).hom.toAlgebra
  let _ : Algebra Γ(X, W) Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens)) :=
    ((cU D).ι.app W).hom.toAlgebra
  have hle : (cU D).ι ⁻¹ᵁ (W : X.Opens) ≤ ((cU D).ι ≫ f) ⁻¹ᵁ (c.V : (Spec (.of k)).Opens) :=
    fun _ hy => e₁ hy
  let _ := (((cU D).ι ≫ f).appLE c.V ((cU D).ι ⁻¹ᵁ (W : X.Opens)) hle).hom.toAlgebra
  have : IsScalarTower Γ(Spec (.of k), c.V) Γ(X, W)
      Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens)) :=
    IsScalarTower.of_algebraMap_eq fun v => by
      change (((cU D).ι ≫ f).appLE c.V _ _).hom v =
        ((cU D).ι.app (W : X.Opens)).hom ((f.appLE c.V W e₁).hom v)
      rw [← Scheme.Hom.appLE_eq_app, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  let dc : Fin n → Γ(X, W) := fun i => b₂.repr (KaehlerDifferential.D _ _ a) i
  refine ⟨dc, ?_⟩
  have hD : KaehlerDifferential.D Γ(Spec (.of k), c.V) Γ(X, W) a =
      ∑ i, dc i • KaehlerDifferential.D Γ(Spec (.of k), c.V) Γ(X, W) (tW c hW i) := by
    conv_lhs => rw [← b₂.sum_repr (KaehlerDifferential.D _ _ a)]
    exact Finset.sum_congr rfl fun i _ => by rw [hb₂]; rfl
  have hD' := congrArg (KaehlerDifferential.map Γ(Spec (.of k), c.V) Γ(Spec (.of k), c.V) Γ(X, W)
    Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens))) hD
  rw [KaehlerDifferential.map_D, map_sum] at hD'
  simp only [map_smul, KaehlerDifferential.map_D] at hD'
  let L := Stacks.AlgebraicGeometry.AffineOpenDeRham.kaehlerSectionsLinearMap ((cU D).ι ≫ f) hle
  have hD'' : KaehlerDifferential.D Γ(Spec (.of k), c.V)
      Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens)) ((cU D).ι.app W a) =
      ∑ x, ((cU D).ι.app W).hom (dc x) • KaehlerDifferential.D Γ(Spec (.of k), c.V)
        Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens)) ((cU D).ι.app W (tW c hW x)) :=
    hD'.trans (Finset.sum_congr rfl fun x _ => (algebraMap_smul _ (dc x) _).symm)
  have hdd : (Scheme.Hom.universalRelativeDerivation ((cU D).ι ≫ f)).d (X := op _)
      ((cU D).ι.app W a) =
      ∑ x, (show (cU D).toScheme.ringCatSheaf.obj.obj (op ((cU D).ι ⁻¹ᵁ (W : X.Opens))) from
        ((cU D).ι.app W).hom (dc x)) •
          (Scheme.Hom.universalRelativeDerivation ((cU D).ι ≫ f)).d (X := op _)
            ((cU D).ι.app W (tW c hW x)) := by
    have h1 := (congrArg L hD'').trans ((map_sum L _ _).trans
      (Finset.sum_congr rfl fun x _ => L.map_smul _ _))
    refine (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections_d ((cU D).ι ≫ f) c.V _
      hle ((cU D).ι.app W a)).symm.trans (h1.trans ?_)
    exact Finset.sum_congr rfl fun x _ => congrArg _
      (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections_d ((cU D).ι ≫ f) c.V _
        hle _)
  refine (congrArg (ι1 ((cU D).ι ≫ f) _) hdd).trans ?_
  rw [ι1_sum]
  exact Finset.sum_congr rfl fun x _ => ι1_smul _ _

omit [SmoothOfRelativeDimension n f] in
/-- **The differential of a function in the coordinates**, on `O = U ∩ W ∩ U'`. -/
theorem exists_δ_eq_sum (a : Γ(X, W)) :
    ∃ dc : Fin n → Γ(X, W),
      δ ((cU D).ι ≫ f) (OO D M W) (ρ M a) =
        ∑ i, sm ((cU D).ι ≫ f) (OO D M W) (ρ M (dc i)) *
          δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW i) := by
  obtain ⟨dc, hdc⟩ := exists_δ_app_eq_sum c hW a
  refine ⟨dc, ?_⟩
  let ψ : op ((cU D).ι ⁻¹ᵁ (W : X.Opens)) ⟶ op (OO D M W) :=
    ((Opens.map (cU D).ι.base).map (homOfLE (inf_le_left : (W : X.Opens) ⊓ cU' D M ≤ W))).op
  have h := congrArg ((TB ((cU D).ι ≫ f)).totalRestrict ψ) hdc
  rw [totalRestrict_δ, map_sum] at h
  have e : ∀ b : Γ(X, W), (cU D).toScheme.presheaf.map ψ ((cU D).ι.app W b) = ρ M b :=
    fun b => G1.app_restrict inf_le_left b
  rw [e] at h
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [Stacks.GradedAlgebra.totalRestrict_mul, totalRestrict_sm, totalRestrict_δ, e, e,
    ← tO_eq]

/-- The logarithmic coordinate forms are closed: `d(∏ σᵢ) ∧ ∏ dtᵢ = 0`. -/
theorem δ_prod_σO_mul (l : List (Fin n)) :
    δ ((cU D).ι ≫ f) (OO D M W) ((l.map (σO c M hW)).prod) *
      (l.map fun i => δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW i)).prod = 0 := by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, δ_one, zero_mul]
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, δ_mul, add_mul]
    set P := (l.map (σO c M hW)).prod
    set Q := (l.map fun i => δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW i)).prod
    have h1 : sm ((cU D).ι ≫ f) (OO D M W) (σO c M hW a) * δ ((cU D).ι ≫ f) (OO D M W) P *
        (δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW a) * Q) = 0 := by
      rw [show sm ((cU D).ι ≫ f) (OO D M W) (σO c M hW a) * δ ((cU D).ι ≫ f) (OO D M W) P *
          (δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW a) * Q) =
          sm ((cU D).ι ≫ f) (OO D M W) (σO c M hW a) * ((δ ((cU D).ι ≫ f) (OO D M W) P *
            δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW a)) * Q) by simp only [mul_assoc],
        δ_anticomm, neg_mul, mul_assoc, ih, mul_zero, neg_zero, mul_zero]
    have h2 : sm ((cU D).ι ≫ f) (OO D M W) P * δ ((cU D).ι ≫ f) (OO D M W) (σO c M hW a) *
        (δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW a) * Q) = 0 := by
      rw [show sm ((cU D).ι ≫ f) (OO D M W) P * δ ((cU D).ι ≫ f) (OO D M W) (σO c M hW a) *
          (δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW a) * Q) =
          sm ((cU D).ι ≫ f) (OO D M W) P * ((δ ((cU D).ι ≫ f) (OO D M W) (σO c M hW a) *
            δ ((cU D).ι ≫ f) (OO D M W) (tO c M hW a)) * Q) by simp only [mul_assoc],
        δ_σO_mul_δ_tO, zero_mul, mul_zero]
    rw [h1, h2, add_zero]

omit [SmoothOfRelativeDimension n f] in
/-- The wedge `θ_K` is the monomial `(∏_{i ∈ K} σᵢ) ∧_{i ∈ K} dtᵢ`. -/
theorem θK_eq_mon (K : Finset (Fin n)) :
    ChartAlgebra.θK (θO c M hW) K = mon ((cU D).ι ≫ f) (OO D M W)
      ((K.sort (· ≤ ·)).map (σO c M hW)).prod ((K.sort (· ≤ ·)).map (tO c M hW)) := by
  unfold ChartAlgebra.θK mon
  rw [List.map_map]
  exact prod_map_sm_mul (g := (cU D).ι ≫ f) _ _ _

omit [SmoothOfRelativeDimension n f] in
/-- The wedge `θ_K` is a monomial form. -/
theorem θK_mem_monSet (K : Finset (Fin n)) :
    ChartAlgebra.θK (θO c M hW) K ∈ monSet ((cU D).ι ≫ f) (OO D M W) := by
  rw [θK_eq_mon]
  exact mon_mem_monSet _ _

/-- **The Leibniz rule on the wedges**: `d(a θ_K) = da ∧ θ_K`. -/
theorem Δ_smul_θK (q : ℕ) (a : Γ(X, W)) (K : Finset (Fin n)) (hK : K.card = q) :
    Δ ((cU D).ι ≫ f) (OO D M W) q
        (letI := chartAlgebra (f := f) (D := D) M (W := W); a • ChartAlgebra.θK (θO c M hW) K) =
      δ ((cU D).ι ≫ f) (OO D M W) (ρ M a) * ChartAlgebra.θK (θO c M hW) K := by
  rw [chartAlgebra_smul, θK_eq_mon]
  set b := ((K.sort (· ≤ ·)).map (σO c M hW)).prod
  set l := (K.sort (· ≤ ·)).map (tO c M hW)
  have e : sm ((cU D).ι ≫ f) (OO D M W) (ρ M a) * mon ((cU D).ι ≫ f) (OO D M W) b l =
      mon ((cU D).ι ≫ f) (OO D M W) (ρ M a * b) l := by
    simp only [mon, map_mul, mul_assoc]
  have hl : l.length = q := by rw [List.length_map, Finset.length_sort, hK]
  rw [e, Δ_mon, ite_eq_left hl]
  unfold dmon mon
  rw [δ_mul, add_mul]
  have h0 : δ ((cU D).ι ≫ f) (OO D M W) b * (l.map (δ ((cU D).ι ≫ f) (OO D M W))).prod = 0 := by
    simpa only [l, b, List.map_map, Function.comp_def] using δ_prod_σO_mul c M hW (K.sort (· ≤ ·))
  rw [mul_assoc, h0, mul_zero, zero_add, sm_comm b, mul_assoc]

/-- The differential of functions, as an additive map to the forms on `O`. -/
noncomputable def Dr : Γ(X, W) →+ (TB ((cU D).ι ≫ f)).Total (op (OO D M W)) where
  toFun a := δ ((cU D).ι ≫ f) (OO D M W) (ρ M a)
  map_zero' := by
    rw [map_zero]
    exact δ_zero'
  map_add' a b := by rw [map_add, δ_add]

/-- The map `Dr` sends `a` to the differential of its restriction `ρ a`. -/
theorem Dr_apply (a : Γ(X, W)) : Dr (f := f) (D := D) M a = δ ((cU D).ι ≫ f) (OO D M W) (ρ M a) :=
  rfl

/-- For `i₀ < r`, the differential of `a` is `a₀ + (tᵢ₀ a₁) θᵢ₀` with `a₀` in the span of the
`θᵢ`, `i ≠ i₀`. -/
theorem exists_Dr_eq {i₀ : Fin n} (hi₀ : (i₀ : ℕ) < c.r) (a : Γ(X, W)) :
    letI := chartAlgebra (f := f) (D := D) M (W := W)
    ∃ a₀ ∈ ChartAlgebra.L (R := Γ(X, W)) (θO c M hW) i₀ 1, ∃ a₁ : Γ(X, W),
      Dr (f := f) (D := D) M a = a₀ + (tW c hW i₀ * a₁) • θO c M hW i₀ := by
  let _ := chartAlgebra (f := f) (D := D) M (W := W)
  obtain ⟨dc, hdc⟩ := exists_δ_eq_sum c M hW a
  have hsum : Dr (f := f) (D := D) M a = ∑ i, (dc i * mW c hW i) • θO c M hW i := by
    rw [Dr_apply, hdc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [δ_tO_eq, chartAlgebra_smul, map_mul, map_mul, mul_assoc]
  refine ⟨∑ i ∈ Finset.univ.erase i₀, (dc i * mW c hW i) • θO c M hW i,
    sum_mem fun i hi => Submodule.smul_mem _ _ ?_, dc i₀, ?_⟩
  · rw [← ChartAlgebra.θK_singleton (θO c M hW) i]
    exact ChartAlgebra.θK_mem_L _ (Finset.card_singleton i)
      fun h => Finset.ne_of_mem_erase hi (Finset.mem_singleton.mp h).symm
  · rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), add_comm, mW, ite_eq_left hi₀,
      mul_comm]

omit [SmoothOfRelativeDimension n f] in
/-- `θᵢ ∧ d a = -(d a ∧ θᵢ)` for a function `a` on `W`. -/
theorem θO_mul_Dr (i₀ : Fin n) (a : Γ(X, W)) :
    θO c M hW i₀ * Dr (f := f) (D := D) M a = -(Dr (f := f) (D := D) M a * θO c M hW i₀) := by
  rw [Dr_apply]
  unfold θO
  rw [mul_assoc, δ_anticomm, mul_neg, ← mul_assoc, ← mul_assoc, ← sm_comm, mul_assoc]

end Differentials

end TwistChartForms

end MMP.LcBpf
