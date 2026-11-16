module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.ChartForms

/-!
# Sections of `𝒪_X(-M) · Ω^q_X(log D)` on a chart

Let `W` be an affine open inside a chart `c` of the relative simple normal crossing divisor `D`
on an integral scheme `X` smooth over a field, and `g₀` a generator of `𝒪_X(-M)` on every open of
`W`, invertible on `O = U ∩ W ∩ U'`. A form `ω` on `O` which is, locally on `W`, a sum `∑ gᵢ ηᵢ`
of sections `gᵢ` of `𝒪_X(-M)` times logarithmic forms `ηᵢ` is `g₀ ∑_K a_K θ_K` with coefficients
`a_K` regular on all of `W`: locally `gᵢ = hᵢ g₀` and `ηᵢ = ∑_K cᵢ_K θ_K`, the local coefficients
agree on overlaps by independence of the `θ_K`, and glue.

## Main results

* `MMP.LcBpf.TwistChartForms.totalRestrict_combo`: combinations restrict to combinations.
* `MMP.LcBpf.TwistChartForms.coeff_inf_eq`: coefficients of local representations agree on
  overlaps.
* `MMP.LcBpf.TwistChartForms.exists_local_incl_eq_sm_mul_combo`: local representations exist.
* `MMP.LcBpf.TwistChartForms.exists_incl_eq_sm_mul_combo`: the global representation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.Mori MMP.FourfoldProofs.FractionalLogComplexProof

universe u

namespace TwistChartForms

open MMP.Mori.Divisor.LogSpreadingProof.G1 (SNCChart logθ logCombo LogData)

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n : ℕ}
  [SmoothOfRelativeDimension n f] {D : Divisor X} {x₀ : X} (c : SNCChart n f D x₀)
  (M : Divisor X)

/-- The open `OO D M W` is monotone in `W`. -/
theorem OO_mono {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁) : OO D M W₂ ≤ OO D M W₁ :=
  Scheme.Hom.preimage_mono _ (inf_le_inf_right _ h)

/-- **Combinations restrict to combinations.** -/
theorem totalRestrict_combo {W₁ W₂ : X.affineOpens} (h₁ : (W₁ : X.Opens) ≤ c.W)
    (h : (W₂ : X.Opens) ≤ W₁) (q : ℕ) (a : {K : Finset (Fin n) // K.card = q} → Γ(X, W₁)) :
    (TB ((cU D).ι ≫ f)).totalRestrict (homOfLE (OO_mono M h)).op
        (letI := chartAlgebra (f := f) (D := D) M (W := W₁);
          ChartAlgebra.combo (θO c M h₁) q a) =
      (letI := chartAlgebra (f := f) (D := D) M (W := W₂);
        ChartAlgebra.combo (θO c M (h.trans h₁)) q
          (fun K => X.presheaf.map (homOfLE h).op (a K))) := by
  rw [← totalRestrict_logCombo c M h₁ q a, ← totalRestrict_logCombo c M (h.trans h₁) q]
  change _ = (TB ((cU D).ι ≫ f)).totalRestrict _ (logCombo (f := f) c.W c.t c.r c.s q
    (h.trans h₁) fun K => X.presheaf.map (homOfLE h).op (a K))
  rw [← show (TB ((cU D).ι ≫ f)).totalRestrict
      ((Opens.map (cU D).ι.base).map (homOfLE h)).op (logCombo (f := f) c.W c.t c.r c.s q h₁ a) =
      logCombo (f := f) c.W c.t c.r c.s q (h.trans h₁)
        (fun K => X.presheaf.map (homOfLE h).op (a K)) from
      (⟨c.W, c.t, c.r, c.hr, c.s⟩ : LogData n f D).totalRestrict_combo q h₁ h a,
    totalRestrict_totalRestrict _ _ (homOfLE ((OO_mono M h).trans
      (Scheme.Hom.preimage_mono (cU D).ι inf_le_left))).op,
    totalRestrict_totalRestrict _ _ (homOfLE ((OO_mono M h).trans
      (Scheme.Hom.preimage_mono (cU D).ι inf_le_left))).op]

/-- The generator restricted to `U ∩ W₂ ∩ U'`. -/
noncomputable abbrev genO {W₁ : X.Opens} (g : Γ(X, W₁ ⊓ cU' D M)) {W₂ : X.Opens} (h : W₂ ≤ W₁) :
    Γ((cU D).toScheme, OO D M W₂) :=
  (cU D).ι.app (W₂ ⊓ cU' D M) (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h)).op g)

/-- Restricting multiplication by `g` on `OO D M W₁` to `OO D M W₂` gives multiplication by
`genO M g h`. -/
theorem totalRestrict_sm_app {W₁ : X.Opens} (g : Γ(X, W₁ ⊓ cU' D M)) {W₂ : X.Opens}
    (h : W₂ ≤ W₁) :
    (TB ((cU D).ι ≫ f)).totalRestrict (homOfLE (OO_mono M h)).op
        (sm ((cU D).ι ≫ f) (OO D M W₁) ((cU D).ι.app (W₁ ⊓ cU' D M) g)) =
      sm ((cU D).ι ≫ f) (OO D M W₂) (genO M g h) := by
  rw [totalRestrict_sm]
  exact congrArg _ (G1.app_restrict (inf_le_inf_right (cU' D M) h) g)

/-- Restricting multiplication by the generator `genO M g h` on `OO D M W₂` to `OO D M W₃` gives
multiplication by the generator `genO M g (h'.trans h)`. -/
theorem totalRestrict_sm_genO {W₁ : X.Opens} (g : Γ(X, W₁ ⊓ cU' D M)) {W₂ W₃ : X.Opens}
    (h : W₂ ≤ W₁) (h' : W₃ ≤ W₂) :
    (TB ((cU D).ι ≫ f)).totalRestrict (homOfLE (OO_mono M h')).op
        (sm ((cU D).ι ≫ f) (OO D M W₂) (genO M g h)) =
      sm ((cU D).ι ≫ f) (OO D M W₃) (genO M g (h'.trans h)) := by
  rw [totalRestrict_sm]
  exact congrArg _ ((G1.app_restrict (inf_le_inf_right (cU' D M) h') _).trans
    (congrArg _ (presheaf_map_map _ _ _ _)))

/-- If `g` is a unit on `U ∩ W₁ ∩ U'`, then its restriction `genO M g h` to `U ∩ W₂ ∩ U'` is a
unit. -/
theorem isUnit_genO {W₁ : X.Opens} {g : Γ(X, W₁ ⊓ cU' D M)} {W₂ : X.Opens} (h : W₂ ≤ W₁)
    (hg : IsUnit ((cU D).ι.app (W₁ ⊓ cU' D M) g)) : IsUnit (genO M g h) := by
  have e : genO M g h = (cU D).toScheme.presheaf.map (homOfLE (OO_mono M h)).op
      ((cU D).ι.app (W₁ ⊓ cU' D M) g) := (G1.app_restrict (inf_le_inf_right (cU' D M) h) g).symm
  rw [e]
  exact hg.map ((cU D).toScheme.presheaf.map (homOfLE (OO_mono M h)).op).hom

/-- Left multiplication by the image `sm _ O G` of a unit `G` in the total algebra is
cancellable. -/
theorem sm_cancel {O : (cU D).toScheme.Opens} {G : Γ((cU D).toScheme, O)} (hG : IsUnit G)
    {z z' : (TB ((cU D).ι ≫ f)).Total (op O)}
    (h : sm ((cU D).ι ≫ f) O G * z = sm ((cU D).ι ≫ f) O G * z') : z = z' :=
  (hG.map (sm ((cU D).ι ≫ f) O)).mul_left_cancel h

variable [IsIntegral X] [Nonempty (cU D)] (hD : D.IsRelativeSNC n f)

include hD in
/-- **Uniqueness of the coefficients**: the coefficients of two representations of the same form on
affine opens `W₁, W₂ ≤ W` agree after restriction to any affine open `A ≤ W₁ ⊓ W₂` containing a
point. -/
theorem coeff_restrict_eq {W W₁ W₂ A : X.affineOpens} (hW : (W : X.Opens) ≤ c.W)
    (h₁ : (W₁ : X.Opens) ≤ W) (h₂ : (W₂ : X.Opens) ≤ W) (hA₁ : (A : X.Opens) ≤ W₁)
    (hA₂ : (A : X.Opens) ≤ W₂) {z : X} (hz : z ∈ (A : X.Opens)) (g : Γ(X, (W : X.Opens) ⊓ cU' D M))
    (hg : IsUnit ((cU D).ι.app ((W : X.Opens) ⊓ cU' D M) g)) {q : ℕ}
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (q : ℤ)).val.obj
      (op (OO D M W)))
    (e₁ : {K : Finset (Fin n) // K.card = q} → Γ(X, W₁))
    (e₂ : {K : Finset (Fin n) // K.card = q} → Γ(X, W₂))
    (he₁ : (TB ((cU D).ι ≫ f)).incl (q : ℤ) (rO f (D := D) (M := M) (q : ℤ) h₁ ω) =
      sm ((cU D).ι ≫ f) (OO D M W₁) (genO M g h₁) *
        (letI := chartAlgebra (f := f) (D := D) M (W := W₁);
          ChartAlgebra.combo (θO c M (h₁.trans hW)) q e₁))
    (he₂ : (TB ((cU D).ι ≫ f)).incl (q : ℤ) (rO f (D := D) (M := M) (q : ℤ) h₂ ω) =
      sm ((cU D).ι ≫ f) (OO D M W₂) (genO M g h₂) *
        (letI := chartAlgebra (f := f) (D := D) M (W := W₂);
          ChartAlgebra.combo (θO c M (h₂.trans hW)) q e₂)) :
    (fun K => X.presheaf.map (homOfLE hA₁).op (e₁ K)) =
      (fun K => X.presheaf.map (homOfLE hA₂).op (e₂ K)) := by
  let _ := chartAlgebra (f := f) (D := D) M (W := A)
  have r₁ := congrArg ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE (OO_mono M hA₁)).op) he₁
  have r₂ := congrArg ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE (OO_mono M hA₂)).op) he₂
  rw [Stacks.GradedAlgebra.totalRestrict_mul, totalRestrict_sm_genO M g h₁ hA₁,
    totalRestrict_combo c M (h₁.trans hW) hA₁, ← incl_map f D] at r₁
  rw [Stacks.GradedAlgebra.totalRestrict_mul, totalRestrict_sm_genO M g h₂ hA₂,
    totalRestrict_combo c M (h₂.trans hW) hA₂, ← incl_map f D] at r₂
  rw [show ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (q : ℤ)).val.map
      (homOfLE (OO_mono M hA₁)).op (rO f (D := D) (M := M) (q : ℤ) h₁ ω) =
      rO f (D := D) (M := M) (q : ℤ) (hA₁.trans h₁) ω from
        rO_rO f (D := D) (M := M) (q : ℤ) h₁ hA₁ ω] at r₁
  rw [show ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (q : ℤ)).val.map
      (homOfLE (OO_mono M hA₂)).op (rO f (D := D) (M := M) (q : ℤ) h₂ ω) =
      rO f (D := D) (M := M) (q : ℤ) (hA₂.trans h₂) ω from
        rO_rO f (D := D) (M := M) (q : ℤ) h₂ hA₂ ω] at r₂
  have hcomb := sm_cancel (isUnit_genO M _ hg) (r₁.symm.trans r₂)
  rw [← sub_eq_zero, ← ChartAlgebra.combo_sub] at hcomb
  exact sub_eq_zero.mp (eq_zero_of_combo_eq_zero c M (hA₁.trans (h₁.trans hW)) hD hz q _ hcomb)

include hD in
/-- **Compatibility of the coefficients**: two representations on affine opens `W₁, W₂ ≤ W` have
coefficients agreeing on `W₁ ⊓ W₂`. -/
theorem coeff_inf_eq {W W₁ W₂ : X.affineOpens} (hW : (W : X.Opens) ≤ c.W)
    (h₁ : (W₁ : X.Opens) ≤ W) (h₂ : (W₂ : X.Opens) ≤ W) (g : Γ(X, (W : X.Opens) ⊓ cU' D M))
    (hg : IsUnit ((cU D).ι.app ((W : X.Opens) ⊓ cU' D M) g)) {q : ℕ}
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (q : ℤ)).val.obj
      (op (OO D M W)))
    (e₁ : {K : Finset (Fin n) // K.card = q} → Γ(X, W₁))
    (e₂ : {K : Finset (Fin n) // K.card = q} → Γ(X, W₂))
    (he₁ : (TB ((cU D).ι ≫ f)).incl (q : ℤ) (rO f (D := D) (M := M) (q : ℤ) h₁ ω) =
      sm ((cU D).ι ≫ f) (OO D M W₁) (genO M g h₁) *
        (letI := chartAlgebra (f := f) (D := D) M (W := W₁);
          ChartAlgebra.combo (θO c M (h₁.trans hW)) q e₁))
    (he₂ : (TB ((cU D).ι ≫ f)).incl (q : ℤ) (rO f (D := D) (M := M) (q : ℤ) h₂ ω) =
      sm ((cU D).ι ≫ f) (OO D M W₂) (genO M g h₂) *
        (letI := chartAlgebra (f := f) (D := D) M (W := W₂);
          ChartAlgebra.combo (θO c M (h₂.trans hW)) q e₂))
    (K : {K : Finset (Fin n) // K.card = q}) :
    X.presheaf.map (homOfLE inf_le_left : (W₁ : X.Opens) ⊓ W₂ ⟶ W₁).op (e₁ K) =
      X.presheaf.map (homOfLE inf_le_right : (W₁ : X.Opens) ⊓ W₂ ⟶ W₂).op (e₂ K) := by
  choose A hA hzA hAle using fun (z : X) (hz : z ∈ (W₁ : X.Opens) ⊓ W₂) =>
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hz
  let A' : {z : X // z ∈ (W₁ : X.Opens) ⊓ W₂} → X.affineOpens := fun z => ⟨A z.1 z.2, hA z.1 z.2⟩
  refine MMP.Mori.Divisor.LogSpreadingProof.G1.eq_of_cover
    (fun z => (A' z : X.Opens)) (fun z => hAle z.1 z.2)
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzA z hz⟩) fun z => ?_
  rw [presheaf_map_map _ _ (homOfLE ((hAle z.1 z.2).trans inf_le_left)).op,
    presheaf_map_map _ _ (homOfLE ((hAle z.1 z.2).trans inf_le_right)).op]
  exact congrFun (coeff_restrict_eq c M hD hW (A := A' z) h₁ h₂ ((hAle z.1 z.2).trans inf_le_left)
    ((hAle z.1 z.2).trans inf_le_right) (hzA z.1 z.2) g hg ω e₁ e₂ he₁ he₂) K

variable [IsLocallyNoetherian X] [IsNormal X]

omit [IsIntegral X] [Nonempty (cU D)] in
/-- **Local representations on the chart.** Every point `y` of `W` has an affine neighbourhood
`W₁ ≤ W` on which a form satisfying `Cond` is `g₀ ∑_K e_K θ_K` with coefficients regular on `W₁`. -/
theorem exists_local_incl_eq_sm_mul_combo {W : X.affineOpens} (hW : (W : X.Opens) ≤ c.W)
    (g : Γ(X, (W : X.Opens) ⊓ cU' D M))
    (hgen : ∀ (W₃ : X.Opens) (h₃ : W₃ ≤ W) (g' : Γ(X, W₃ ⊓ cU' D M)),
      DivCond (D := D) (M := M) W₃ g' → ∃ h : Γ(X, W₃),
        g' = X.presheaf.map (homOfLE inf_le_left).op h *
          X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g)
    {q : ℕ} {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (q : ℤ)).val.obj (op (OO D M W))}
    (hω : Cond n f D hD 0 M q W ω) {y : X} (hy : y ∈ (W : X.Opens)) :
    ∃ (W₁ : X.affineOpens) (h₁ : (W₁ : X.Opens) ≤ W), y ∈ (W₁ : X.Opens) ∧
      ∃ e : {K : Finset (Fin n) // K.card = q} → Γ(X, W₁),
        (TB ((cU D).ι ≫ f)).incl (q : ℤ) (rO f (D := D) (M := M) (q : ℤ) h₁ ω) =
          sm ((cU D).ι ≫ f) (OO D M W₁) (genO M g h₁) *
            (letI := chartAlgebra (f := f) (D := D) M (W := W₁);
              ChartAlgebra.combo (θO c M (h₁.trans hW)) q e) := by
  classical
  obtain ⟨W₁, h₁, hy₁, m, gs, η, hgs, hη, he⟩ := hω y hy
  let _ := chartAlgebra (f := f) (D := D) M (W := W₁)
  choose cη hcη using fun i => ((c.basis hD q (h₁.trans hW)).2.1 _ (η i)).1 (hη i)
  choose hh hhe using fun i => hgen W₁ h₁ (gs i) (hgs i)
  refine ⟨W₁, h₁, hy₁, ∑ i, hh i • cη i, ?_⟩
  rw [ChartAlgebra.combo_sum_smul, Finset.mul_sum]
  refine he.trans (Finset.sum_congr rfl fun i _ => ?_)
  have h1 : (TB ((cU D).ι ≫ f)).incl (q : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (q : ℤ)).val.map
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
          (inf_le_left : (W₁ : X.Opens) ⊓ cU' D M ≤ W₁))).op (η i)) =
      ChartAlgebra.combo (θO c M (h₁.trans hW)) q (cη i) := by
    rw [incl_map f D, (hcη i).2]
    exact totalRestrict_logCombo c M (h₁.trans hW) q (cη i)
  rw [h1, hhe i, chartAlgebra_smul]
  change sm ((cU D).ι ≫ f) (OO D M W₁) ((cU D).ι.app ((W₁ : X.Opens) ⊓ cU' D M)
      (X.presheaf.map (homOfLE inf_le_left).op (hh i) * X.presheaf.map
        (homOfLE (inf_le_inf_right (cU' D M) h₁)).op g)) * _ = _
  simp only [map_mul]
  rw [← mul_assoc]
  congr 1
  exact (map_mul _ _ _).symm.trans ((congrArg _ (mul_comm _ _)).trans (map_mul _ _ _))

/-- **The global representation on the chart.** A form satisfying `Cond` on `W` is
`g₀ ∑_K e_K θ_K` with coefficients regular on `W`. -/
theorem exists_incl_eq_sm_mul_combo {W : X.affineOpens} (hW : (W : X.Opens) ≤ c.W)
    (g : Γ(X, (W : X.Opens) ⊓ cU' D M))
    (hg : IsUnit ((cU D).ι.app ((W : X.Opens) ⊓ cU' D M) g))
    (hgen : ∀ (W₃ : X.Opens) (h₃ : W₃ ≤ W) (g' : Γ(X, W₃ ⊓ cU' D M)),
      DivCond (D := D) (M := M) W₃ g' → ∃ h : Γ(X, W₃),
        g' = X.presheaf.map (homOfLE inf_le_left).op h *
          X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g)
    {q : ℕ} {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (q : ℤ)).val.obj (op (OO D M W))}
    (hω : Cond n f D hD 0 M q W ω) :
    ∃ e : {K : Finset (Fin n) // K.card = q} → Γ(X, W),
      (TB ((cU D).ι ≫ f)).incl (q : ℤ) ω =
        sm ((cU D).ι ≫ f) (OO D M W) ((cU D).ι.app ((W : X.Opens) ⊓ cU' D M) g) *
          (letI := chartAlgebra (f := f) (D := D) M (W := W);
            ChartAlgebra.combo (θO c M hW) q e) := by
  classical
  let _ := chartAlgebra (f := f) (D := D) M (W := W)
  choose W₁ h₁ hy₁ e he using fun (y : X) (hy : y ∈ (W : X.Opens)) =>
    exists_local_incl_eq_sm_mul_combo c M hD hW g hgen hω hy
  let V : {y : X // y ∈ (W : X.Opens)} → X.Opens := fun y => (W₁ y.1 y.2 : X.Opens)
  have hV : ∀ y, V y ≤ W := fun y => h₁ y.1 y.2
  have hcov : (W : X.Opens) ≤ ⨆ y, V y := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hy₁ y hy⟩
  choose eg heg using fun K =>
    MMP.Mori.Divisor.LogSpreadingProof.G1.exists_glue_of_cover V hV hcov
      (fun y => e y.1 y.2 K) fun i j => coeff_inf_eq c M hD hW (h₁ i.1 i.2) (h₁ j.1 j.2) g hg ω
        (e i.1 i.2) (e j.1 j.2) (he i.1 i.2) (he j.1 j.2) K
  refine ⟨eg, ?_⟩
  obtain ⟨ω₀, hω₀⟩ := (⟨c.W, c.t, c.r, c.hr, c.s⟩ : LogData n f D).exists_incl_eq_combo q hW eg
  let z₀ := ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (q : ℤ)).val.map
    (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
      (inf_le_left : (W : X.Opens) ⊓ cU' D M ≤ W))).op ω₀
  have hz₀ : (TB ((cU D).ι ≫ f)).incl (q : ℤ) z₀ = ChartAlgebra.combo (θO c M hW) q eg := by
    change (TB ((cU D).ι ≫ f)).incl (q : ℤ) (((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU D).ι ≫ f)).piece (q : ℤ)).val.map _ ω₀) = _
    rw [incl_map f D]
    change (TB ((cU D).ι ≫ f)).totalRestrict _ ((TB ((cU D).ι ≫ f)).incl (q : ℤ) ω₀) = _
    rw [hω₀]
    exact totalRestrict_logCombo c M hW q eg
  rw [← hz₀]
  refine Eq.trans ?_ (sm_mul_incl _ _ _).symm
  congr 1
  refine piece_ext (g := (cU D).ι ≫ f) (q : ℤ) (fun y => OO D M (V y))
    (fun y => homOfLE (OO_mono M (hV y))) (fun p hp => ?_) _ _ fun y => ?_
  · exact Opens.mem_iSup.2 ⟨⟨(cU D).ι p, hp.1⟩, ⟨hy₁ _ hp.1, hp.2⟩⟩
  · refine formsIncl_injective ((cU D).ι ≫ f) _ (q : ℤ) ?_
    beta_reduce
    change (TB ((cU D).ι ≫ f)).incl (q : ℤ) (rO f (D := D) (M := M) (q : ℤ) (hV y) ω) = _
    rw [he y.1 y.2, incl_map f D]
    refine Eq.trans ?_ (congrArg _ (sm_mul_incl _ _ z₀))
    rw [Stacks.GradedAlgebra.totalRestrict_mul, totalRestrict_sm_app M g (hV y), hz₀,
      totalRestrict_combo c M hW (hV y)]
    congr 2
    funext K
    exact (heg K y).symm

end TwistChartForms

end MMP.LcBpf
