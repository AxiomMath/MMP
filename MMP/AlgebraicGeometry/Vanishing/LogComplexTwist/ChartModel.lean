module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.ChartRepresentation

/-!
# Sections of a model of the fractional logarithmic complex on a chart

Let `K` be a model of `C^• = 𝒪_V(-M) · Ω^•_V(log D)`, and `U' = V ∖ (D ∪ Supp M)`. On an affine
open `W` inside a chart of `D`, with a generator `g₀` of `𝒪_V(-M)` on `W`, the sections of `K` over
`W` are, through the embedding into forms on `U ∩ W ∩ U'`, exactly the forms `g₀ ∑_K a_K θ_K` with
regular coefficients.

## Main definitions

* `MMP.LcBpf.TwistChartForms.encK`: the encoding of the sections of a model as forms on
  `U ∩ W ∩ U'`.

## Main results

* `MMP.LcBpf.TwistChartForms.encK_injective`: the encoding is injective.
* `MMP.LcBpf.TwistChartForms.exists_encK_eq`, `MMP.LcBpf.TwistChartForms.exists_encK_eq_lift`:
  the sections of `K`.
* `MMP.LcBpf.TwistChartForms.exists_incl_ι_eq_sm_mul_combo`: every form `g ∑_K a_K θ_K` is the
  image of a section of the model.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.Mori MMP.FourfoldProofs.FractionalLogComplexProof

namespace TwistChartForms

open MMP.Mori.Divisor.LogSpreadingProof.G1 (SNCChart LogData)

variable {n : ℕ} {V : Scheme.{0}} {π : V ⟶ Spec (CommRingCat.of ℂ)}
  [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
  {D : Divisor V} {hD : D.IsRelativeSNC n π} {M : Divisor V} {N : ℕ} {u : Γ(V, cU' D M)}
  {K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
  {F : ℕ → V.Modules}
  {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
  {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))}

omit [IsLocallyNoetherian V] [IsNormal V] in
/-- On sections over `W`, the hom of `e q` undoes its inverse. -/
theorem e_inv_hom (q : ℕ) (W : V.Opens) (x : (F q).val.obj (op W)) :
    (e q).hom.val.app (op W) ((e q).inv.val.app (op W) x) = x :=
  congrArg (fun φ => φ.val.app (op W) x) (e q).inv_hom_id

omit [IsLocallyNoetherian V] [IsNormal V] in
/-- On sections over `W`, the hom of `e q` is injective. -/
theorem e_hom_injective (q : ℕ) (W : V.Opens) :
    Function.Injective ((e q).hom.val.app (op W)) :=
  Function.LeftInverse.injective (g := (e q).inv.val.app (op W)) fun z =>
    congrArg (fun φ => φ.val.app (op W) z) (e q).hom_inv_id

variable (hK : IsCModel n π D hD 0 M N u K F e ι)

include hK

/-- The encoding of the sections of `K` over `W` as forms on `U ∩ W ∩ U'`. -/
noncomputable def encK (W : V.Opens) (q : ℕ) :
    (K.X q).val.obj (op W) →+ (TB ((cU D).ι ≫ π)).Total (op (OO D M W)) :=
  AddMonoidHom.mk' (fun x => (TB ((cU D).ι ≫ π)).incl (q : ℤ) (ι q W ((e q).hom.val.app (op W) x)))
    fun x y => by
      rw [map_add]
      exact (congrArg _ (hK.2.1 q W _ _)).trans ((TB ((cU D).ι ≫ π)).incl_add _ _ _)

/-- `encK hK W q x` is the form `ι q W (e q x)` in the total algebra. -/
@[simp]
theorem encK_apply (W : V.Opens) (q : ℕ) (x : (K.X q).val.obj (op W)) :
    encK hK W q x = (TB ((cU D).ι ≫ π)).incl (q : ℤ) (ι q W ((e q).hom.val.app (op W) x)) :=
  rfl

/-- The encoding `encK hK W q` is injective. -/
theorem encK_injective (W : V.Opens) (q : ℕ) : Function.Injective (encK hK W q) :=
  fun _ _ h => e_hom_injective q W (hK.1 q W (formsIncl_injective ((cU D).ι ≫ π) _ (q : ℤ) h))

/-- For `g` a section of `𝒪(-M)` over `W`, the form `g ∑_K a_K θ_K` on `U ∩ W ∩ U'` is
`ι q W x` for some section `x` of `F q` over `W`. -/
theorem exists_incl_ι_eq_sm_mul_combo {x₀ : V} (c : SNCChart n π D x₀) {W : V.affineOpens}
    (hW : (W : V.Opens) ≤ c.W) (g : Γ(V, (W : V.Opens) ⊓ cU' D M))
    (hg : DivCond (D := D) (M := M) (W : V.Opens) g) (q : ℕ)
    (a : {K : Finset (Fin n) // K.card = q} → Γ(V, W)) :
    ∃ x : (F q).val.obj (op (W : V.Opens)),
      (TB ((cU D).ι ≫ π)).incl (q : ℤ) (ι q W x) =
        sm ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g) *
          (letI := chartAlgebra (f := π) (D := D) M (W := W);
            ChartAlgebra.combo (θO c M hW) q a) := by
  obtain ⟨ω₀, hω₀⟩ := (⟨c.W, c.t, c.r, c.hr, c.s⟩ : LogData n π D).exists_incl_eq_combo q hW a
  have hmem : ω₀ ∈ Divisor.relativeLogForms n π D hD (0 : Divisor V).suppIdeal q W :=
    ((c.basis hD q hW).2.1 _ ω₀).2 ⟨a, fun K => by rw [suppIdeal_zero_ideal]; trivial, hω₀⟩
  let y₀ := ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (q : ℤ)).val.map
    (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
      (inf_le_left : (W : V.Opens) ⊓ cU' D M ≤ W))).op ω₀
  have hy₀ : (TB ((cU D).ι ≫ π)).incl (q : ℤ) y₀ =
      (letI := chartAlgebra (f := π) (D := D) M (W := W);
        ChartAlgebra.combo (θO c M hW) q a) := by
    change (TB ((cU D).ι ≫ π)).incl (q : ℤ) (((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((cU D).ι ≫ π)).piece (q : ℤ)).val.map _ ω₀) = _
    rw [incl_map π D]
    change (TB ((cU D).ι ≫ π)).totalRestrict _ ((TB ((cU D).ι ≫ π)).incl (q : ℤ) ω₀) = _
    rw [hω₀]
    exact totalRestrict_logCombo c M hW q a
  let ω := (show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
    (op (OO D M W)) from (cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g) • y₀
  have hω : (TB ((cU D).ι ≫ π)).incl (q : ℤ) ω =
      sm ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g) *
        (letI := chartAlgebra (f := π) (D := D) M (W := W);
          ChartAlgebra.combo (θO c M hW) q a) := by
    rw [← hy₀]
    exact (sm_mul_incl _ _ _).symm
  have hcond : Cond n π D hD 0 M q W ω := by
    intro y hy
    refine ⟨W, le_rfl, hy, 1, fun _ => g, fun _ => ω₀, fun _ => hg, fun _ => hmem, ?_⟩
    rw [Fin.sum_univ_one]
    refine (congrArg _ (piece_map_id
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (q : ℤ)).val _
      (show ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (q : ℤ)).val.obj
        (op (OO D M W)) from ω))).trans ?_
    change (TB ((cU D).ι ≫ π)).incl (q : ℤ) ω = _ * (TB ((cU D).ι ≫ π)).incl (q : ℤ) y₀
    exact (sm_mul_incl _ _ _).symm
  obtain ⟨x, hx⟩ := (hK.2.2.2.2.1 q W ω).2 hcond
  exact ⟨x, by rwa [hx]⟩

/-- **Every form `g₀ ∑_K a_K θ_K`**, `g₀` a section of `𝒪(-M)` over `W`, is `encK` of a section
of `K` over `W`. -/
theorem exists_encK_eq_lift {x₀ : V} (c : SNCChart n π D x₀) {W : V.affineOpens}
    (hW : (W : V.Opens) ≤ c.W) (g₀ : Γ(V, (W : V.Opens) ⊓ cU' D M))
    (hg₀ : DivCond (D := D) (M := M) (W : V.Opens) g₀) (q : ℕ)
    (a : {K : Finset (Fin n) // K.card = q} → Γ(V, W)) :
    ∃ y : (K.X q).val.obj (op (W : V.Opens)),
      encK hK W q y = sm ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g₀) *
        (letI := chartAlgebra (f := π) (D := D) M (W := W);
          ChartAlgebra.combo (θO c M hW) q a) := by
  obtain ⟨x, hx⟩ := exists_incl_ι_eq_sm_mul_combo hK c hW g₀ hg₀ q a
  exact ⟨(e q).inv.val.app (op (W : V.Opens)) x, by rw [encK_apply, e_inv_hom, hx]⟩

variable [IsIntegral V] [Nonempty (cU D)]

/-- **Sections of `K` on a chart** are `g₀ ∑_K a_K θ_K` with regular coefficients. -/
theorem exists_encK_eq {x₀ : V} (c : SNCChart n π D x₀) {W : V.affineOpens}
    (hW : (W : V.Opens) ≤ c.W) (g₀ : Γ(V, (W : V.Opens) ⊓ cU' D M))
    (hg₀ : IsUnit ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g₀))
    (hgen : ∀ (W₃ : V.Opens) (h₃ : W₃ ≤ W) (g' : Γ(V, W₃ ⊓ cU' D M)),
      DivCond (D := D) (M := M) W₃ g' → ∃ h : Γ(V, W₃),
        g' = V.presheaf.map (homOfLE inf_le_left).op h *
          V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g₀)
    (q : ℕ) (x : (K.X q).val.obj (op (W : V.Opens))) :
    ∃ a : {K : Finset (Fin n) // K.card = q} → Γ(V, W),
      encK hK W q x = sm ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app ((W : V.Opens) ⊓ cU' D M) g₀) *
        (letI := chartAlgebra (f := π) (D := D) M (W := W);
          ChartAlgebra.combo (θO c M hW) q a) :=
  exists_incl_eq_sm_mul_combo c M hD hW g₀ hg₀ hgen ((hK.2.2.2.2.1 q W _).1 ⟨_, rfl⟩)

end TwistChartForms

end MMP.LcBpf
