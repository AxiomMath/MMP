module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.ChartCombination
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Construction

/-!
# The rational form of a logarithmic form on a chart

Let `W` be a chart of the relative simple normal crossing divisor `D` with coordinates `tᵢ`, the
first `r` of them local equations of components of `D`, and `θᵢ = dtᵢ / tᵢ` (`i < r`), `θᵢ = dtᵢ`
(`i ≥ r`) the chart basis of the logarithmic `1`-forms. A form `ω` on `W' ∖ D`, `W' ⊆ W`, equal to
the combination `∑_K c_K θ_K` has, on every non-empty affine open `O ⊆ W' ∖ D`, the rational form
`∑_K c_K β_K`, where `β_K` is the wedge of the rational forms `tᵢ⁻¹ dtᵢ`, resp. `dtᵢ`, over the
`i ∈ K` in increasing order.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.ratTotal_eq_sum_of_incl_eq_combo`: the rational form,
  in the exterior algebra.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratForm_eq_sum_ιMulti_of_incl_eq_combo`: the rational
  form, as a `p`-form.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **The rational form of a combination of the chart basis**, in the exterior algebra: if `ω`
equals `∑_K c_K θ_K` in the chart basis, then its total rational form on `O` is `∑_K c_K β_K`. -/
theorem ratTotal_eq_sum_of_incl_eq_combo [IsIntegral X] (f : X ⟶ Spec (.of k))
    (D : MMP.Mori.Divisor X) [Nonempty (cU D)] {n : ℕ} (W : X.affineOpens)
    (t : Fin n → Γ(X, W)) {r : ℕ} (hr : r ≤ n)
    (s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens)))
    (hs : ∀ i, s i * (cU D).ι.app W (t (Fin.castLE hr i)) = 1)
    (θ : Fin n → (TB ((cU D).ι ≫ f)).Total (op ((cU D).ι ⁻¹ᵁ (W : X.Opens))))
    (hθ : θ = fun i : Fin n => if h : (i : ℕ) < r then
        sm ((cU D).ι ≫ f) _ (s ⟨i, h⟩) * δ ((cU D).ι ≫ f) _ ((cU D).ι.app W (t i))
      else δ ((cU D).ι ≫ f) _ ((cU D).ι.app W (t i)))
    (p : ℕ) (W' : X.affineOpens) (hW' : (W' : X.Opens) ≤ W)
    (c : {K : Finset (Fin n) // K.card = p} → Γ(X, W'))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ (W' : X.Opens))))
    (hω : (TB ((cU D).ι ≫ f)).incl (p : ℤ) ω =
      ∑ K, sm ((cU D).ι ≫ f) _ (((cU D).ι.app W').hom (c K)) *
        ((K.1.sort (· ≤ ·)).map fun i =>
          (TB ((cU D).ι ≫ f)).totalRestrict
            ((Opens.map (cU D).ι.base).map (homOfLE hW')).op (θ i)).prod)
    (O : (cU D).toScheme.affineOpens)
    (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W' : X.Opens))
    [Nonempty (O : (cU D).toScheme.Opens)] :
    letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
        ((TB ((cU D).ι ≫ f)).incl (p : ℤ) ω)) =
      ∑ K, algebraMap (cU D).toScheme.functionField
          (ExteriorAlgebra (cU D).toScheme.functionField Ω[(cU D).toScheme.functionField⁄k])
          ((cU D).toScheme.germToFunctionField O
            ((cU D).toScheme.presheaf.map (homOfLE hO).op (((cU D).ι.app W').hom (c K)))) *
        ((K.1.sort (· ≤ ·)).map fun i : Fin n =>
          ExteriorAlgebra.ι (cU D).toScheme.functionField
            (if (i : ℕ) < r then
              ((cU D).toScheme.germToFunctionField O
                ((cU D).toScheme.presheaf.map
                  (homOfLE (hO.trans (Scheme.Hom.preimage_mono _ hW'))).op
                  ((cU D).ι.app W (t i))))⁻¹ •
                KaehlerDifferential.D k (cU D).toScheme.functionField
                  ((cU D).toScheme.germToFunctionField O
                  ((cU D).toScheme.presheaf.map
                    (homOfLE (hO.trans (Scheme.Hom.preimage_mono _ hW'))).op
                    ((cU D).ι.app W (t i))))
            else KaehlerDifferential.D k (cU D).toScheme.functionField
              ((cU D).toScheme.germToFunctionField O
              ((cU D).toScheme.presheaf.map
                (homOfLE (hO.trans (Scheme.Hom.preimage_mono _ hW'))).op
                ((cU D).ι.app W (t i)))))).prod := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  have hO' : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W : X.Opens) :=
    hO.trans (Scheme.Hom.preimage_mono _ hW')
  have hθi : ∀ i : Fin n, ratTotal ((cU D).ι ≫ f) O
      ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
        ((TB ((cU D).ι ≫ f)).totalRestrict
          ((Opens.map (cU D).ι.base).map (homOfLE hW')).op (θ i))) =
      ExteriorAlgebra.ι (cU D).toScheme.functionField
        (if (i : ℕ) < r then
          ((cU D).toScheme.germToFunctionField O
            ((cU D).toScheme.presheaf.map (homOfLE hO').op ((cU D).ι.app W (t i))))⁻¹ •
            KaehlerDifferential.D k (cU D).toScheme.functionField
              ((cU D).toScheme.germToFunctionField O
              ((cU D).toScheme.presheaf.map (homOfLE hO').op ((cU D).ι.app W (t i))))
        else KaehlerDifferential.D k (cU D).toScheme.functionField
          ((cU D).toScheme.germToFunctionField O
          ((cU D).toScheme.presheaf.map (homOfLE hO').op ((cU D).ι.app W (t i))))) := by
    intro i
    rw [totalRestrict_totalRestrict _ _ (homOfLE hO').op]
    subst hθ
    by_cases h : (i : ℕ) < r
    · simp only [h, dite_true, ite_true]
      exact ratTotal_totalRestrict_logOne ((cU D).ι ≫ f) hO' (hs ⟨i, h⟩)
    · simp only [h, dite_false, ite_false]
      exact ratTotal_totalRestrict_exactOne ((cU D).ι ≫ f) hO' _
  have hnn : ∀ i : Fin n, (TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
      ((TB ((cU D).ι ≫ f)).totalRestrict
        ((Opens.map (cU D).ι.base).map (homOfLE hW')).op (θ i)) ∈
      nonnegForms ((cU D).ι ≫ f) O := by
    intro i
    rw [totalRestrict_totalRestrict _ _ (homOfLE hO').op]
    subst hθ
    by_cases h : (i : ℕ) < r
    · simp only [h, dite_true]
      rw [Stacks.GradedAlgebra.totalRestrict_mul]
      exact mul_mem_nonnegForms _ _ (by
          rw [totalRestrict_sm]; exact structureMap_mem_nonnegForms _ _ _)
        (by rw [totalRestrict_δ]; exact incl_mem_nonnegForms _ _ 1 _)
    · simp only [h, dite_false]
      rw [totalRestrict_δ]
      exact incl_mem_nonnegForms _ _ 1 _
  rw [hω]
  refine (ratTotal_totalRestrict_sum ((cU D).ι ≫ f) hO Finset.univ
    (fun K => ((cU D).ι.app W').hom (c K)) _ (fun K => K.1.sort (· ≤ ·)) hnn).trans ?_
  refine Finset.sum_congr rfl fun K _ => ?_
  congr 2
  exact List.map_congr_left fun i _ => hθi i

/-- **The rational form of a combination of the chart basis**, as a `p`-form: the combination of
the wedges of the rational chart forms over the `p`-element subsets. -/
theorem ratForm_eq_sum_ιMulti_of_incl_eq_combo [IsIntegral X] (f : X ⟶ Spec (.of k))
    (D : MMP.Mori.Divisor X) [Nonempty (cU D)] {n : ℕ} (W : X.affineOpens)
    (t : Fin n → Γ(X, W)) {r : ℕ} (hr : r ≤ n)
    (s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens)))
    (hs : ∀ i, s i * (cU D).ι.app W (t (Fin.castLE hr i)) = 1)
    (θ : Fin n → (TB ((cU D).ι ≫ f)).Total (op ((cU D).ι ⁻¹ᵁ (W : X.Opens))))
    (hθ : θ = fun i : Fin n => if h : (i : ℕ) < r then
        sm ((cU D).ι ≫ f) _ (s ⟨i, h⟩) * δ ((cU D).ι ≫ f) _ ((cU D).ι.app W (t i))
      else δ ((cU D).ι ≫ f) _ ((cU D).ι.app W (t i)))
    (p : ℕ) (W' : X.affineOpens) (hW' : (W' : X.Opens) ≤ W)
    (c : {K : Finset (Fin n) // K.card = p} → Γ(X, W'))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ (W' : X.Opens))))
    (hω : (TB ((cU D).ι ≫ f)).incl (p : ℤ) ω =
      ∑ K, sm ((cU D).ι ≫ f) _ (((cU D).ι.app W').hom (c K)) *
        ((K.1.sort (· ≤ ·)).map fun i =>
          (TB ((cU D).ι ≫ f)).totalRestrict
            ((Opens.map (cU D).ι.base).map (homOfLE hW')).op (θ i)).prod)
    (O : (cU D).toScheme.affineOpens)
    (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W' : X.Opens))
    [Nonempty (O : (cU D).toScheme.Opens)] :
    letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ratForm ((cU D).ι ≫ f) p O
        ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op ω) =
      ∑ K : {K : Finset (Fin n) // K.card = p},
        (cU D).toScheme.germToFunctionField O
            ((cU D).toScheme.presheaf.map (homOfLE hO).op (((cU D).ι.app W').hom (c K))) •
          exteriorPower.ιMulti (cU D).toScheme.functionField p fun j =>
            (if ((K.1.orderEmbOfFin K.2 j : Fin n) : ℕ) < r then
              ((cU D).toScheme.germToFunctionField O
                ((cU D).toScheme.presheaf.map
                  (homOfLE (hO.trans (Scheme.Hom.preimage_mono _ hW'))).op
                  ((cU D).ι.app W (t (K.1.orderEmbOfFin K.2 j)))))⁻¹ •
                KaehlerDifferential.D k (cU D).toScheme.functionField
                  ((cU D).toScheme.germToFunctionField O
                  ((cU D).toScheme.presheaf.map
                    (homOfLE (hO.trans (Scheme.Hom.preimage_mono _ hW'))).op
                    ((cU D).ι.app W (t (K.1.orderEmbOfFin K.2 j)))))
            else KaehlerDifferential.D k (cU D).toScheme.functionField
              ((cU D).toScheme.germToFunctionField O
              ((cU D).toScheme.presheaf.map
                (homOfLE (hO.trans (Scheme.Hom.preimage_mono _ hW'))).op
                ((cU D).ι.app W (t (K.1.orderEmbOfFin K.2 j)))))) := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  have h1 := ratTotal_eq_sum_of_incl_eq_combo f D W t hr s hs θ hθ p W' hW' c ω hω O hO
  rw [Stacks.GradedAlgebra.totalRestrict_incl, Stacks.sectionRestrict_apply] at h1
  have h2 := (DirectSum.toAddMonoid_of (ratPiece ((cU D).ι ≫ f) O) (p : ℤ)
    (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
      (homOfLE hO).op ω)).symm.trans h1
  rw [← piece_map_eq_presheaf_map ((cU D).ι ≫ f) hO p ω]
  refine Submodule.injective_subtype _ (h2.trans ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [LinearMap.map_smul, Algebra.smul_def]
  congr 1
  rw [Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ← ofFn_orderEmbOfFin K.1 K.2, List.map_ofFn]
  rfl

end MMP.FourfoldProofs.FractionalLogComplexProof
