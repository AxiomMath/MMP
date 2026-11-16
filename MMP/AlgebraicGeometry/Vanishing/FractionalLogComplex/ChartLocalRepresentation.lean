module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.ChartHomogeneity

/-!
# Sections of `𝒪_X(-M) · Ω^p_X(log D)(-S)` on a chart, through rational forms

Let `W'` be an affine open inside a chart of the relative simple normal crossing divisor `D`, and
`g₀` a section of `𝒪_X(-M)` over `W'`. A form `ω` on `U ∩ W' ∩ U'` (`U = X ∖ D`,
`U' = X ∖ (D ∪ Supp M)`) whose rational forms are those of `g₀ ∑_K c_K θ_K`, with `θ_K` the chart
basis of the logarithmic forms and every `c_K` in the ideal of `S`, has the local representation
`ω = g₀ η` with `η` a section of `Ω^p_X(log D)(-S)` over `W'`: it is a section of
`𝒪_X(-M) · Ω^p_X(log D)(-S)` over `W'`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.localRep_of_ratTotal_eq`: the local representation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Local representations through rational forms.** A form on `U ∩ W' ∩ U'` with the rational
forms of `g₀ ∑_K c_K θ_K`, `g₀` a section of `𝒪_X(-M)` over `W'` and the `c_K` in the ideal of
`S`, is `g₀ η` with `η` a section of `Ω^p_X(log D)(-S)` over `W'`. -/
theorem localRep_of_ratTotal_eq [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (n : ℕ)
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor X)
    (hD : D.IsRelativeSNC n f) (S M : MMP.Mori.Divisor X) [Nonempty (cU D)]
    (x : X) (W : X.affineOpens) (V : (Spec (.of k)).affineOpens)
    (e : (W : X.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens)) (t : Fin n → Γ(X, W))
    (hx : x ∈ (W : X.Opens))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄Γ(Spec (.of k), V)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (.of k), V) Γ(X, W) (t i))
    (r : ℕ) (hr : r ≤ n) (j : Fin r → MMP.Mori.PrimeDivisor X) (hj : Function.Injective j)
    (hjD : ∀ i, j i ∈ D.support ∧ x ∈ (j i).support ∧
      (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    (hDW : D.suppIdeal.ideal W = Ideal.span {∏ i, t (Fin.castLE hr i)})
    (s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens)))
    (hs : ∀ i, s i * (cU D).ι.app W (t (Fin.castLE hr i)) = 1)
    (θ : Fin n → (TB ((cU D).ι ≫ f)).Total (op ((cU D).ι ⁻¹ᵁ (W : X.Opens))))
    (hθ : θ = fun i : Fin n => if h : (i : ℕ) < r then
        sm ((cU D).ι ≫ f) _ (s ⟨i, h⟩) * δ ((cU D).ι ≫ f) _ ((cU D).ι.app W (t i))
      else δ ((cU D).ι ≫ f) _ ((cU D).ι.app W (t i)))
    (p : ℕ) (W' : X.affineOpens) (hW' : (W' : X.Opens) ≤ W)
    (g₀ : Γ(X, (W' : X.Opens) ⊓ cU' D M)) (hg₀ : DivCond (D := D) (M := M) (W' : X.Opens) g₀)
    (c : {K : Finset (Fin n) // K.card = p} → Γ(X, W')) (hc : ∀ K, c K ∈ S.suppIdeal.ideal W')
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op (OO D M W')))
    (hω : ∀ (O : (cU D).toScheme.affineOpens)
      (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W') [Nonempty (O : (cU D).toScheme.Opens)],
      ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
          ((TB ((cU D).ι ≫ f)).incl (p : ℤ) ω)) =
        ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
          (sm ((cU D).ι ≫ f) (OO D M W') ((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M) g₀) *
            (TB ((cU D).ι ≫ f)).totalRestrict
              (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
                (inf_le_left : (W' : X.Opens) ⊓ cU' D M ≤ W'))).op
              (∑ K, sm ((cU D).ι ≫ f) _ (((cU D).ι.app W').hom (c K)) *
                ((K.1.sort (· ≤ ·)).map fun i =>
                  (TB ((cU D).ι ≫ f)).totalRestrict
                    ((Opens.map (cU D).ι.base).map (homOfLE hW')).op (θ i)).prod)))) :
    LocalRep n f D hD S M p W' ω := by
  have : SmoothOfRelativeDimension n ((cU D).ι ≫ f) := zero_add n ▸ inferInstance
  -- the form `η = ∑_K c_K θ_K` on `W' ∖ D`
  obtain ⟨y, hy⟩ := exists_incl_eq_sum_sm_mul_prod ((cU D).ι ≫ f)
    (O := (cU D).ι ⁻¹ᵁ (W' : X.Opens))
    (fun i => (TB ((cU D).ι ≫ f)).totalRestrict
      ((Opens.map (cU D).ι.base).map (homOfLE hW')).op (θ i))
    (fun i => by
      rw [hθ]
      by_cases h : (i : ℕ) < r
      · refine ⟨(cU D).toScheme.presheaf.map ((Opens.map (cU D).ι.base).map (homOfLE hW')).op
            (s ⟨i, h⟩),
          (cU D).toScheme.presheaf.map ((Opens.map (cU D).ι.base).map (homOfLE hW')).op
            ((cU D).ι.app W (t i)), ?_⟩
        simp only [h, dite_true]
        rw [Stacks.GradedAlgebra.totalRestrict_mul, totalRestrict_sm, totalRestrict_δ]
      · refine ⟨1, (cU D).toScheme.presheaf.map ((Opens.map (cU D).ι.base).map (homOfLE hW')).op
            ((cU D).ι.app W (t i)), ?_⟩
        simp only [h, dite_false]
        rw [totalRestrict_δ, map_one, one_mul])
    Finset.univ (fun K => ((cU D).ι.app W').hom (c K)) (fun K => K.1.sort (· ≤ ·)) p
    (fun K _ => by rw [Finset.length_sort, K.2])
  refine ⟨1, fun _ => g₀, fun _ => y, fun _ => hg₀, fun _ =>
    mem_relativeLogForms_of_ratTotal_eq n f D hD x W V e t hx hb r hr j hj hjD hDW s hs θ hθ p W'
      hW' S.suppIdeal y c hc fun O hO _ => by rw [hy], ?_⟩
  rw [Fin.sum_univ_one]
  -- `ω = g₀ η` on `U ∩ W' ∩ U'`
  let a := asStr ((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M) g₀)
  let y' := ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
    (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
      (inf_le_left : (W' : X.Opens) ⊓ cU' D M ≤ W'))).op y
  have e1 : (TB ((cU D).ι ≫ f)).incl (p : ℤ) (a • y') =
      sm ((cU D).ι ≫ f) (OO D M W') ((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M) g₀) *
        (TB ((cU D).ι ≫ f)).totalRestrict
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
            (inf_le_left : (W' : X.Opens) ⊓ cU' D M ≤ W'))).op
          ((TB ((cU D).ι ≫ f)).incl (p : ℤ) y) := by
    rw [Stacks.GradedAlgebra.totalRestrict_incl, Stacks.sectionRestrict_apply]
    exact (sm_mul_incl a (p : ℤ) y').symm
  rw [eq_of_ratTotal_eq ((cU D).ι ≫ f) (m := n) p ω (a • y') fun O hO _ => by
    rw [hω O hO, e1, hy]]
  exact (sm_mul_incl a (p : ℤ) y').symm

end MMP.FourfoldProofs.FractionalLogComplexProof
