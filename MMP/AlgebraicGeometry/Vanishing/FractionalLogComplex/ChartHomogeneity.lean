module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Construction
public import MMP.AlgebraicGeometry.DeRham.RationalForms.Separation
public import MMP.AlgebraicGeometry.DeRham.RationalForms.TotalRing

/-!
# Homogeneity of chart combinations

On an open `O` of a scheme `Y` over `S`, a combination `∑_K c_K θ_{K}` of products of length `p`
of forms `θᵢ = σᵢ dτᵢ` is homogeneous of degree `p`: it is the image of a `p`-form in the total
ring of forms. The basis of the logarithmic forms on a chart of a relative simple normal crossing
divisor consists of such products (`θᵢ = sᵢ dtᵢ = dtᵢ/tᵢ` or `θᵢ = dtᵢ`), so a form can be
compared with a combination of the basis through its rational forms.

Combined with the description of the twisted logarithmic forms on a chart by their coordinates
in this basis (`MMP.Mori.Divisor.relativeLogForms_free_and_deRhamD_mem`), and with the fact that a
form is determined by its rational forms, this gives a criterion for a form to be a twisted
logarithmic form: its rational forms are those of a combination of the basis with coefficients
in the twisting ideal.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_incl_eq_sum_sm_mul_prod`: homogeneity.
* `MMP.FourfoldProofs.FractionalLogComplexProof.eq_of_ratTotal_eq`: forms with the same rational forms
  are equal.
* `MMP.FourfoldProofs.FractionalLogComplexProof.mem_relativeLogForms_of_ratTotal_eq`: the membership
  criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

section Homogeneous

variable {Y S : Scheme.{u}} (g : Y ⟶ S)

/-- `b · ∏ σᵢ dτᵢ` is a monomial `b ∏ σᵢ · dτ₁ ∧ ⋯ ∧ dτₚ`. -/
theorem sm_mul_prod_eq_mon {O : Y.Opens} {ι : Type*} (b : Γ(Y, O)) (σ τ : ι → Γ(Y, O))
    (l : List ι) :
    sm g O b * (l.map fun i => sm g O (σ i) * δ g O (τ i)).prod =
      mon g O (b * (l.map σ).prod) (l.map τ) := by
  rw [prod_map_sm_mul, mon, map_mul, mul_assoc, List.map_map]
  rfl

/-- **Homogeneity of chart combinations.** A combination `∑_K c_K θ_{l_K}` of products of length
`p` of forms `θᵢ = σᵢ dτᵢ` is the image of a `p`-form. -/
theorem exists_incl_eq_sum_sm_mul_prod {O : Y.Opens} {ι κ : Type*}
    (θ : ι → (TB g).Total (op O)) (hθ : ∀ i, ∃ σ τ : Γ(Y, O), θ i = sm g O σ * δ g O τ)
    (s : Finset κ) (c : κ → Γ(Y, O)) (l : κ → List ι) (p : ℕ)
    (hl : ∀ K ∈ s, (l K).length = p) :
    ∃ x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O),
      (TB g).incl (p : ℤ) x = ∑ K ∈ s, sm g O (c K) * ((l K).map θ).prod := by
  classical
  choose σ τ hστ using hθ
  have hθ' : θ = fun i => sm g O (σ i) * δ g O (τ i) := funext hστ
  have hK : ∀ K ∈ s, ∃ x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece
      (p : ℤ)).val.obj (op O), (TB g).incl (p : ℤ) x = sm g O (c K) * ((l K).map θ).prod := by
    intro K hKs
    rw [hθ', sm_mul_prod_eq_mon]
    obtain ⟨x, hx, -⟩ := exists_incl_eq_mon (g := g) O (c K * ((l K).map σ).prod) ((l K).map τ)
    have hlen : ((l K).map τ).length = p := by rw [List.length_map, hl K hKs]
    revert x
    rw [hlen]
    exact fun x hx => ⟨x, hx⟩
  choose! x hx using hK
  refine ⟨∑ K ∈ s, x K, ?_⟩
  rw [incl_sum]
  exact Finset.sum_congr rfl fun K hKs => hx K hKs

end Homogeneous

section Membership

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Two `q`-forms on `O` are equal if their images in the total ring of rational forms agree on
every non-empty affine open `W ⊆ O`. -/
theorem eq_of_ratTotal_eq (sX : X ⟶ Spec (.of k)) [IsIntegral X] {m : ℕ}
    [SmoothOfRelativeDimension m sX] (q : ℕ) {O : X.Opens}
    (θ θ' : ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (q : ℤ)).val.obj (op O))
    (h : ∀ (W : X.affineOpens) (hW : (W : X.Opens) ≤ O) [Nonempty (W : X.Opens)],
      ratTotal sX W ((TB sX).totalRestrict (homOfLE hW).op ((TB sX).incl (q : ℤ) θ)) =
        ratTotal sX W ((TB sX).totalRestrict (homOfLE hW).op ((TB sX).incl (q : ℤ) θ'))) :
    θ = θ' := by
  refine eq_of_ratForm_eq sX (m := m) q θ θ' fun W hW _ => ?_
  have h1 := h W hW
  rw [Stacks.GradedAlgebra.totalRestrict_incl, Stacks.GradedAlgebra.totalRestrict_incl] at h1
  have h2 : ratPiece sX W q
        (Stacks.sectionRestrict ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece q).val
          (homOfLE hW).op θ) =
      ratPiece sX W q
        (Stacks.sectionRestrict ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece q).val
          (homOfLE hW).op θ') :=
    (DirectSum.toAddMonoid_of _ _ _).symm.trans (h1.trans (DirectSum.toAddMonoid_of _ _ _))
  have h3 := Submodule.injective_subtype _ h2
  rw [Stacks.sectionRestrict_apply, Stacks.sectionRestrict_apply,
    piece_map_eq_presheaf_map sX hW q θ, piece_map_eq_presheaf_map sX hW q θ'] at h3
  exact h3

/-- **Membership in the logarithmic forms through rational forms.** On an affine open `W'` inside
a chart `W` of the relative simple normal crossing divisor `D`, a form `ω` on `W' ∖ D` whose
rational form on every non-empty affine open `O ⊆ W' ∖ D` is that of a combination `∑_K c_K θ_K`
of the chart basis, with every `c_K ∈ I(W')`, is a section of `I · Ω^p_X(log D)` over `W'`. -/
theorem mem_relativeLogForms_of_ratTotal_eq [IsIntegral X] (n : ℕ) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor X) (hD : D.IsRelativeSNC n f)
    [Nonempty (cU D)] (x : X) (W : X.affineOpens) (V : (Spec (.of k)).affineOpens)
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
    (p : ℕ) (W' : X.affineOpens) (hW' : (W' : X.Opens) ≤ W) (I : X.IdealSheafData)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (p : ℤ)).val.obj (op ((cU D).ι ⁻¹ᵁ (W' : X.Opens))))
    (c : {K : Finset (Fin n) // K.card = p} → Γ(X, W')) (hc : ∀ K, c K ∈ I.ideal W')
    (hω : ∀ (O : (cU D).toScheme.affineOpens)
      (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W' : X.Opens))
      [Nonempty (O : (cU D).toScheme.Opens)],
      ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
          ((TB ((cU D).ι ≫ f)).incl (p : ℤ) ω)) =
        ratTotal ((cU D).ι ≫ f) O
          ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
            (∑ K, sm ((cU D).ι ≫ f) _ (((cU D).ι.app W').hom (c K)) *
              ((K.1.sort (· ≤ ·)).map fun i =>
                (TB ((cU D).ι ≫ f)).totalRestrict
                  ((Opens.map (cU D).ι.base).map (homOfLE hW')).op (θ i)).prod))) :
    ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W' := by
  have : SmoothOfRelativeDimension n ((cU D).ι ≫ f) := by
    have h := (inferInstance : SmoothOfRelativeDimension (0 + n) ((cU D).ι ≫ f))
    rwa [zero_add] at h
  obtain ⟨-, hiff, -, -⟩ :=
    (MMP.Mori.Divisor.relativeLogForms_free_and_deRhamD_mem n f D hD).2 x W V e t hx hb r
    hr j hj hjD hDW s hs p W' hW'
  refine (hiff I ω).2 ⟨c, hc, ?_⟩
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
  have hωy : ω = y := by
    refine eq_of_ratTotal_eq ((cU D).ι ≫ f) (m := n) p ω y fun O hO _ => ?_
    rw [hω O hO, hy]
  subst hωy
  subst hθ
  exact hy

end Membership

end MMP.FourfoldProofs.FractionalLogComplexProof
