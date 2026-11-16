module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Restrict.FormsComparison
public import MMP.AlgebraicGeometry.Divisor.IdealSheafRestrictOpen

/-!
# Logarithmic forms on an open subscheme

Let `π : V ⟶ Spec ℂ` be smooth of relative dimension `n`, `D` a relative simple normal crossing
divisor on `V`, `U ⊆ V` an open on which the restriction `D|_U` is relative simple normal
crossing, and `S` a divisor on `V`. For an open `O ⊆ U` of `V`, a form on `(U ∖ D|_U) ∩ O` is a
form on `(V ∖ D) ∩ O` (`MMP.FourfoldProofs.FractionalLogComplexProof.pieceFormsEquiv`), and it is a
section over `O` of `Ω^p_{U/ℂ}(log D|_U) ⊗ I_{S|_U}` exactly when it is a section over `O` of
`Ω^p_{V/ℂ}(log D) ⊗ I_S`.

The two conditions are local on affine opens. An affine open `O' ⊆ U` of `V` has an affine trace
on `U`, and every affine open of `U` is such a trace. Over `O'` the comparison of forms in all
degrees is a ring isomorphism of the total rings of forms, which matches the functions, their
differentials and the restriction of functions from `O'`; the ideals of `S` and of `S|_U` on
`O'` correspond, and so do the local equations of the components of `D` and of `D|_U`, except
for components of `D` missing `O'`, whose local equations on `O'` are units.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.relativeLogForms_restrictDivisor_iff`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

section Restriction

variable {X S : Scheme.{0}} (f : X ⟶ S) (D : MMP.Mori.Divisor X) (p : ℤ)

/-- Restricting a section of the relative `p`-forms on the complement of `D` from `W` to itself is
the identity. -/
theorem relativeDifferentialForms_map_cU_refl {W : X.Opens}
    (ω : Γ(((cU D).ι ≫ f).relativeDifferentialForms p, (cU D).ι ⁻¹ᵁ W)) :
    (((cU D).ι ≫ f).relativeDifferentialForms p).presheaf.map
      (homOfLE ((cU D).ι.preimage_mono le_rfl)).op ω = ω := by
  rw [show (homOfLE ((cU D).ι.preimage_mono le_rfl)).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

/-- A form on the complement of `D` over `W` is a section of the logarithmic forms twisted by `I`
exactly when every point of `W` has an affine open neighbourhood `W' ≤ W` on which the restriction
of the form lies in `brSetOn`. -/
theorem mem_relativeLogForms_iff_brSetOn (n : ℕ) [SmoothOfRelativeDimension n f]
    (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData) (W : X.Opens)
    (ω : Γ(((cU D).ι ≫ f).relativeDifferentialForms p, (cU D).ι ⁻¹ᵁ W)) :
    ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W ↔
      ∀ x ∈ W, ∃ (W' : X.Opens) (hW' : IsAffineOpen W') (h : W' ≤ W), x ∈ W' ∧
        (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).toPresheafGradedAlgebra.incl p
          ((((cU D).ι ≫ f).relativeDifferentialForms p).presheaf.map
            (homOfLE ((cU D).ι.preimage_mono h)).op ω) ∈ brSetOn f (cU D) D I W' hW' := by
  refine ⟨fun hω x hx => ?_, fun hω x hx => ?_⟩
  · obtain ⟨W', h, hx', hB⟩ := hω x hx
    exact ⟨W', W'.2, h, hx', hB⟩
  · obtain ⟨W', hW', h, hx', hB⟩ := hω x hx
    exact ⟨⟨W', hW'⟩, h, hx', hB⟩

end Restriction

section Comparison

variable {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (U : V.Opens)
  (D : MMP.Mori.Divisor V)

variable (S : MMP.Mori.Divisor V)

/-- A ring isomorphism `α` matching the ideals `I` and `J` matches the principal generators of
`I` and `J`. -/
theorem ideal_eq_span_singleton_iff_of_ringEquiv {R R' : Type*} [CommSemiring R] [CommSemiring R']
    (α : R ≃+* R') {I : Ideal R} {J : Ideal R'} (h : ∀ g, α g ∈ J ↔ g ∈ I) (t : R) :
    I = Ideal.span {t} ↔ J = Ideal.span {α t} := by
  refine ⟨fun e => Ideal.ext fun x => ?_, fun e => Ideal.ext fun g => ?_⟩
  · rw [← α.apply_symm_apply x, h, e, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
      map_dvd_iff]
  · rw [← h, e, Ideal.mem_span_singleton, Ideal.mem_span_singleton, map_dvd_iff]

/-- The forward direction of `brSetOn_restrictDivisor_iff`: a form on `(U ∖ D|_U) ∩ O` satisfying
the condition for `S|_U` has comparison on `(V ∖ D) ∩ O` satisfying the condition for `S`. -/
theorem brSetOn_of_brSetOn_restrictDivisor (p : ℤ) (O : V.Opens) (hO : O ≤ U) (hA : IsAffineOpen O)
    (hA' : IsAffineOpen (U.ι ⁻¹ᵁ O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
        π)).piece p).val.obj (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))))
    (h : (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
        π)).toPresheafGradedAlgebra.incl p ω ∈
        brSetOn (U.ι ≫ π) (cU (restrictDivisor U D)) (restrictDivisor U D)
          (restrictDivisor U S).suppIdeal (U.ι ⁻¹ᵁ O) hA') :
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl p
          (pieceFormsEquiv' π U D p O hO ω) ∈
        brSetOn π (cU D) D S.suppIdeal O hA := by
  set α := appRingEquiv U O hO
  have hideal : ∀ (I : V.IdealSheafData) (g : Γ(V, O)),
      α g ∈ (I.comap U.ι).ideal ⟨U.ι ⁻¹ᵁ O, hA'⟩ ↔ g ∈ I.ideal ⟨O, hA⟩ :=
    fun I g => app_mem_ideal_comap_iff U I hA hO hA' g
  have key := map_mem_brSetOn (U.ι ≫ π) π (cU (restrictDivisor U D)) (cU D) (restrictDivisor U D)
      D (restrictDivisor U S).suppIdeal S.suppIdeal (U.ι ⁻¹ᵁ O) hA' O hA
      (pieceTotalEquiv π U D O hO) (pieceRingEquiv U D O hO) α.symm
      (pieceTotalEquiv_structureMap π U D O hO) (pieceTotalEquiv_dOne π U D O hO)
      (fun a => (congrArg (fun z => pieceRingEquiv U D O hO
        (((cU (restrictDivisor U D)).ι.app (U.ι ⁻¹ᵁ O)).hom z))
        (α.apply_symm_apply a)).symm.trans (pieceRingEquiv_app U D O hO _))
      (fun E hE t ht => by
        left
        refine ⟨primeDivisorOfOpens U E, ?_, ?_⟩
        · rw [Finsupp.mem_support_iff, restrictDivisor_apply] at hE
          exact Finsupp.mem_support_iff.2 hE
        · refine (ideal_eq_span_singleton_iff_of_ringEquiv α (hideal _) _).2 ?_
          change _ = Ideal.span {α (α.symm t)}
          rw [comap_idealSheaf_primeDivisorOfOpens, α.apply_symm_apply]
          exact ht)
      (fun a ha => by
        rw [suppIdeal_restrictDivisor] at ha
        exact (hideal _ _).1 (by rwa [α.apply_symm_apply]))
      h
  exact (congrArg (· ∈ brSetOn π (cU D) D S.suppIdeal O hA)
    (pieceTotalEquiv_incl π U D O hO p ω)).mp key

/-- The backward direction of `brSetOn_restrictDivisor_iff`: a form on `(U ∖ D|_U) ∩ O` whose
comparison on `(V ∖ D) ∩ O` satisfies the condition for `S` satisfies the condition for `S|_U`. -/
theorem brSetOn_restrictDivisor_of_brSetOn (p : ℤ) (O : V.Opens) (hO : O ≤ U) (hA : IsAffineOpen O)
    (hA' : IsAffineOpen (U.ι ⁻¹ᵁ O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
        π)).piece p).val.obj (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))))
    (h : (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl p
          (pieceFormsEquiv' π U D p O hO ω) ∈
        brSetOn π (cU D) D S.suppIdeal O hA) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
        π)).toPresheafGradedAlgebra.incl p ω ∈
        brSetOn (U.ι ≫ π) (cU (restrictDivisor U D)) (restrictDivisor U D)
          (restrictDivisor U S).suppIdeal (U.ι ⁻¹ᵁ O) hA' := by
  set Φ := pieceTotalEquiv π U D O hO
  set ψ := pieceRingEquiv U D O hO
  set α := appRingEquiv U O hO
  have hideal : ∀ (I : V.IdealSheafData) (g : Γ(V, O)),
      α g ∈ (I.comap U.ι).ideal ⟨U.ι ⁻¹ᵁ O, hA'⟩ ↔ g ∈ I.ideal ⟨O, hA⟩ :=
    fun I g => app_mem_ideal_comap_iff U I hA hO hA' g
  have key := map_mem_brSetOn π (U.ι ≫ π) (cU D) (cU (restrictDivisor U D)) D
      (restrictDivisor U D) S.suppIdeal (restrictDivisor U S).suppIdeal O hA (U.ι ⁻¹ᵁ O) hA'
      Φ.symm ψ.symm α
      (fun c => by
        have e := pieceTotalEquiv_structureMap π U D O hO (ψ.symm c)
        rw [ψ.apply_symm_apply] at e
        rw [← e, Φ.symm_apply_apply])
      (fun c => by
        have e := pieceTotalEquiv_dOne π U D O hO (ψ.symm c)
        rw [ψ.apply_symm_apply] at e
        rw [← e, Φ.symm_apply_apply])
      (fun g => (RingEquiv.symm_apply_eq ψ).2 (pieceRingEquiv_app U D O hO g).symm)
      (fun E hE t ht => by
        by_cases hx : ∃ y : U.toScheme, y ∈ U.ι ⁻¹ᵁ O ∧ U.ι y ∈ E.support
        · obtain ⟨y, -, hyE⟩ := hx
          obtain ⟨E', rfl⟩ := exists_primeDivisorOfOpens_eq U E hyE
          left
          refine ⟨E', ?_, ?_⟩
          · rw [Finsupp.mem_support_iff, restrictDivisor_apply]
            exact Finsupp.mem_support_iff.1 hE
          · rw [← comap_idealSheaf_primeDivisorOfOpens]
            exact (ideal_eq_span_singleton_iff_of_ringEquiv α (hideal _) _).1 ht
        · right
          have htop : E.idealSheaf.ideal ⟨O, hA⟩ = ⊤ :=
            ideal_eq_top_of_disjoint _ _ fun z hz hzE => hx ⟨⟨z, hO hz⟩, hz, hzE⟩
          rw [ht, Ideal.span_singleton_eq_top] at htop
          exact htop.map α)
      (fun a ha => by
        rw [suppIdeal_restrictDivisor]
        exact (hideal _ _).2 ha)
      h
  refine (congrArg (· ∈ brSetOn (U.ι ≫ π) (cU (restrictDivisor U D)) (restrictDivisor U D)
    (restrictDivisor U S).suppIdeal (U.ι ⁻¹ᵁ O) hA') ?_).mp key
  exact (pieceTotalEquiv_symm_incl π U D O hO p _).trans
    (congrArg _ ((pieceFormsEquiv' π U D p O hO).symm_apply_apply ω))

/-- **Logarithmic forms over an affine open `O ⊆ U`** of `V` with affine trace on `U`: a form on
`(U ∖ D|_U) ∩ O` satisfies the condition for `S|_U` exactly when its comparison on `(V ∖ D) ∩ O`
satisfies the condition for `S`. -/
theorem brSetOn_restrictDivisor_iff (p : ℤ) (O : V.Opens) (hO : O ≤ U) (hA : IsAffineOpen O)
    (hA' : IsAffineOpen (U.ι ⁻¹ᵁ O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
        π)).piece p).val.obj (op ((cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O)))) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
        π)).toPresheafGradedAlgebra.incl p ω ∈
        brSetOn (U.ι ≫ π) (cU (restrictDivisor U D)) (restrictDivisor U D)
          (restrictDivisor U S).suppIdeal (U.ι ⁻¹ᵁ O) hA' ↔
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl p
          (pieceFormsEquiv' π U D p O hO ω) ∈
        brSetOn π (cU D) D S.suppIdeal O hA :=
  ⟨brSetOn_of_brSetOn_restrictDivisor π U D S p O hO hA hA' ω,
    brSetOn_restrictDivisor_of_brSetOn π U D S p O hO hA hA' ω⟩

/-- The comparison `pieceFormsEquiv'` of forms commutes with restriction from `O₂` to `O₁`. -/
theorem pieceFormsEquiv'_map (q : ℤ) {O₁ O₂ : V.Opens} (h : O₁ ≤ O₂) (hO₂ : O₂ ≤ U)
    (x : Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms q,
      (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O₂))) :
    pieceFormsEquiv' π U D q O₁ (h.trans hO₂)
        (((((cU (restrictDivisor U D)).ι ≫ (U.ι ≫ π)).relativeDifferentialForms q).presheaf.map
            (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono (U.ι.preimage_mono h))).op x)) =
      ((((cU D).ι ≫ π).relativeDifferentialForms q).presheaf.map (homOfLE ((cU D).ι.preimage_mono
          h)).op (pieceFormsEquiv π U D q O₂ hO₂ x)) :=
  (pieceFormsEquiv'_apply_sections π U D q O₁ _ _).trans (pieceFormsEquiv_map π U D q h hO₂ x)

/-- The form version of `brSetOn_restrictDivisor_iff` for an affine open `W₁` of `U` equal to the
trace `U.ι ⁻¹ᵁ O` of an affine open `O ⊆ U` of `V`. -/
theorem brSetOn_restrictDivisor_iff_of_eq (p : ℤ) (O : V.Opens) (hO : O ≤ U)
    (hA : IsAffineOpen O) (W₁ : U.toScheme.Opens) (hA₁ : IsAffineOpen W₁) (hW : U.ι ⁻¹ᵁ O = W₁)
    (ω : Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms p,
      (cU (restrictDivisor U D)).ι ⁻¹ᵁ W₁)) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU (restrictDivisor U D)).ι ≫ U.ι ≫
        π)).toPresheafGradedAlgebra.incl p ω ∈
        brSetOn (U.ι ≫ π) (cU (restrictDivisor U D)) (restrictDivisor U D)
          (restrictDivisor U S).suppIdeal W₁ hA₁ ↔
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).toPresheafGradedAlgebra.incl p
          (pieceFormsEquiv' π U D p O hO
            ((((cU (restrictDivisor U D)).ι ≫ (U.ι ≫ π)).relativeDifferentialForms p).presheaf.map
              (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono hW.le)).op ω)) ∈
        brSetOn π (cU D) D S.suppIdeal O hA := by
  subst hW
  rw [relativeDifferentialForms_map_cU_refl (U.ι ≫ π) (restrictDivisor U D) p]
  exact brSetOn_restrictDivisor_iff π U D S p O hO hA hA₁ ω

end Comparison

/-- **Logarithmic forms on an open subscheme.** For an open `O ⊆ U` of `V`, a form on
`(U ∖ D|_U) ∩ O` is a section over `O` of `Ω^p_{U/ℂ}(log D|_U)` twisted by the ideal of `Supp S|_U`
exactly when its comparison on `(V ∖ D) ∩ O` is a section over `O` of `Ω^p_{V/ℂ}(log D)` twisted
by the ideal of `Supp S`. -/
theorem relativeLogForms_restrictDivisor_iff (n : ℕ) {V : Scheme.{0}}
    (π : V ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] (U : V.Opens)
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π)
    (hDU : MMP.Mori.Divisor.IsRelativeSNC n (U.ι ≫ π) (restrictDivisor U D))
    (S : MMP.Mori.Divisor V) (p : ℕ) (O : V.Opens) (hO : O ≤ U)
    (η : Γ(((cU (restrictDivisor U D)).ι ≫ U.ι ≫ π).relativeDifferentialForms (p : ℤ),
      (cU (restrictDivisor U D)).ι ⁻¹ᵁ (U.ι ⁻¹ᵁ O))) :
    η ∈ MMP.Mori.Divisor.relativeLogForms n (U.ι ≫ π) (restrictDivisor U D) hDU
        (restrictDivisor U S).suppIdeal p (U.ι ⁻¹ᵁ O) ↔
      pieceFormsEquiv π U D p O hO η ∈
        MMP.Mori.Divisor.relativeLogForms n π D hD S.suppIdeal p O := by
  constructor
  · intro h
    refine (mem_relativeLogForms_iff_brSetOn π D p n hD S.suppIdeal O _).2 fun x hx => ?_
    obtain ⟨W₁, hA₁, h₁, hy, hB⟩ := (mem_relativeLogForms_iff_brSetOn (U.ι ≫ π)
      (restrictDivisor U D) p n hDU (restrictDivisor U S).suppIdeal (U.ι ⁻¹ᵁ O) η).1 h
      ⟨x, hO hx⟩ hx
    have hpre : U.ι ⁻¹ᵁ (U.ι ''ᵁ W₁) = W₁ := U.ι.preimage_image_eq _
    have hO'O : U.ι ''ᵁ W₁ ≤ O := by
      refine (U.ι.image_mono h₁).trans ?_
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_le_right
    refine ⟨U.ι ''ᵁ W₁, hA₁.image_of_isOpenImmersion U.ι, hO'O, ⟨⟨x, hO hx⟩, hy, rfl⟩, ?_⟩
    rw [← pieceFormsEquiv'_map π U D p hO'O hO η,
      ← MMP.FourfoldProofs.LogDegenerationProof.modules_map_map_apply (((cU (restrictDivisor U D)).ι ≫
          U.ι ≫ π).relativeDifferentialForms (p : ℤ))
      (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono h₁)).op
      (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono hpre.le)).op
      (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono (U.ι.preimage_mono hO'O))).op η]
    exact (brSetOn_restrictDivisor_iff_of_eq π U D S p _ (hO'O.trans hO)
      (hA₁.image_of_isOpenImmersion U.ι) W₁ hA₁ hpre _).1 hB
  · intro h
    refine (mem_relativeLogForms_iff_brSetOn (U.ι ≫ π) (restrictDivisor U D) p n hDU
      (restrictDivisor U S).suppIdeal (U.ι ⁻¹ᵁ O) η).2 fun y hy => ?_
    obtain ⟨W', hA, hW', hx, hB⟩ :=
      (mem_relativeLogForms_iff_brSetOn π D p n hD S.suppIdeal O _).1 h (U.ι y) hy
    have hA' : IsAffineOpen (U.ι ⁻¹ᵁ W') :=
      hA.preimage_of_isOpenImmersion U.ι (by rw [Scheme.Opens.opensRange_ι]; exact hW'.trans hO)
    refine ⟨U.ι ⁻¹ᵁ W', hA', U.ι.preimage_mono hW', hx, ?_⟩
    refine (brSetOn_restrictDivisor_iff_of_eq π U D S p W' (hW'.trans hO) hA (U.ι ⁻¹ᵁ W') hA'
      rfl _).2 ?_
    rwa [MMP.FourfoldProofs.LogDegenerationProof.modules_map_map_apply (((cU (restrictDivisor U D)).ι ≫
        U.ι ≫ π).relativeDifferentialForms (p : ℤ))
      (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono (U.ι.preimage_mono hW'))).op
      (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono le_rfl)).op
      (homOfLE ((cU (restrictDivisor U D)).ι.preimage_mono (U.ι.preimage_mono hW'))).op η,
      pieceFormsEquiv'_map π U D p hW' hO η]

end MMP.FourfoldProofs.FractionalLogComplexProof
