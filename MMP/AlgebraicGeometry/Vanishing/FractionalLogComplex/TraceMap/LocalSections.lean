module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.PullbackMap.Gluing

/-!
# Local sections of `C^p` with a prescribed rational form

Let `D` be a relative simple normal crossing divisor on a normal integral scheme `X` smooth over
`k`, `S ≤ D` with support in `D`, `M` a divisor, and `ρ` a rational `p`-form. Near a point `x`,
let `g₀` be a section of `𝒪_X(-M)` over an open `W₂ ∋ x` with non-zero germ `G`. If at every prime
divisor `E` meeting `W₂` the form `G⁻¹ ρ` lies in the wedges of the regular lattice (`E ∉ D`), of
the logarithmic lattice (`E ∈ D`), and in the maximal ideal times the latter (`E ∈ S`), then near
`x` the form `ρ` is the rational form of `g₀ η` with `η` a section of `Ω^p_X(log D)(-S)`: on a
chart of `D` the form `G⁻¹ ρ` is a combination of the chart basis with coefficients in the ideal
of `S` (`MMP.FourfoldProofs.FractionalLogComplexProof.exists_local_relativeLogForm_of_le`).

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_localRep_of_forall_primeDivisor`: the local
  sections `g₀ η` of `C^p`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_cond_of_forall_localRep`: the glued section of
  `C^p` over an open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Local sections `g₀ η` of `C^p` with rational form `ρ`.** If `g₀` is a section of
`𝒪_X(-M)` over `W₂` with non-zero germ `G`, and at every prime divisor `E` meeting `W₂` the form
`G⁻¹ ρ` lies in the regular wedge (`E ∉ D`), the logarithmic wedge (`E ∈ D`), and the maximal ideal
times the logarithmic wedge (`E ∈ S`), then every `x ∈ W₂` has an affine neighbourhood `W' ≤ W₂`
with a local representation whose rational form is `ρ`. -/
theorem exists_localRep_of_forall_primeDivisor [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (n : ℕ) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor X)
    (hD : D.IsRelativeSNC n f) (S M : MMP.Mori.Divisor X) (hSD : ∀ E ∈ S.support, E ∈ D.support)
    [Nonempty (cU D)] (p : ℕ) (W₂ : X.Opens) (g₀ : Γ(X, W₂ ⊓ cU' D M))
    (hg₀ : DivCond (D := D) (M := M) W₂ g₀) [Nonempty (W₂ ⊓ cU' D M : X.Opens)]
    (hG : X.germToFunctionField (W₂ ⊓ cU' D M) g₀ ≠ 0)
    (ρ : letI := MMP.Mori.functionFieldAlgebra f; ⋀[X.functionField]^p Ω[X.functionField⁄k])
    (hβ : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ W₂).Nonempty →
      letI := MMP.Mori.functionFieldAlgebra f
      letI := MMP.Mori.stalkAlgebra f E.genericPoint
      haveI := MMP.Mori.isScalarTower_stalk_functionField f E.genericPoint
      (E ∉ D.support → (X.germToFunctionField (W₂ ⊓ cU' D M) g₀)⁻¹ • ρ ∈
          wedgeSpan E.localRing (regLattice k E.localRing) p) ∧
      (E ∈ D.support → (X.germToFunctionField (W₂ ⊓ cU' D M) g₀)⁻¹ • ρ ∈
          wedgeSpan E.localRing (logLattice k E.localRing) p) ∧
      (E ∈ S.support → (X.germToFunctionField (W₂ ⊓ cU' D M) g₀)⁻¹ • ρ ∈
          maximalIdeal E.localRing • wedgeSpan E.localRing (logLattice k E.localRing) p))
    {x : X} (hx : x ∈ W₂) :
    ∃ (W' : X.affineOpens), x ∈ (W' : X.Opens) ∧ (W' : X.Opens) ≤ W₂ ∧
      ∃ ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
          (op (OO D M (W' : X.Opens))),
        LocalRep n f D hD S M p (W' : X.Opens) ω ∧
        letI := MMP.Mori.functionFieldAlgebra f
        ∀ (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W')
          [Nonempty (O : (cU D).toScheme.Opens)],
          openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p O
            ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map
              (homOfLE hO).op ω)) = ρ := by
  classical
  let := MMP.Mori.functionFieldAlgebra f
  set G := X.germToFunctionField (W₂ ⊓ cU' D M) g₀
  obtain ⟨W', hxW', hW'₂, y, hyS, hyβ⟩ := exists_local_relativeLogForm_of_le n f D S hD hSD p W₂
    (G⁻¹ • ρ) hβ hx
  have hle : (W' : X.Opens) ⊓ cU' D M ≤ W₂ ⊓ cU' D M := inf_le_inf_right _ hW'₂
  set g₁ : Γ(X, (W' : X.Opens) ⊓ cU' D M) := X.presheaf.map (homOfLE hle).op g₀ with hg₁
  set a := asStr ((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M) g₁)
  set y' := ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
    (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
      (inf_le_left : (W' : X.Opens) ⊓ cU' D M ≤ W'))).op y
  refine ⟨W', hxW', hW'₂, a • y', ⟨1, fun _ => g₁, fun _ => y,
    fun _ => DivCond.restrict (D := D) (M := M) hW'₂ hg₀, fun _ => hyS, ?_⟩, fun O hO _ => ?_⟩
  · rw [Fin.sum_univ_one]
    exact (sm_mul_incl a (p : ℤ) y').symm
  · have hO₁ : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W' : X.Opens) :=
      hO.trans (Scheme.Hom.preimage_mono _ inf_le_left)
    obtain ⟨⟨w, hw⟩⟩ := ‹Nonempty (O : (cU D).toScheme.Opens)›
    have : Nonempty (OO D M (W' : X.Opens)) := ⟨⟨w, hO hw⟩⟩
    have : Nonempty ((W' : X.Opens) ⊓ cU' D M : X.Opens) := ⟨⟨_, hO hw⟩⟩
    have e1 : (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
        (p : ℤ)).val.map (homOfLE hO).op (a • y') : Γ(((cU D).ι ≫ f).relativeDifferentialForms
          (p : ℤ), O)) = ((cU D).toScheme.presheaf.map (homOfLE hO).op
          ((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M) g₁)) •
          (((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO₁).op y := by
      refine (PresheafOfModules.map_smul _ _ _ _).trans ?_
      congr 1
      exact piece_map_map _ _ _ _ y
    rw [← piece_map_eq_presheaf_map ((cU D).ι ≫ f) hO p (a • y')]
    rw [e1, ratForm_smul, openFormsMap_smul, hyβ O hO₁, germToFunctionField_map,
      openFunctionFieldEquiv_germ, hg₁, germToFunctionField_map, smul_smul,
      mul_inv_cancel₀ hG, one_smul]

/-- **Gluing local sections of `C^p` with rational form `ρ`.** If every point of `W` has an
affine neighbourhood `W' ⊆ W` carrying a local representation `∑ gᵢ ηᵢ` with rational form `ρ`,
then there is a section of `C^p` over `W` satisfying `Cond` whose rational form is `ρ`. -/
theorem exists_cond_of_forall_localRep [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (n : ℕ) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor X)
    (hD : D.IsRelativeSNC n f) (S M : MMP.Mori.Divisor X) [Nonempty (cU D)] (p : ℕ)
    (W : X.Opens)
    (ρ : letI := MMP.Mori.functionFieldAlgebra f; ⋀[X.functionField]^p Ω[X.functionField⁄k])
    (hloc : ∀ x ∈ W, ∃ (W' : X.affineOpens), x ∈ (W' : X.Opens) ∧ (W' : X.Opens) ≤ W ∧
      ∃ ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
          (op (OO D M (W' : X.Opens))),
        LocalRep n f D hD S M p (W' : X.Opens) ω ∧
        letI := MMP.Mori.functionFieldAlgebra f
        ∀ (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W')
          [Nonempty (O : (cU D).toScheme.Opens)],
          openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p O
            ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map
              (homOfLE hO).op ω)) = ρ) :
    ∃ θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
        (op (OO D M W)),
      Cond n f D hD S M p W θ ∧
      letI := MMP.Mori.functionFieldAlgebra f
      ∀ (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W)
        [Nonempty (O : (cU D).toScheme.Opens)],
        openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p O
          ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO).op θ)) = ρ := by
  classical
  let := MMP.Mori.functionFieldAlgebra f
  have : SmoothOfRelativeDimension n ((cU D).ι ≫ f) := by
    have h := (inferInstance : SmoothOfRelativeDimension (0 + n) ((cU D).ι ≫ f))
    rwa [zero_add] at h
  obtain ⟨β', hβ'⟩ := (openFormsMap_bijective (cU D) f p).2 ρ
  have hinj := (openFormsMap_bijective (cU D) f p).1
  choose W' hxW' hW'W ω hω hωρ using hloc
  -- the local forms on `U ∩ W ∩ U'` have rational form `β'`
  have hglue : ∀ u ∈ OO D M W, ∃ Wa : (cU D).toScheme.affineOpens,
      u ∈ (Wa : (cU D).toScheme.Opens) ∧ (Wa : (cU D).toScheme.Opens) ≤ OO D M W ∧
      ∃ ω' : Γ(((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ), Wa),
        ∀ _ : Nonempty (Wa : (cU D).toScheme.Opens), ratForm ((cU D).ι ≫ f) p Wa ω' = β' := by
    intro u hu
    set x : X := (cU D).ι u
    have hx : x ∈ W := hu.1
    obtain ⟨_, ⟨Wa, hWa, rfl⟩, huWa, hle⟩ :=
      (cU D).toScheme.isBasis_affineOpens.exists_subset_of_mem_open
        (show u ∈ OO D M (W' x hx : X.Opens) from ⟨hxW' x hx, hu.2⟩)
        (OO D M (W' x hx : X.Opens)).isOpen
    let Wa' : (cU D).toScheme.affineOpens := ⟨Wa, hWa⟩
    have hle' : (Wa' : (cU D).toScheme.Opens) ≤ OO D M (W' x hx : X.Opens) := hle
    refine ⟨Wa', huWa, hle'.trans (Scheme.Hom.preimage_mono _ (inf_le_inf_right _ (hW'W x hx))),
      (((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hle').op
        (ω x hx), fun hne => hinj ?_⟩
    rw [hβ']
    exact hωρ x hx Wa' hle'
  obtain ⟨θ, hθ⟩ := exists_form_of_forall_ratForm_eq ((cU D).ι ≫ f) (m := n) p β' hglue
  refine ⟨θ, fun x hx => ⟨W' x hx, hW'W x hx, hxW' x hx, ?_⟩, fun O hO _ => by
    rw [hθ O hO, hβ']⟩
  have e : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
      (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) (hW'W x hx)))).op θ =
      ω x hx := by
    refine eq_of_ratForm_eq ((cU D).ι ≫ f) (m := n) p _ _ fun Wa hWa _ => hinj ?_
    rw [hωρ x hx Wa hWa, ← hβ', ← hθ Wa (hWa.trans (Scheme.Hom.preimage_mono _
      (inf_le_inf_right _ (hW'W x hx))))]
    exact congrArg (fun w => openFormsMap (cU D) f p (ratForm ((cU D).ι ≫ f) p Wa w))
      (forms_map_map ((cU D).ι ≫ f) p _ _ θ)
  rw [e]
  exact hω x hx

end MMP.FourfoldProofs.FractionalLogComplexProof
