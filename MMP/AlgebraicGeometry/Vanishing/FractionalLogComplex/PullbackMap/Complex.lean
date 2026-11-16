module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Retract.Defs
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Retract.Sections
public import MMP.AlgebraicGeometry.DeRham.RationalForms.OverComplex

/-!
# The pull-back map of the retract

Let `K` be a model of the fractional logarithmic complex `C^•` (`IsCModel`), with terms the
`𝒪_V`-modules `F p` embedded by `ι` into the forms on `U ∩ W ∩ U'`, and let `g : V' ⟶ V` be a cover
on which the pull-back `θ ↦ g^*θ / z` lands in `Ω^•_{V'}(log S')(-S')` (`IMapSpec`). The
pull-back is a morphism of sheaves of `π⁻¹𝒪`-modules `F p ⟶ g_* Ω^p_{V'}(log S')(-S')`, and, when
`d(z⁻¹ g^*β) = z⁻¹ g^*(∇β)` on rational forms, a morphism of complexes
`K ⟶ g_* Ω^•_{V'}(log S')(-S')`. Each property is checked on rational forms, which determine the
sections of both sheaves.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.coverLogCx`: the complex `Ω^•_{V'}(log S')(-S')`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.iSec`: the pull-back of a section of `F p`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.iHom`: the pull-back as a morphism of sheaves.
* `MMP.FourfoldProofs.FractionalLogComplexProof.iCx`: the pull-back as a morphism of complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

attribute [local instance] HasDerivedCategory.standard

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

/-- The complex `Ω^•_{V'}(log S')(-S')` of sheaves of `(g ≫ π)⁻¹𝒪`-modules on `V'`. -/
noncomputable abbrev coverLogCx (n : ℕ) {V V' : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    (g : V' ⟶ V) [SmoothOfRelativeDimension n (g ≫ π)] (S' : MMP.Mori.Divisor V')
    (hS' : S'.IsRelativeSNC n (g ≫ π)) :
    CochainComplex (SheafOfModules.{0} (invRing (g ≫ π))) ℕ :=
  MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal

/-- Its direct image `g_* Ω^•_{V'}(log S')(-S')`, a complex of sheaves of `π⁻¹𝒪`-modules on
`V`. -/
noncomputable abbrev coverDI (n : ℕ) {V V' : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    (g : V' ⟶ V) [SmoothOfRelativeDimension n (g ≫ π)] (S' : MMP.Mori.Divisor V')
    (hS' : S'.IsRelativeSNC n (g ≫ π)) :
    CochainComplex (SheafOfModules.{0} (invRing π)) ℕ :=
  ((relDirectImage g π).mapHomologicalComplex _).obj (coverLogCx n π g S' hS')

/-- An open subscheme of a scheme smooth of relative dimension `n` is smooth of relative
dimension `n`. -/
theorem smoothOfRelativeDimension_ι_comp (n : ℕ) {X T : Scheme.{0}} (f : X ⟶ T)
    [SmoothOfRelativeDimension n f] (U : X.Opens) :
    SmoothOfRelativeDimension n (U.ι ≫ f) := by
  have h := (inferInstance : SmoothOfRelativeDimension (0 + n) (U.ι ≫ f))
  rwa [zero_add] at h

section Cover

variable (n : ℕ) {V V' : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) (g : V' ⟶ V)
  [IsIntegral V'] [SmoothOfRelativeDimension n (g ≫ π)] (S' : MMP.Mori.Divisor V')
  (hS' : S'.IsRelativeSNC n (g ≫ π)) [Nonempty (cU S')]

/-- A section of `g_* Ω^p_{V'}(log S')(-S')` over `W`, as a form on `(V' ∖ S') ∩ g⁻¹ W`. -/
noncomputable def coverVal (p : ℕ) (W : V.Opens) (y : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ g ≫ π)).piece (p : ℤ)).val.obj
      (op ((cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))) :=
  y.1

omit [IsIntegral V'] [Nonempty (cU S')] in
/-- A section of `g_* Ω^p_{V'}(log S')(-S')` is determined by its form on `(V' ∖ S') ∩ g⁻¹ W`. -/
theorem coverVal_injective (p : ℕ) (W : V.Opens) :
    Function.Injective (coverVal n π g S' hS' p W) :=
  fun _ _ h => Subtype.ext h

omit [IsIntegral V'] [Nonempty (cU S')] in
/-- The form of a sum of sections is the sum of their forms. -/
theorem coverVal_add (p : ℕ) (W : V.Opens) (y₁ y₂ : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    coverVal n π g S' hS' p W (y₁ + y₂) =
      coverVal n π g S' hS' p W y₁ + coverVal n π g S' hS' p W y₂ := rfl

omit [IsIntegral V'] [Nonempty (cU S')] in
/-- The action of `π⁻¹𝒪` on `g_* Ω^p_{V'}(log S')(-S')` is multiplication by the image of the
section in `𝒪_{V'}`. -/
theorem coverVal_smul (p : ℕ) (W : V.Opens) (a : (invRing π).obj.obj (op W))
    (y : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    coverVal n π g S' hS' p W (a • y) =
      (show (Stacks.RingedSpace.structureRingSheaf (cU S').toScheme.toRingedSpace).obj.obj
        (op ((cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))) from (cU S').ι.app (g ⁻¹ᵁ W)
          (((inverseImageStructureMap (g ≫ π)).hom.app (op (g ⁻¹ᵁ W))).hom
            (((relRingHom g π).hom.app (op W)).hom a))) • coverVal n π g S' hS' p W y :=
  MMP.Mori.Divisor.LogSpreadingProof.G1.KX_smul (g ≫ π) (cU S') p
    (W := g ⁻¹ᵁ W) (((relRingHom g π).hom.app (op W)).hom a) y.1

omit [IsIntegral V'] [Nonempty (cU S')] in
/-- Restriction of sections of `g_* Ω^p_{V'}(log S')(-S')` is restriction of forms. -/
theorem coverVal_map (p : ℕ) {W W' : V.Opens} (h : W' ≤ W)
    (y : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    coverVal n π g S' hS' p W' (((coverDI n π g S' hS').X p).val.map (homOfLE h).op y) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ g ≫ π)).piece (p : ℤ)).val.map
        (homOfLE (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ h))).op
          (coverVal n π g S' hS' p W y) := rfl

omit [IsIntegral V'] [Nonempty (cU S')] in
/-- The differential of `g_* Ω^•_{V'}(log S')(-S')` is the de Rham differential. -/
theorem coverVal_d (p : ℕ) (W : V.Opens) (y : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    coverVal n π g S' hS' (p + 1) W (((coverDI n π g S' hS').d p (p + 1)).val.app (op W) y) =
      ((Scheme.Hom.deRhamComplex ((cU S').ι ≫ g ≫ π)).d p (p + 1)).val.app
        (op ((cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))) (coverVal n π g S' hS' p W y) := by
  unfold coverVal
  rw [Functor.mapHomologicalComplex_obj_d, MMP.Mori.Divisor.relativeLogDeRhamComplex_d]
  rfl

/-- **Sections of `g_* Ω^p_{V'}(log S')(-S')` are determined by their rational forms.** -/
theorem coverDI_ext (p : ℕ) (W : V.Opens) (y₁ y₂ : ((coverDI n π g S' hS').X p).val.obj (op W))
    (h : ∀ (O' : (cU S').toScheme.affineOpens)
      (hO' : (O' : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))
      [Nonempty (O' : (cU S').toScheme.Opens)],
      ratV (cU S') (g ≫ π) p O' hO' (coverVal n π g S' hS' p W y₁) =
        ratV (cU S') (g ≫ π) p O' hO' (coverVal n π g S' hS' p W y₂)) :
    y₁ = y₂ := by
  have := smoothOfRelativeDimension_ι_comp n (g ≫ π) (cU S')
  exact coverVal_injective n π g S' hS' p W (eq_of_ratV_eq (cU S') (g ≫ π) (m := n) p _ _ h)

/-- A logarithmic form on `(V' ∖ S') ∩ g⁻¹ W`, as a section of `g_* Ω^p_{V'}(log S')(-S')`. -/
noncomputable def coverSec (p : ℕ) (W : V.Opens)
    (θ' : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ g ≫ π)).piece
      (p : ℤ)).val.obj (op ((cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))))
    (hθ' : θ' ∈ MMP.Mori.Divisor.relativeLogForms n (g ≫ π) S' hS' S'.suppIdeal p (g ⁻¹ᵁ W)) :
    ((coverDI n π g S' hS').X p).val.obj (op W) :=
  ⟨θ', (mem_relativeLogDeRhamTerms_iff n (g ≫ π) S' hS' p (g ⁻¹ᵁ W) θ').2 hθ'⟩

omit [IsIntegral V'] [Nonempty (cU S')] in
/-- The form of the section `coverSec θ'` is `θ'`. -/
@[simp] theorem coverVal_coverSec (p : ℕ) (W : V.Opens)
    (θ' : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ g ≫ π)).piece
      (p : ℤ)).val.obj (op ((cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))))
    (hθ' : θ' ∈ MMP.Mori.Divisor.relativeLogForms n (g ≫ π) S' hS' S'.suppIdeal p (g ⁻¹ᵁ W)) :
    coverVal n π g S' hS' p W (coverSec n π g S' hS' p W θ' hθ') = θ' := rfl

omit [IsIntegral V'] [Nonempty (cU S')] in
/-- The sections of `g_* Ω^p_{V'}(log S')(-S')` are logarithmic forms. -/
theorem coverDI_mem (p : ℕ) (W : V.Opens) (y : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    coverVal n π g S' hS' p W y ∈
      MMP.Mori.Divisor.relativeLogForms n (g ≫ π) S' hS' S'.suppIdeal p (g ⁻¹ᵁ W) :=
  (mem_relativeLogDeRhamTerms_iff n (g ≫ π) S' hS' p (g ⁻¹ᵁ W) y.1).1 y.2

end Cover

section Model

variable (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n π] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (N : ℕ)
  (u : Γ(V, cU' D M)) [Nonempty (cU D)]
  {K : CochainComplex (SheafOfModules.{0} (invRing π)) ℕ} {F : ℕ → V.Modules}
  {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
  {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))}

omit [IsIntegral V] [Nonempty (cU D)] in
/-- The images of `ι` satisfy `Cond`: they are sections of `C^p`. -/
theorem cond_of_isCModel (hK : IsCModel n π D hD S M N u K F e ι) (p : ℕ) (W : V.Opens)
    (f : (F p).val.obj (op W)) : Cond n π D hD S M p W (ι p W f) :=
  (hK.2.2.2.2.1 p W (ι p W f)).1 ⟨f, rfl⟩

omit [IsIntegral V] [Nonempty (cU D)] in
/-- Every section of `C^p` is in the image of `ι`. -/
theorem exists_eq_of_cond (hK : IsCModel n π D hD S M N u K F e ι) (p : ℕ) (W : V.Opens)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))) (hθ : Cond n π D hD S M p W θ) : ∃ f, ι p W f = θ :=
  (hK.2.2.2.2.1 p W θ).2 hθ

/-- **Sections of `F p` are determined by the rational forms of their images under `ι`.** -/
theorem model_ext (hK : IsCModel n π D hD S M N u K F e ι) (p : ℕ) (W : V.Opens)
    (f₁ f₂ : (F p).val.obj (op W))
    (h : ∀ (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W)
      [Nonempty (O : (cU D).toScheme.Opens)],
      ratV (cU D) π p O hO (ι p W f₁) = ratV (cU D) π p O hO (ι p W f₂)) :
    f₁ = f₂ := by
  have := smoothOfRelativeDimension_ι_comp n π (cU D)
  exact hK.1 p W (eq_of_ratV_eq (cU D) π (m := n) p _ _ h)

section IMap

variable [Nonempty (cU' D M)] {V' : Scheme.{0}} (g : V' ⟶ V) [IsFinite g] [Surjective g]
  [IsIntegral V']
  [SmoothOfRelativeDimension n (g ≫ π)] (S' : MMP.Mori.Divisor V')
  (hS' : S'.IsRelativeSNC n (g ≫ π)) [Nonempty (cU S')] (z : V'.functionField)

/-- The pull-back `g^*θ / z` of the image of a section of `F p`, a logarithmic form on
`(V' ∖ S') ∩ g⁻¹ W`. -/
noncomputable def iForm (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens) (f : (F p).val.obj (op W)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ g ≫ π)).piece (p : ℤ)).val.obj
      (op ((cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))) :=
  (hI p W (ι p W f) (cond_of_isCModel n π D hD S M N u hK p W f)).choose

omit [Nonempty (cU' D M)] in
/-- The pull-back `g^*θ / z` is a logarithmic form in `Ω^p_{V'}(log S')(-S')`. -/
theorem iForm_mem (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens) (f : (F p).val.obj (op W)) :
    iForm n π D hD S M N u g S' hS' z hK hI p W f ∈
      MMP.Mori.Divisor.relativeLogForms n (g ≫ π) S' hS' S'.suppIdeal p (g ⁻¹ᵁ W) :=
  (hI p W (ι p W f) (cond_of_isCModel n π D hD S M N u hK p W f)).choose_spec.1

omit [Nonempty (cU' D M)] in
/-- **The rational forms of the pull-back**: `z⁻¹ g^*` of the rational form of `θ`. -/
theorem iForm_spec (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens) (f : (F p).val.obj (op W))
    (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W)
    [hO₁ : Nonempty (O : (cU D).toScheme.Opens)]
    (O' : (cU S').toScheme.affineOpens)
    (hO' : (O' : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))
    [hO₁' : Nonempty (O' : (cU S').toScheme.Opens)] :
    letI := MMP.Mori.functionFieldAlgebra π
    letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
    letI := MMP.Mori.functionFieldMapAlgebra g
    haveI := MMP.Mori.isScalarTower_functionFieldMap π g
    ratV (cU S') (g ≫ π) p O' hO'
        (hI p W (ι p W f) (cond_of_isCModel n π D hD S M N u hK p W f)).choose =
      z⁻¹ • KaehlerDifferential.mapExteriorPower ℂ V.functionField V'.functionField p
        (ratV (cU D) π p O hO (ι p W f)) := by
  have h := @(hI p W (ι p W f) (cond_of_isCModel n π D hD S M N u hK p W f)).choose_spec.2 O hO
    hO₁ O' hO' hO₁'
  rw [ratV_def, ratV_def]
  with_reducible exact h

/-- The pull-back of a section of `F p`, as a section of `g_* Ω^p_{V'}(log S')(-S')`. -/
noncomputable def iSec (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens) (f : (F p).val.obj (op W)) :
    ((coverDI n π g S' hS').X p).val.obj (op W) :=
  coverSec n π g S' hS' p W (iForm n π D hD S M N u g S' hS' z hK hI p W f)
    (iForm_mem n π D hD S M N u g S' hS' z hK hI p W f)

omit [Nonempty (cU' D M)] in
/-- The form of the section `iSec f` is the form chosen by `IMapSpec` for `ι f`. -/
theorem coverVal_iSec (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens) (f : (F p).val.obj (op W)) :
    coverVal n π g S' hS' p W (iSec n π D hD S M N u g S' hS' z hK hI p W f) =
      (hI p W (ι p W f) (cond_of_isCModel n π D hD S M N u hK p W f)).choose := rfl

/-- **The pull-back is additive.** -/
theorem iSec_add (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens)
    (f₁ f₂ : (F p).val.obj (op W)) :
    iSec n π D hD S M N u g S' hS' z hK hI p W (f₁ + f₂) =
      iSec n π D hD S M N u g S' hS' z hK hI p W f₁ +
        iSec n π D hD S M N u g S' hS' z hK hI p W f₂ := by
  apply coverDI_ext
  intro O' hO' hne'
  obtain ⟨O, hO, hne⟩ := exists_affineOpen_le_OO D M W (nonempty_of_le_preimage g S' hO')
  rw [coverVal_add, ratV_add, coverVal_iSec, coverVal_iSec, coverVal_iSec,
    iForm_spec n π D hD S M N u g S' hS' z hK hI p W (f₁ + f₂) O hO O' hO',
    iForm_spec n π D hD S M N u g S' hS' z hK hI p W f₁ O hO O' hO',
    iForm_spec n π D hD S M N u g S' hS' z hK hI p W f₂ O hO O' hO', hK.2.1 p W f₁ f₂,
    ratV_add, map_add, smul_add]

/-- **The pull-back commutes with restriction.** -/
theorem iSec_map (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (p : ℕ) {W W' : V.Opens} (h : W' ≤ W)
    (f : (F p).val.obj (op W)) :
    iSec n π D hD S M N u g S' hS' z hK hI p W' ((F p).val.map (homOfLE h).op f) =
      ((coverDI n π g S' hS').X p).val.map (homOfLE h).op
        (iSec n π D hD S M N u g S' hS' z hK hI p W f) := by
  apply coverDI_ext
  intro O' hO' hne'
  obtain ⟨O, hO, hne⟩ := exists_affineOpen_le_OO D M W' (nonempty_of_le_preimage g S' hO')
  rw [coverVal_iSec n π D hD S M N u g S' hS' z hK hI p W' ((F p).val.map (homOfLE h).op f),
    iForm_spec n π D hD S M N u g S' hS' z hK hI p W' ((F p).val.map (homOfLE h).op f) O hO O'
      hO', hK.2.2.2.1 p W W' h f, ratV_map, coverVal_map, ratV_map, coverVal_iSec,
    iForm_spec n π D hD S M N u g S' hS' z hK hI p W f O _ O' _]

/-- **The pull-back is linear over `π⁻¹𝒪`.** -/
theorem iSec_smul (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens)
    (a : (invRing π).obj.obj (op W)) (f : (F p).val.obj (op W)) :
    iSec n π D hD S M N u g S' hS' z hK hI p W
        ((show V.ringCatSheaf.obj.obj (op W) from
          ((inverseImageStructureMap π).hom.app (op W)).hom a) • f) =
      a • iSec n π D hD S M N u g S' hS' z hK hI p W f := by
  let := MMP.Mori.functionFieldAlgebra π
  let := MMP.Mori.functionFieldAlgebra (g ≫ π)
  let := MMP.Mori.functionFieldMapAlgebra g
  have := MMP.Mori.isScalarTower_functionFieldMap π g
  apply coverDI_ext
  intro O' hO' hne'
  obtain ⟨O, hO, hne⟩ := exists_affineOpen_le_OO D M W (nonempty_of_le_preimage g S' hO')
  rw [coverVal_smul, ratV_smul, coverVal_iSec n π D hD S M N u g S' hS' z hK hI p W
      ((show V.ringCatSheaf.obj.obj (op W) from
          ((inverseImageStructureMap π).hom.app (op W)).hom a) • f), coverVal_iSec,
    iForm_spec n π D hD S M N u g S' hS' z hK hI p W
      ((show V.ringCatSheaf.obj.obj (op W) from
          ((inverseImageStructureMap π).hom.app (op W)).hom a) • f) O hO O' hO',
    iForm_spec n π D hD S M N u g S' hS' z hK hI p W f O hO O' hO',
    ratV_eq_smul_of_incl_eq (cU D) π p O hO _ (ι p W f) _ (hK.2.2.1 p W _ f),
    germ_inverseImageStructureMap_relRingHom π g D M S' W a hO hO', LinearMap.map_smul_of_tower,
    algebraMap_smul, smul_comm]

/-- **The pull-back commutes with the differentials**: `d(z⁻¹ g^*θ) = z⁻¹ g^*(∇θ)`. -/
theorem iSec_d (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (ψK : V.functionField)
    (hψ : V.germToFunctionField (cU' D M) u = ψK)
    (hRC : letI := MMP.Mori.functionFieldAlgebra π
      letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
      letI := MMP.Mori.functionFieldMapAlgebra g
      haveI := MMP.Mori.isScalarTower_functionFieldMap π g
      haveI := finiteDimensional_functionFieldMap g
      haveI := isSeparable_functionFieldMap π g
      RatCompat ℂ V.functionField V'.functionField N ψK z)
    (p : ℕ) (W : V.Opens) (x : (K.X p).val.obj (op W)) :
    iSec n π D hD S M N u g S' hS' z hK hI (p + 1) W
        ((e (p + 1)).hom.val.app (op W) ((K.d p (p + 1)).val.app (op W) x)) =
      ((coverDI n π g S' hS').d p (p + 1)).val.app (op W)
        (iSec n π D hD S M N u g S' hS' z hK hI p W ((e p).hom.val.app (op W) x)) := by
  let := MMP.Mori.functionFieldAlgebra π
  let := MMP.Mori.functionFieldAlgebra (g ≫ π)
  let := MMP.Mori.functionFieldMapAlgebra g
  have := MMP.Mori.isScalarTower_functionFieldMap π g
  have := finiteDimensional_functionFieldMap g
  have := isSeparable_functionFieldMap π g
  apply coverDI_ext
  intro O' hO' hne'
  obtain ⟨O, hO, hne⟩ := exists_affineOpen_le_OO D M W (nonempty_of_le_preimage g S' hO')
  have : Nonempty (W ⊓ cU' D M : V.Opens) := let ⟨x⟩ := hne; ⟨⟨_, hO x.2⟩⟩
  rw [coverVal_d, ratV_d, coverVal_iSec n π D hD S M N u g S' hS' z hK hI (p + 1) W
      ((e (p + 1)).hom.val.app (op W) ((K.d p (p + 1)).val.app (op W) x)),
    coverVal_iSec n π D hD S M N u g S' hS' z hK hI p W ((e p).hom.val.app (op W) x),
    iForm_spec n π D hD S M N u g S' hS' z hK hI (p + 1) W
      ((e (p + 1)).hom.val.app (op W) ((K.d p (p + 1)).val.app (op W) x)) O hO O' hO',
    iForm_spec n π D hD S M N u g S' hS' z hK hI p W ((e p).hom.val.app (op W) x) O hO O' hO']
  have hn := ratV_nabla (cU D) π p N O hO _ _ _ (hK.2.2.2.2.2 p W x)
  rw [openFunctionFieldEquiv_germ_restrict (cU D) hO, germToFunctionField_map inf_le_right,
    hψ] at hn
  exact (hRC.1 p _ _ hn).symm

/-- **The pull-back as a morphism of sheaves of `π⁻¹𝒪`-modules**
`F p ⟶ g_* Ω^p_{V'}(log S')(-S')`. -/
noncomputable def iHom (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (p : ℕ) :
    (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p) ⟶
        (coverDI n π g S' hS').X p :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun f => iSec n π D hD S M N u g S' hS' z hK hI p W.unop f)
        (fun f₁ f₂ => iSec_add n π D hD S M N u g S' hS' z hK hI p W.unop f₁ f₂))
      naturality := fun {W W'} h => by
        ext f
        rw [show h = (homOfLE (leOfHom h.unop)).op from Subsingleton.elim _ _]
        exact iSec_map n π D hD S M N u g S' hS' z hK hI p (leOfHom h.unop) f }
    (fun W a f => iSec_smul n π D hD S M N u g S' hS' z hK hI p W.unop a f)⟩

/-- On sections over `W`, `iHom` is `iSec`. -/
@[simp] theorem iHom_app (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens) (f : (F p).val.obj (op W)) :
    (iHom n π D hD S M N u g S' hS' z hK hI p).val.app (op W) f =
      iSec n π D hD S M N u g S' hS' z hK hI p W f := rfl

/-- **The pull-back as a morphism of complexes** `K ⟶ g_* Ω^•_{V'}(log S')(-S')`. -/
noncomputable def iCx (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (ψK : V.functionField)
    (hψ : V.germToFunctionField (cU' D M) u = ψK)
    (hRC : letI := MMP.Mori.functionFieldAlgebra π
      letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
      letI := MMP.Mori.functionFieldMapAlgebra g
      haveI := MMP.Mori.isScalarTower_functionFieldMap π g
      haveI := finiteDimensional_functionFieldMap g
      haveI := isSeparable_functionFieldMap π g
      RatCompat ℂ V.functionField V'.functionField N ψK z) :
    K ⟶ coverDI n π g S' hS' where
  f p := (e p).hom ≫ iHom n π D hD S M N u g S' hS' z hK hI p
  comm' := by
    rintro p q rfl
    ext W x
    exact (iSec_d n π D hD S M N u g S' hS' z hK hI ψK hψ hRC p W.unop x).symm

end IMap

end Model

end MMP.FourfoldProofs.FractionalLogComplexProof
