module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.PullbackMap.Complex

/-!
# The trace map of the retract

Let `K` be a model of the fractional logarithmic complex `C^•` (`IsCModel`) and `g : V' ⟶ V` a
cover on which the trace map `ω' ↦ [k(V') : k(V)]⁻¹ Tr(z ω')` carries
`Ω^p_{V'}(log S')(-S')` into `C^p` (`RMapSpec`). The trace map is a morphism of sheaves of
`π⁻¹𝒪`-modules `g_* Ω^p_{V'}(log S')(-S') ⟶ F p`; when `r d = ∇ r` on rational forms, a morphism of
complexes `g_* Ω^•_{V'}(log S')(-S') ⟶ K`; and when `r i = 1` on rational forms, it is a left
inverse of the pull-back map. Each property is checked on rational forms.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.rSec`: the trace of a section.
* `MMP.FourfoldProofs.FractionalLogComplexProof.rHom`: the trace as a morphism of sheaves.
* `MMP.FourfoldProofs.FractionalLogComplexProof.rCx`: the trace as a morphism of complexes.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.iCx_comp_rCx`: the trace map is a left inverse of the
  pull-back map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

section RMap

variable (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n π] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (N : ℕ)
  (u : Γ(V, cU' D M)) [Nonempty (cU D)] [Nonempty (cU' D M)]
  {K : CochainComplex (SheafOfModules.{0} (invRing π)) ℕ} {F : ℕ → V.Modules}
  {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
  {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))}
  {V' : Scheme.{0}} (g : V' ⟶ V) [IsFinite g] [Surjective g] [IsIntegral V']
  [SmoothOfRelativeDimension n (g ≫ π)] (S' : MMP.Mori.Divisor V')
  (hS' : S'.IsRelativeSNC n (g ≫ π)) [Nonempty (cU S')] (z : V'.functionField)

/-- The trace `[k(V') : k(V)]⁻¹ Tr(z ω')` of a section of `g_* Ω^p_{V'}(log S')(-S')`, as a
relative differential form on `OO D M W`. -/
noncomputable def rTheta (hR : RMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens)
    (y : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W)) :=
  (hR p W (coverVal n π g S' hS' p W y) (coverDI_mem n π g S' hS' p W y)).choose

/-- The trace of a section, as a section of `F p`. -/
noncomputable def rSec (hK : IsCModel n π D hD S M N u K F e ι)
    (hR : RMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens)
    (y : ((coverDI n π g S' hS').X p).val.obj (op W)) : (F p).val.obj (op W) :=
  (exists_eq_of_cond n π D hD S M N u hK p W (rTheta n π D hD S M g S' hS' z hR p W y)
    (hR p W (coverVal n π g S' hS' p W y) (coverDI_mem n π g S' hS' p W y)).choose_spec.1).choose

omit [Nonempty (cU' D M)] in
/-- The image under `ι` of the trace of a section is the rational form `rTheta` of the trace. -/
theorem ι_rSec (hK : IsCModel n π D hD S M N u K F e ι)
    (hR : RMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens)
    (y : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    ι p W (rSec n π D hD S M N u g S' hS' z hK hR p W y) =
      (hR p W (coverVal n π g S' hS' p W y) (coverDI_mem n π g S' hS' p W y)).choose :=
  (exists_eq_of_cond n π D hD S M N u hK p W (rTheta n π D hD S M g S' hS' z hR p W y)
    (hR p W (coverVal n π g S' hS' p W y)
      (coverDI_mem n π g S' hS' p W y)).choose_spec.1).choose_spec

omit [Nonempty (cU' D M)] in
/-- **The rational forms of the trace**: `[k(V') : k(V)]⁻¹ Tr(z ω')`. -/
theorem rSec_spec (hK : IsCModel n π D hD S M N u K F e ι)
    (hR : RMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens)
    (y : ((coverDI n π g S' hS').X p).val.obj (op W))
    (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W)
    [hO₁ : Nonempty (O : (cU D).toScheme.Opens)]
    (O' : (cU S').toScheme.affineOpens)
    (hO' : (O' : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))
    [hO₁' : Nonempty (O' : (cU S').toScheme.Opens)] :
    letI := MMP.Mori.functionFieldAlgebra π
    letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
    letI := MMP.Mori.functionFieldMapAlgebra g
    haveI := MMP.Mori.isScalarTower_functionFieldMap π g
    haveI := finiteDimensional_functionFieldMap g
    haveI := isSeparable_functionFieldMap π g
    ratV (cU D) π p O hO (ι p W (rSec n π D hD S M N u g S' hS' z hK hR p W y)) =
      ((Module.finrank V.functionField V'.functionField : V.functionField))⁻¹ •
        formsTrace ℂ V.functionField V'.functionField p
          (z • ratV (cU S') (g ≫ π) p O' hO' (coverVal n π g S' hS' p W y)) := by
  have h := @(hR p W (coverVal n π g S' hS' p W y)
    (coverDI_mem n π g S' hS' p W y)).choose_spec.2 O hO hO₁ O' hO' hO₁'
  rw [ι_rSec n π D hD S M N u g S' hS' z hK hR p W y, ratV_def, ratV_def]
  with_reducible exact h

omit [Nonempty (cU' D M)] in
/-- **The trace is additive.** -/
theorem rSec_add (hK : IsCModel n π D hD S M N u K F e ι)
    (hR : RMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens)
    (y₁ y₂ : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    rSec n π D hD S M N u g S' hS' z hK hR p W (y₁ + y₂) =
      rSec n π D hD S M N u g S' hS' z hK hR p W y₁ +
        rSec n π D hD S M N u g S' hS' z hK hR p W y₂ := by
  refine model_ext n π D hD S M N u hK p W _ _ fun O hO hne => ?_
  obtain ⟨O', hO', hne'⟩ := exists_affineOpen_le_preimage g S' W (nonempty_of_le_OO D M hO)
  rw [rSec_spec n π D hD S M N u g S' hS' z hK hR p W (y₁ + y₂) O hO O' hO', coverVal_add,
    ratV_add, smul_add, map_add, smul_add, hK.2.1 p W, ratV_add,
    rSec_spec n π D hD S M N u g S' hS' z hK hR p W y₁ O hO O' hO',
    rSec_spec n π D hD S M N u g S' hS' z hK hR p W y₂ O hO O' hO']

omit [Nonempty (cU' D M)] in
/-- **The trace is linear over `π⁻¹𝒪`.** -/
theorem rSec_smul (hK : IsCModel n π D hD S M N u K F e ι)
    (hR : RMapSpec n π D hD S M g S' hS' z) (p : ℕ) (W : V.Opens)
    (a : (invRing π).obj.obj (op W)) (y : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    rSec n π D hD S M N u g S' hS' z hK hR p W (a • y) =
      (show V.ringCatSheaf.obj.obj (op W) from
          ((inverseImageStructureMap π).hom.app (op W)).hom a) •
        rSec n π D hD S M N u g S' hS' z hK hR p W y := by
  let := MMP.Mori.functionFieldAlgebra π
  let := MMP.Mori.functionFieldAlgebra (g ≫ π)
  let := MMP.Mori.functionFieldMapAlgebra g
  have := MMP.Mori.isScalarTower_functionFieldMap π g
  have := finiteDimensional_functionFieldMap g
  have := isSeparable_functionFieldMap π g
  refine model_ext n π D hD S M N u hK p W _ _ fun O hO hne => ?_
  obtain ⟨O', hO', hne'⟩ := exists_affineOpen_le_preimage g S' W (nonempty_of_le_OO D M hO)
  rw [rSec_spec n π D hD S M N u g S' hS' z hK hR p W (a • y) O hO O' hO', coverVal_smul,
    ratV_smul, germ_inverseImageStructureMap_relRingHom π g D M S' W a hO hO',
    ratV_eq_smul_of_incl_eq (cU D) π p O hO _
      (ι p W (rSec n π D hD S M N u g S' hS' z hK hR p W y)) _ (hK.2.2.1 p W _ _),
    rSec_spec n π D hD S M N u g S' hS' z hK hR p W y O hO O' hO', smul_comm z, algebraMap_smul,
    map_smul, smul_comm]

omit [Nonempty (cU' D M)] in
/-- **The trace commutes with restriction.** -/
theorem rSec_map (hK : IsCModel n π D hD S M N u K F e ι)
    (hR : RMapSpec n π D hD S M g S' hS' z) (p : ℕ) {W W' : V.Opens} (h : W' ≤ W)
    (y : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    rSec n π D hD S M N u g S' hS' z hK hR p W'
        (((coverDI n π g S' hS').X p).val.map (homOfLE h).op y) =
      (F p).val.map (homOfLE h).op (rSec n π D hD S M N u g S' hS' z hK hR p W y) := by
  refine model_ext n π D hD S M N u hK p W' _ _ fun O hO hne => ?_
  obtain ⟨O', hO', hne'⟩ := exists_affineOpen_le_preimage g S' W' (nonempty_of_le_OO D M hO)
  rw [rSec_spec n π D hD S M N u g S' hS' z hK hR p W'
      (((coverDI n π g S' hS').X p).val.map (homOfLE h).op y) O hO O' hO', coverVal_map,
    ratV_map, hK.2.2.2.1 p W W' h, ratV_map,
    rSec_spec n π D hD S M N u g S' hS' z hK hR p W y O _ O' _]

omit [Nonempty (cU' D M)] in
/-- **The trace is a left inverse of the pull-back**: `[k(V') : k(V)]⁻¹ Tr(z · g^*θ / z) = θ`. -/
theorem rSec_iSec (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (hR : RMapSpec n π D hD S M g S' hS' z)
    (ψK : V.functionField)
    (hRC : letI := MMP.Mori.functionFieldAlgebra π
      letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
      letI := MMP.Mori.functionFieldMapAlgebra g
      haveI := MMP.Mori.isScalarTower_functionFieldMap π g
      haveI := finiteDimensional_functionFieldMap g
      haveI := isSeparable_functionFieldMap π g
      RatCompat ℂ V.functionField V'.functionField N ψK z)
    (p : ℕ) (W : V.Opens) (f : (F p).val.obj (op W)) :
    rSec n π D hD S M N u g S' hS' z hK hR p W (iSec n π D hD S M N u g S' hS' z hK hI p W f) =
      f := by
  refine model_ext n π D hD S M N u hK p W _ _ fun O hO hne => ?_
  obtain ⟨O', hO', hne'⟩ := exists_affineOpen_le_preimage g S' W (nonempty_of_le_OO D M hO)
  rw [rSec_spec n π D hD S M N u g S' hS' z hK hR p W _ O hO O' hO',
    coverVal_iSec n π D hD S M N u g S' hS' z hK hI p W f,
    iForm_spec n π D hD S M N u g S' hS' z hK hI p W f O hO O' hO']
  exact hRC.2.2 p _

omit [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [Nonempty (cU D)] in
/-- `(e p).hom` undoes `(e p).inv` on sections over `W`. -/
theorem e_inv_hom_id_apply (p : ℕ) (W : V.Opens) (f : (F p).val.obj (op W)) :
    (e p).hom.val.app (op W) ((e p).inv.val.app (op W) f) = f :=
  congrArg (fun φ => φ.val.app (op W) f) (e p).inv_hom_id

omit [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [Nonempty (cU D)] in
/-- `(e p).inv` undoes `(e p).hom` on sections over `W`. -/
theorem e_hom_inv_id_apply (p : ℕ) (W : V.Opens) (x : (K.X p).val.obj (op W)) :
    (e p).inv.val.app (op W) ((e p).hom.val.app (op W) x) = x :=
  congrArg (fun φ => φ.val.app (op W) x) (e p).hom_inv_id

/-- **The trace commutes with the differentials**: `r d = ∇ r`. -/
theorem rSec_d (hK : IsCModel n π D hD S M N u K F e ι)
    (hR : RMapSpec n π D hD S M g S' hS' z) (ψK : V.functionField)
    (hψ : V.germToFunctionField (cU' D M) u = ψK)
    (hRC : letI := MMP.Mori.functionFieldAlgebra π
      letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
      letI := MMP.Mori.functionFieldMapAlgebra g
      haveI := MMP.Mori.isScalarTower_functionFieldMap π g
      haveI := finiteDimensional_functionFieldMap g
      haveI := isSeparable_functionFieldMap π g
      RatCompat ℂ V.functionField V'.functionField N ψK z)
    (p : ℕ) (W : V.Opens) (y : ((coverDI n π g S' hS').X p).val.obj (op W)) :
    rSec n π D hD S M N u g S' hS' z hK hR (p + 1) W
        (((coverDI n π g S' hS').d p (p + 1)).val.app (op W) y) =
      (e (p + 1)).hom.val.app (op W) ((K.d p (p + 1)).val.app (op W)
        ((e p).inv.val.app (op W) (rSec n π D hD S M N u g S' hS' z hK hR p W y))) := by
  let := MMP.Mori.functionFieldAlgebra π
  let := MMP.Mori.functionFieldAlgebra (g ≫ π)
  let := MMP.Mori.functionFieldMapAlgebra g
  have := MMP.Mori.isScalarTower_functionFieldMap π g
  have := finiteDimensional_functionFieldMap g
  have := isSeparable_functionFieldMap π g
  refine model_ext n π D hD S M N u hK (p + 1) W _ _ fun O hO hne => ?_
  obtain ⟨O', hO', hne'⟩ := exists_affineOpen_le_preimage g S' W (nonempty_of_le_OO D M hO)
  have : Nonempty (W ⊓ cU' D M : V.Opens) := let ⟨x⟩ := hne; ⟨⟨_, hO x.2⟩⟩
  rw [rSec_spec n π D hD S M N u g S' hS' z hK hR (p + 1) W _ O hO O' hO', coverVal_d, ratV_d]
  have hn := ratV_nabla (cU D) π p N O hO _ _ _
    (hK.2.2.2.2.2 p W ((e p).inv.val.app (op W) (rSec n π D hD S M N u g S' hS' z hK hR p W y)))
  rw [openFunctionFieldEquiv_germ_restrict (cU D) hO, germToFunctionField_map inf_le_right, hψ,
    e_inv_hom_id_apply, rSec_spec n π D hD S M N u g S' hS' z hK hR p W y O hO O' hO'] at hn
  have h1 := hRC.1 p _ _ hn
  have h2 := hRC.1 p _ _ (hRC.2.1 p (ratV (cU S') (g ≫ π) p O' hO' (coverVal n π g S' hS' p W y)))
  rw [← hRC.2.2 (p + 1) (ratV (cU D) π (p + 1) O hO _), ← h1, h2, hRC.2.2]

/-- **The trace as a morphism of sheaves of `π⁻¹𝒪`-modules**
`g_* Ω^p_{V'}(log S')(-S') ⟶ F p`. -/
noncomputable def rHom (hK : IsCModel n π D hD S M N u K F e ι)
    (hR : RMapSpec n π D hD S M g S' hS' z) (p : ℕ) :
    (coverDI n π g S' hS').X p ⟶
      (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p) :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun y => rSec n π D hD S M N u g S' hS' z hK hR p W.unop y)
        (fun y₁ y₂ => rSec_add n π D hD S M N u g S' hS' z hK hR p W.unop y₁ y₂))
      naturality := fun {W W'} h => by
        ext y
        rw [show h = (homOfLE (leOfHom h.unop)).op from Subsingleton.elim _ _]
        exact rSec_map n π D hD S M N u g S' hS' z hK hR p (leOfHom h.unop) y }
    (fun W a y => rSec_smul n π D hD S M N u g S' hS' z hK hR p W.unop a y)⟩

/-- **The trace as a morphism of complexes** `g_* Ω^•_{V'}(log S')(-S') ⟶ K`. -/
noncomputable def rCx (hK : IsCModel n π D hD S M N u K F e ι)
    (hR : RMapSpec n π D hD S M g S' hS' z) (ψK : V.functionField)
    (hψ : V.germToFunctionField (cU' D M) u = ψK)
    (hRC : letI := MMP.Mori.functionFieldAlgebra π
      letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
      letI := MMP.Mori.functionFieldMapAlgebra g
      haveI := MMP.Mori.isScalarTower_functionFieldMap π g
      haveI := finiteDimensional_functionFieldMap g
      haveI := isSeparable_functionFieldMap π g
      RatCompat ℂ V.functionField V'.functionField N ψK z) :
    coverDI n π g S' hS' ⟶ K where
  f p := rHom n π D hD S M N u g S' hS' z hK hR p ≫ (e p).inv
  comm' := by
    rintro p q rfl
    ext W y
    change (K.d p (p + 1)).val.app W ((e p).inv.val.app W
        (rSec n π D hD S M N u g S' hS' z hK hR p W.unop y)) =
      (e (p + 1)).inv.val.app W (rSec n π D hD S M N u g S' hS' z hK hR (p + 1) W.unop
        (((coverDI n π g S' hS').d p (p + 1)).val.app W y))
    rw [rSec_d n π D hD S M N u g S' hS' z hK hR ψK hψ hRC p W.unop y, e_hom_inv_id_apply]

/-- **The trace map is a left inverse of the pull-back map**: `i ≫ r = 𝟙`. -/
theorem iCx_comp_rCx (hK : IsCModel n π D hD S M N u K F e ι)
    (hI : IMapSpec n π D hD S M g S' hS' z) (hR : RMapSpec n π D hD S M g S' hS' z)
    (ψK : V.functionField) (hψ : V.germToFunctionField (cU' D M) u = ψK)
    (hRC : letI := MMP.Mori.functionFieldAlgebra π
      letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
      letI := MMP.Mori.functionFieldMapAlgebra g
      haveI := MMP.Mori.isScalarTower_functionFieldMap π g
      haveI := finiteDimensional_functionFieldMap g
      haveI := isSeparable_functionFieldMap π g
      RatCompat ℂ V.functionField V'.functionField N ψK z) :
    iCx n π D hD S M N u g S' hS' z hK hI ψK hψ hRC ≫
      rCx n π D hD S M N u g S' hS' z hK hR ψK hψ hRC = 𝟙 K := by
  ext p W x
  change (e p).inv.val.app W (rSec n π D hD S M N u g S' hS' z hK hR p W.unop
    (iSec n π D hD S M N u g S' hS' z hK hI p W.unop ((e p).hom.val.app W x))) = x
  rw [rSec_iSec n π D hD S M N u g S' hS' z hK hI hR ψK hRC p W.unop ((e p).hom.val.app W x),
    e_hom_inv_id_apply]

end RMap

end MMP.FourfoldProofs.FractionalLogComplexProof
