module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.Basic

/-!
# The inclusion of a twist of the fractional logarithmic complex

Let `C^•` be the fractional logarithmic complex `𝒪_V(-M) · Ω^•_V(log D)(-S)` with the connection
`∇ = d - N⁻¹ du/u ∧`, and let `M'` be a divisor with `-M' ≤ -M` and
`V ∖ (D ∪ Supp M') = V ∖ (D ∪ Supp M)`, as for `M' = M + A` with `A ≥ 0` supported on `D`. The
complex `C'^•` of the same connection on `𝒪_V(-M') · Ω^•_V(log D)(-S)` is a subcomplex of
`C^•`: its sections are forms on the same open `U ∩ W ∩ U'`, and a local representation with
coefficients in `𝒪_V(-M')` is one with coefficients in `𝒪_V(-M)`. This gives, for every model `K`
of `C^•` and every model `K'` of `C'^•`, a morphism of complexes `K' ⟶ K` which is the inclusion
on forms and a monomorphism in every degree. Inclusions compose.

## Main results

* `MMP.LcBpf.cU'_add_of_supp_le`: twisting by a divisor supported on `D` does not move
  `V ∖ (D ∪ Supp M)`.
* `MMP.LcBpf.exists_isTwistInclusion`: the inclusion `K' ⟶ K`.
* `MMP.LcBpf.exists_isTwistInclusion_add`: the inclusion for `M' = M + A`, `A ≥ 0` supported
  on `D`.
* `MMP.LcBpf.IsTwistInclusion.comp`: inclusions compose.

## Implementation notes

The opens `U ∩ W ∩ U'` for `M` and for `M'` are equal but not definitionally so; forms are carried
from one to the other by restriction along the equality.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.FourfoldProofs.FractionalLogComplexProof

variable {V : Scheme.{0}}

/-- **Twisting by a divisor supported on `D` does not move `V ∖ (D ∪ Supp M)`.** -/
theorem cU'_add_of_supp_le (D M A : MMP.Mori.Divisor V) (hA : A.supp ≤ D.supp) :
    cU' D (M + A) = cU' D M := by
  have hle : M.supp ≤ (M + A).supp ⊔ D.supp := by
    have h := MMP.Mori.DivisorWithCoeffs.supp_add_le (M + A) (-A)
    rw [add_neg_cancel_right, MMP.Mori.DivisorWithCoeffs.supp_neg] at h
    exact h.trans (sup_le_sup_left hA _)
  have heq : D.supp ⊔ (M + A).supp = D.supp ⊔ M.supp := by
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · exact (MMP.Mori.DivisorWithCoeffs.supp_add_le _ _).trans
        (sup_le le_sup_right (hA.trans le_sup_left))
    · exact hle.trans (sup_le le_sup_right le_sup_left)
  simp only [cU', heq]

variable (π : V ⟶ Spec (CommRingCat.of ℂ))

/-- The open `U ∩ W ∩ U'` for `M` lies in the one for `M'` when the two `U'` agree. -/
theorem oo_le_of_cU'_eq (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M) (W : V.Opens) :
    OO D M W ≤ OO D M' W := by
  simp only [OO, hM]
  exact le_rfl

/-- Forms on `U ∩ W ∩ U'` for `M'`, read on `U ∩ W ∩ U'` for `M`. -/
noncomputable abbrev twForms (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M) (p : ℤ)
    (W : V.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece p).val.obj
      (op (OO D M' W))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece p).val.obj
      (op (OO D M W)) :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece p).val.map
    (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op ω

/-- `twForms` commutes with restriction to a smaller open `W' ≤ W`. -/
theorem twForms_restrict (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M) (p : ℤ)
    {W W' : V.Opens} (h : W' ≤ W)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece p).val.obj
      (op (OO D M' W))) :
    twForms π D M M' hM p W'
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece p).val.map
          (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M') h))).op ω) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece p).val.map
        (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op
        (twForms π D M M' hM p W ω) := by
  simp only [twForms]
  rw [piece_map_map _ _ _ (homOfLE ((Scheme.Hom.preimage_mono _
      (inf_le_inf_right (cU' D M) h)).trans (oo_le_of_cU'_eq D M M' hM W))).op,
    piece_map_map _ _ _ (homOfLE ((Scheme.Hom.preimage_mono _
      (inf_le_inf_right (cU' D M) h)).trans (oo_le_of_cU'_eq D M M' hM W))).op]

/-- `twForms` is injective. -/
theorem twForms_injective (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M) (p : ℤ)
    (W : V.Opens) : Function.Injective (twForms π D M M' hM p W) := by
  intro ω ω' h
  have key := congrArg (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece
    p).val.map (homOfLE (oo_le_of_cU'_eq D M' M hM.symm W)).op) h
  simp only [twForms] at key
  rwa [piece_map_map _ _ _ (𝟙 _), piece_map_map _ _ _ (𝟙 _), piece_map_id, piece_map_id] at key

/-- In the total algebra, the inclusion of `twForms π D M M' hM p W ω` is the restriction of the
inclusion of `ω`. -/
theorem incl_twForms (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M) (p : ℤ)
    (W : V.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece p).val.obj
      (op (OO D M' W))) :
    (TB ((cU D).ι ≫ π)).incl p (twForms π D M M' hM p W ω) =
      (TB ((cU D).ι ≫ π)).totalRestrict (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op
        ((TB ((cU D).ι ≫ π)).incl p ω) :=
  ((TB ((cU D).ι ≫ π)).totalRestrict_incl _ p ω).symm

/-- Pulling a function on `W ∩ U'` for `M'` back to `U` and restricting to `U ∩ W ∩ U'` for `M`
is pulling back its restriction to `W ∩ U'` for `M`. -/
theorem app_restrict_cU' (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M)
    (W : V.Opens) (g : Γ(V, W ⊓ cU' D M')) :
    (cU D).toScheme.presheaf.map (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op
        ((cU D).ι.app (W ⊓ cU' D M') g) =
      (cU D).ι.app (W ⊓ cU' D M)
        (V.presheaf.map (homOfLE (inf_le_inf_left W hM.ge)).op g) :=
  G1.app_restrict (inf_le_inf_left W hM.ge) g

/-- The restriction of a function `r` on `W`, pulled back to `U ∩ W ∩ U'` for `M'` and read on
`U ∩ W ∩ U'` for `M`, is the pullback of `r` to `U ∩ W ∩ U'` for `M`. -/
theorem res_twForms (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M) (W : V.Opens)
    (r : Γ(V, W)) :
    (cU D).toScheme.presheaf.map (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op
        ((cU D).ι.app (W ⊓ cU' D M') (V.presheaf.map (homOfLE inf_le_left).op r)) =
      (cU D).ι.app (W ⊓ cU' D M) (V.presheaf.map (homOfLE inf_le_left).op r) :=
  (app_restrict_cU' D M M' hM W _).trans (congrArg _ (presheaf_map_map _ _ _ r))

/-- The restriction of a function `u` on `U'` for `M`, pulled back to `U ∩ W ∩ U'` for `M'` and
read on `U ∩ W ∩ U'` for `M`, is the pullback of `u` to `U ∩ W ∩ U'` for `M`. -/
theorem resU_twForms (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M) (W : V.Opens)
    (u : Γ(V, cU' D M)) :
    (cU D).toScheme.presheaf.map (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op
        ((cU D).ι.app (W ⊓ cU' D M') (V.presheaf.map (homOfLE inf_le_right).op
          (V.presheaf.map (homOfLE hM.le).op u))) =
      (cU D).ι.app (W ⊓ cU' D M) (V.presheaf.map (homOfLE inf_le_right).op u) :=
  (app_restrict_cU' D M M' hM W _).trans (congrArg _
    ((congrArg (V.presheaf.map (homOfLE (inf_le_inf_left W hM.ge)).op).hom
      (presheaf_map_map _ _ (homOfLE (inf_le_right.trans hM.le)).op u)).trans
      (presheaf_map_map _ _ _ u)))

/-- `twForms` sends the differential `dF π D _ c` of a function `c` to the differential of the
restriction of `c`. -/
theorem twForms_dF (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M) (W : V.Opens)
    (c : Γ((cU D).toScheme, OO D M' W)) :
    twForms π D M M' hM 1 W (dF π D (OO D M' W) c) =
      dF π D (OO D M W)
        ((cU D).toScheme.presheaf.map (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op c) :=
  dF_restrict π D _ c

/-- `twForms` commutes with the de Rham differential. -/
theorem twForms_deRham (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M) (p : ℕ)
    (W : V.Opens)
    (b : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M' W))) :
    twForms π D M M' hM ((p + 1 : ℕ) : ℤ) W
        (((Scheme.Hom.deRhamComplex ((cU D).ι ≫ π)).d p (p + 1)).val.app (op (OO D M' W)) b) =
      ((Scheme.Hom.deRhamComplex ((cU D).ι ≫ π)).d p (p + 1)).val.app (op (OO D M W))
        (twForms π D M M' hM p W b) :=
  (PresheafOfModules.naturality_apply
    ((Scheme.Hom.deRhamComplex ((cU D).ι ≫ π)).d p (p + 1)).val _ b).symm

/-- Restriction from `U ∩ W ∩ U'` for `M'` to `U ∩ W ∩ U'` for `M` is multiplicative on the total
algebra. -/
theorem totalRestrict_mul_twForms (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M)
    (W : V.Opens) (a b : (TB ((cU D).ι ≫ π)).Total (op (OO D M' W))) :
    (TB ((cU D).ι ≫ π)).totalRestrict (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op (a * b) =
      (TB ((cU D).ι ≫ π)).totalRestrict (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op a *
        (TB ((cU D).ι ≫ π)).totalRestrict (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op b := by
  rw [← (TB ((cU D).ι ≫ π)).totalRestrictRingHom_apply, map_mul]
  rfl

/-- Restriction from `U ∩ W ∩ U'` for `M'` to `U ∩ W ∩ U'` for `M` of a product `c · a` of a
function and a form is the product of the restriction of `c` and `twForms π D M M' hM q W a`. -/
theorem totalRestrict_sm_mul_incl (D M M' : MMP.Mori.Divisor V) (hM : cU' D M' = cU' D M)
    (W : V.Opens) (c : Γ((cU D).toScheme, OO D M' W)) (q : ℤ)
    (a : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece q).val.obj
      (op (OO D M' W))) :
    (TB ((cU D).ι ≫ π)).totalRestrict (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op
        ((TB ((cU D).ι ≫ π)).structureMap (op (OO D M' W)) c * (TB ((cU D).ι ≫ π)).incl q a) =
      (TB ((cU D).ι ≫ π)).structureMap (op (OO D M W))
          ((cU D).toScheme.presheaf.map (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op c) *
        (TB ((cU D).ι ≫ π)).incl q (twForms π D M M' hM q W a) := by
  rw [totalRestrict_mul_twForms π D M M' hM W, incl_twForms π D M M' hM q W]
  exact congrArg (· * _) (totalRestrict_sm _ c)

/-- A morphism of sheaves of modules which is injective on sections is a monomorphism. -/
theorem mono_of_injective_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} {A B : SheafOfModules.{0} R} (f : A ⟶ B)
    (h : ∀ X, Function.Injective (f.val.app X)) : Mono f :=
  (SheafOfModules.toSheaf R).mono_of_mono_map (Sheaf.mono_of_injective _ h)

/-- The components on sections of an isomorphism of sheaves of modules are injective. -/
theorem injective_hom_val_app_of_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} {A B : SheafOfModules.{0} R} (e : A ≅ B) (X : Cᵒᵖ) :
    Function.Injective (e.hom.val.app X) := fun z z' h =>
  ((congrArg (fun f => f.val.app X z) e.hom_inv_id).symm.trans
    (congrArg (e.inv.val.app X) h)).trans (congrArg (fun f => f.val.app X z') e.hom_inv_id)

variable (n : ℕ) [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]

section Clauses

variable {π n} {D : MMP.Mori.Divisor V} {hD : D.IsRelativeSNC n π} {S M : MMP.Mori.Divisor V}
  {N : ℕ} {u : Γ(V, cU' D M)}
  {K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
  {F : ℕ → V.Modules}
  {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
  {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))}

/-- For a model of `C^•`, the map `ι p W` to forms is injective. -/
theorem isCModel_inj (h : IsCModel n π D hD S M N u K F e ι) (p : ℕ) (W : V.Opens) :
    Function.Injective (ι p W) := h.1 p W

/-- For a model of `C^•`, the map `ι p W` to forms is additive. -/
theorem isCModel_add (h : IsCModel n π D hD S M N u K F e ι) (p : ℕ) (W : V.Opens)
    (x y : (F p).val.obj (op W)) : ι p W (x + y) = ι p W x + ι p W y := h.2.1 p W x y

/-- For a model of `C^•`, the map `ι p W` to forms is linear over functions on `W`. -/
theorem isCModel_smul (h : IsCModel n π D hD S M N u K F e ι) (p : ℕ) (W : V.Opens)
    (r : V.ringCatSheaf.obj.obj (op W)) (x : (F p).val.obj (op W)) :
    (TB ((cU D).ι ≫ π)).incl (p : ℤ) (ι p W (r • x)) =
      (TB ((cU D).ι ≫ π)).structureMap (op (OO D M W))
          ((cU D).ι.app (W ⊓ cU' D M) (V.presheaf.map (homOfLE inf_le_left).op r)) *
        (TB ((cU D).ι ≫ π)).incl (p : ℤ) (ι p W x) := h.2.2.1 p W r x

/-- For a model of `C^•`, the maps `ι p W` commute with restriction to `W' ≤ W`. -/
theorem isCModel_restrict (h : IsCModel n π D hD S M N u K F e ι) (p : ℕ) (W W' : V.Opens)
    (hW : W' ≤ W) (x : (F p).val.obj (op W)) :
    ι p W' ((F p).val.map (homOfLE hW).op x) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.map
        (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) hW))).op (ι p W x) :=
  h.2.2.2.1 p W W' hW x

/-- For a model of `C^•`, a form `ω` on `U ∩ W ∩ U'` is in the range of `ι p W` if and only if,
locally on affine opens `W' ≤ W`, it is a finite sum `∑ gᵢ ηᵢ` of logarithmic forms `ηᵢ` with
coefficients `gᵢ` that are sections of `𝒪_V(-M)`. -/
theorem isCModel_range_iff (h : IsCModel n π D hD S M N u K F e ι) (p : ℕ) (W : V.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))) :
    ω ∈ Set.range (ι p W) ↔ ∀ x ∈ W, ∃ (W' : V.affineOpens) (h : (W' : V.Opens) ≤ W),
      x ∈ (W' : V.Opens) ∧ ∃ (m : ℕ) (g : Fin m → Γ(V, (W' : V.Opens) ⊓ cU' D M))
        (η : Fin m → ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece
          (p : ℤ)).val.obj (op ((cU D).ι ⁻¹ᵁ (W' : V.Opens)))),
        (∀ i, ∃ a ∈ (-M).divisorialSubmodule (W' : V.Opens),
          (MMP.Mori.rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a =
            (MMP.Mori.toRationalFunctionsPresheaf V).app (op ((W' : V.Opens) ⊓ cU' D M)) (g i)) ∧
        (∀ i, η i ∈ MMP.Mori.Divisor.relativeLogForms n π D hD S.suppIdeal p (W' : V.Opens)) ∧
        (TB ((cU D).ι ≫ π)).incl (p : ℤ)
            (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.map
              (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op ω) =
          ∑ i, (TB ((cU D).ι ≫ π)).structureMap (op (OO D M W'))
              ((cU D).ι.app ((W' : V.Opens) ⊓ cU' D M) (g i)) *
            (TB ((cU D).ι ≫ π)).incl (p : ℤ)
              (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece
                (p : ℤ)).val.map (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op (η i)) :=
  h.2.2.2.2.1 p W ω

/-- For a model of `C^•`, the differential of `K` is the connection `∇ = d - N⁻¹ du/u ∧` on forms,
after multiplication by `N u`. -/
theorem isCModel_nabla (h : IsCModel n π D hD S M N u K F e ι) (p : ℕ) (W : V.Opens)
    (y : (K.X p).val.obj (op W)) :
    N • ((TB ((cU D).ι ≫ π)).structureMap (op (OO D M W)) (resU W u) *
        (TB ((cU D).ι ≫ π)).incl ((p + 1 : ℕ) : ℤ) (ι (p + 1) W ((e (p + 1)).hom.val.app (op W)
          ((K.d p (p + 1)).val.app (op W) y)))) =
      N • ((TB ((cU D).ι ≫ π)).structureMap (op (OO D M W)) (resU W u) *
        (TB ((cU D).ι ≫ π)).incl ((p + 1 : ℕ) : ℤ)
          (((Scheme.Hom.deRhamComplex ((cU D).ι ≫ π)).d p (p + 1)).val.app (op (OO D M W))
            (ι p W ((e p).hom.val.app (op W) y)))) -
      (TB ((cU D).ι ≫ π)).incl 1 (dF π D (OO D M W) (resU W u)) *
        (TB ((cU D).ι ≫ π)).incl (p : ℤ) (ι p W ((e p).hom.val.app (op W) y)) :=
  h.2.2.2.2.2 p W y

end Clauses

omit [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V] in
/-- Cancelling `N u`: multiplication by `N u` is injective on the forms on `U ∩ W ∩ U'`. -/
theorem eq_of_nsmul_structureMap_mul_eq (D M : MMP.Mori.Divisor V) (N : ℕ)
    (u : Γ(V, cU' D M)) (hNu : IsUnit ((N : Γ(V, cU' D M)) * u)) (W : V.Opens)
    (z z' : (TB ((cU D).ι ≫ π)).Total (op (OO D M W)))
    (h : N • ((TB ((cU D).ι ≫ π)).structureMap (op (OO D M W)) (resU W u) * z) =
      N • ((TB ((cU D).ι ≫ π)).structureMap (op (OO D M W)) (resU W u) * z')) : z = z' := by
  let φr : Γ(V, cU' D M) →+* Γ((cU D).toScheme, OO D M W) :=
    ((cU D).ι.app (W ⊓ cU' D M)).hom.comp (V.presheaf.map (homOfLE inf_le_right).op).hom
  have h1 : φr ↑hNu.unit⁻¹ * (N : Γ((cU D).toScheme, OO D M W)) * φr u = 1 := by
    have := congrArg φr hNu.val_inv_mul
    rwa [map_mul, map_mul, map_natCast, map_one, ← mul_assoc] at this
  have key : ∀ y, sm ((cU D).ι ≫ π) (OO D M W) (φr ↑hNu.unit⁻¹) *
      (N • (sm ((cU D).ι ≫ π) (OO D M W) (resU W u) * y)) = y := by
    intro y
    change sm ((cU D).ι ≫ π) (OO D M W) (φr ↑hNu.unit⁻¹) *
      (N • (sm ((cU D).ι ≫ π) (OO D M W) (φr u) * y)) = y
    rw [nsmul_eq_mul, ← map_natCast (sm ((cU D).ι ≫ π) (OO D M W)) N,
      ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, h1, map_one, one_mul]
  change N • (sm ((cU D).ι ≫ π) (OO D M W) (resU W u) * z) =
    N • (sm ((cU D).ι ≫ π) (OO D M W) (resU W u) * z') at h
  simpa only [key] using
    congrArg (fun y => sm ((cU D).ι ≫ π) (OO D M W) (φr ↑hNu.unit⁻¹) * y) h

section Twist

variable (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M M' : MMP.Mori.Divisor V)
  (hM : cU' D M' = cU' D M) (N : ℕ) (u : Γ(V, cU' D M))
  {K K' : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
  {F F' : ℕ → V.Modules}
  {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
  {e' : ∀ p, K'.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F' p)}
  {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))}
  {ι' : ∀ (p : ℕ) (W : V.Opens), (F' p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M' W))}

/-- A form of `C'^•` is a form of `C^•`. -/
theorem twForms_mem_range (hdiv : -M' ≤ -M) (hK : IsCModel n π D hD S M N u K F e ι)
    (u' : Γ(V, cU' D M')) (hK' : IsCModel n π D hD S M' N u' K' F' e' ι') (p : ℕ) (W : V.Opens)
    (x' : (F' p).val.obj (op W)) : ∃ x, ι p W x = twForms π D M M' hM p W (ι' p W x') := by
  refine (isCModel_range_iff hK p W _).2 fun y hy => ?_
  obtain ⟨W', h, hyW', m, g, η, hg, hη, he⟩ :=
    (isCModel_range_iff hK' p W (ι' p W x')).1 ⟨x', rfl⟩ y hy
  refine ⟨W', h, hyW', m, fun i => V.presheaf.map
    (homOfLE (inf_le_inf_left (W' : V.Opens) hM.ge)).op (g i), η, fun i => ?_, hη, ?_⟩
  · obtain ⟨a, ha, hae⟩ := hg i
    refine ⟨a, MMP.Mori.Divisor.divisorialSubmodule_mono hdiv _ ha, ?_⟩
    calc (MMP.Mori.rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a =
          (MMP.Mori.rationalFunctionsPresheaf V).map
            (homOfLE (inf_le_inf_left (W' : V.Opens) hM.ge)).op
            ((MMP.Mori.rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a) := rfl
      _ = (MMP.Mori.rationalFunctionsPresheaf V).map
            (homOfLE (inf_le_inf_left (W' : V.Opens) hM.ge)).op
            ((MMP.Mori.toRationalFunctionsPresheaf V).app (op ((W' : V.Opens) ⊓ cU' D M'))
              (g i)) := by rw [hae]
      _ = _ := (congrArg (fun φ => φ.hom (g i))
          ((MMP.Mori.toRationalFunctionsPresheaf V).naturality
            (homOfLE (inf_le_inf_left (W' : V.Opens) hM.ge)).op)).symm
  · refine (congrArg ((TB ((cU D).ι ≫ π)).incl (p : ℤ))
      (twForms_restrict π D M M' hM p h (ι' p W x')).symm).trans
      ((incl_twForms π D M M' hM p W' _).trans ((congrArg _ he).trans
        ((map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_))))
    exact (totalRestrict_sm_mul_incl π D M M' hM W' _ _ _).trans
      (congrArg₂ (· * ·) (congrArg _ (app_restrict_cU' D M M' hM W' (g i)))
        (congrArg _ (piece_map_map _ _ _ _ _)))

/-- The connection is compatible with the inclusion: if `y` and `z` are the images of `x` and of
`∇ x`, then `z = ∇ y`. -/
theorem eq_d_of_twForms (hK : IsCModel n π D hD S M N u K F e ι)
    (hK' : IsCModel n π D hD S M' N (V.presheaf.map (homOfLE hM.le).op u) K' F' e' ι')
    (hNu : IsUnit ((N : Γ(V, cU' D M)) * u)) (p : ℕ) (W : V.Opens)
    (x : (K'.X p).val.obj (op W)) (y : (K.X p).val.obj (op W))
    (z : (K.X (p + 1)).val.obj (op W))
    (hy : ι p W ((e p).hom.val.app (op W) y) =
      twForms π D M M' hM p W (ι' p W ((e' p).hom.val.app (op W) x)))
    (hz : ι (p + 1) W ((e (p + 1)).hom.val.app (op W) z) =
      twForms π D M M' hM (p + 1 : ℕ) W (ι' (p + 1) W ((e' (p + 1)).hom.val.app (op W)
        ((K'.d p (p + 1)).val.app (op W) x)))) :
    ι (p + 1) W ((e (p + 1)).hom.val.app (op W) z) =
      ι (p + 1) W ((e (p + 1)).hom.val.app (op W) ((K.d p (p + 1)).val.app (op W) y)) := by
  refine (TB ((cU D).ι ≫ π)).incl_inj_of_proj
    (eq_of_nsmul_structureMap_mul_eq π D M N u hNu W _ _ ?_)
  refine Eq.trans ?_ (isCModel_nabla hK p W y).symm
  rw [hz, hy]
  have E0 := isCModel_nabla hK' p W x
  let T := (TB ((cU D).ι ≫ π)).totalRestrict (homOfLE (oo_le_of_cU'_eq D M M' hM W)).op
  exact (congrArg (N • ·) ((totalRestrict_sm_mul_incl π D M M' hM W _ _ _).trans
      (congrArg (· * _) (congrArg _ (resU_twForms D M M' hM W u))))).symm.trans
    ((map_nsmul T N _).symm.trans ((congrArg T E0).trans ((map_sub T _ _).trans
      (congrArg₂ (fun X Y => X - Y) ((map_nsmul T N _).trans (congrArg (N • ·)
        ((totalRestrict_sm_mul_incl π D M M' hM W _ _ _).trans
          (congrArg₂ (· * ·) (congrArg _ (resU_twForms D M M' hM W u))
            (congrArg _ (twForms_deRham π D M M' hM p W _))))))
        ((totalRestrict_mul_twForms π D M M' hM W _ _).trans
          (congrArg₂ (· * ·) ((incl_twForms π D M M' hM 1 W _).symm.trans
            (congrArg _ ((twForms_dF π D M M' hM W _).trans
              (congrArg _ (resU_twForms D M M' hM W u)))))
            (incl_twForms π D M M' hM (p : ℤ) W _).symm))))))

/-- **The inclusion of a twist.** Let `M'` be a divisor with `-M' ≤ -M` and
`V ∖ (D ∪ Supp M') = V ∖ (D ∪ Supp M)`, and `u` a function on this open with `N u` a unit. For
a model `K` of `C^•` for `(M, u)` and a model `K'` of `C^•` for `(M', u)`, there is a morphism of
complexes `φ : K' ⟶ K` which is the inclusion on forms (`MMP.LcBpf.IsTwistInclusion`) and a
monomorphism in every degree. -/
theorem exists_isTwistInclusion (hdiv : -M' ≤ -M) (hNu : IsUnit ((N : Γ(V, cU' D M)) * u))
    (hK : IsCModel n π D hD S M N u K F e ι)
    (hK' : IsCModel n π D hD S M' N (V.presheaf.map (homOfLE hM.le).op u) K' F' e' ι') :
    ∃ φ : K' ⟶ K, IsTwistInclusion π D M M' hM e e' ι ι' φ ∧ ∀ p, Mono (φ.f p) := by
  classical
  choose ψf hψf using twForms_mem_range π n D hD S M M' hM N u hdiv hK _ hK'
  have hι1 := isCModel_inj hK
  have hadd : ∀ p W x y, ψf p W (x + y) = ψf p W x + ψf p W y := fun p W x y =>
    hι1 p W ((hψf p W (x + y)).trans ((congrArg (twForms π D M M' hM p W)
      (isCModel_add hK' p W x y)).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) (hψf p W x).symm
        (hψf p W y).symm).trans (isCModel_add hK p W _ _).symm))))
  have hnat : ∀ (p : ℕ) (W W' : V.Opens) (h : W' ≤ W) x,
      ψf p W' ((F' p).val.map (homOfLE h).op x) = (F p).val.map (homOfLE h).op (ψf p W x) :=
    fun p W W' h x => hι1 p W' ((hψf p W' _).trans
      ((congrArg (twForms π D M M' hM p W')
        (isCModel_restrict hK' p W W' h x)).trans
        ((twForms_restrict π D M M' hM p h _).trans
          ((congrArg _ (hψf p W x).symm).trans
            (isCModel_restrict hK p W W' h _).symm))))
  have hsmul : ∀ (p : ℕ) (W : V.Opens) (r : V.ringCatSheaf.obj.obj (op W)) x,
      ψf p W (r • x) = r • ψf p W x := fun p W r x =>
    hι1 p W ((TB ((cU D).ι ≫ π)).incl_inj_of_proj
      ((congrArg _ (hψf p W (r • x))).trans ((incl_twForms π D M M' hM p W _).trans
        ((congrArg _ (isCModel_smul hK' p W r x)).trans
          ((totalRestrict_sm_mul_incl π D M M' hM W _ _ _).trans
          ((congrArg₂ (· * ·) (congrArg _ (res_twForms D M M' hM W r))
            (congrArg _ (hψf p W x).symm)).trans
              (isCModel_smul hK p W r _).symm))))))
  let ψ : ∀ p, F' p ⟶ F p := fun p => ⟨PresheafOfModules.homMk
      { app := fun W => AddCommGrpCat.ofHom (AddMonoidHom.mk' (ψf p W.unop) (hadd p W.unop))
        naturality := fun {W W'} g => by
          ext x
          rw [show g = (homOfLE (leOfHom g.unop)).op from Subsingleton.elim _ _]
          exact hnat p W.unop W'.unop (leOfHom g.unop) x }
      (fun W r x => hsmul p W.unop r x)⟩
  let φf : ∀ p, K'.X p ⟶ K.X p := fun p =>
    (e' p).hom ≫ (SheafOfModules.restrictScalars _).map (ψ p) ≫ (e p).inv
  have hee : ∀ (p : ℕ) (W : V.Opens) z,
      (e p).hom.val.app (op W) ((e p).inv.val.app (op W) z) = z := fun p W z =>
    congrArg (fun f => f.val.app (op W) z) (e p).inv_hom_id
  have hφι : ∀ (p : ℕ) (W : V.Opens) x,
      ι p W ((e p).hom.val.app (op W) ((φf p).val.app (op W) x)) =
        twForms π D M M' hM p W (ι' p W ((e' p).hom.val.app (op W) x)) := fun p W x =>
    (congrArg (ι p W) (hee p W _)).trans (hψf p W _)
  refine ⟨{ f := φf, comm' := ?_ }, fun p W x => hφι p W x, fun p => ?_⟩
  · rintro p _ rfl
    ext W x
    exact (injective_hom_val_app_of_iso (e (p + 1)) W (hι1 (p + 1) W.unop
      (eq_d_of_twForms π n D hD S M M' hM N u hK hK' hNu p W.unop x _ _ (hφι p W.unop x)
        (hφι (p + 1) W.unop _)))).symm
  · refine mono_of_injective_app _ fun W => ?_
    induction W with
    | op W =>
      intro x y hxy
      have := congrArg (fun z => ι p W ((e p).hom.val.app (op W) z)) hxy
      simp only [hφι] at this
      exact injective_hom_val_app_of_iso (e' p) _ (isCModel_inj hK' p W
        (twForms_injective π D M M' hM p W this))

end Twist

/-- **The inclusion of a twist by a divisor `A ≥ 0` supported on `D`.** -/
theorem exists_isTwistInclusion_add (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π)
    (S M A : MMP.Mori.Divisor V) (hA : 0 ≤ A) (hAD : A.supp ≤ D.supp) (N : ℕ)
    (u : Γ(V, cU' D M)) (hNu : IsUnit ((N : Γ(V, cU' D M)) * u))
    {K K' : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
    {F F' : ℕ → V.Modules}
    {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
    {e' : ∀ p, K'.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F' p)}
    {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W))}
    {ι' : ∀ (p : ℕ) (W : V.Opens), (F' p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D (M + A) W))}
    (hK : IsCModel n π D hD S M N u K F e ι)
    (hK' : IsCModel n π D hD S (M + A) N
      (V.presheaf.map (homOfLE (cU'_add_of_supp_le D M A hAD).le).op u) K' F' e' ι') :
    ∃ φ : K' ⟶ K, IsTwistInclusion π D M (M + A) (cU'_add_of_supp_le D M A hAD) e e' ι ι' φ ∧
      ∀ p, Mono (φ.f p) :=
  exists_isTwistInclusion π n D hD S M (M + A) _ N u (by
    rw [neg_add]
    exact add_le_of_nonpos_right (neg_nonpos.2 hA)) hNu hK hK'

variable {π} in
omit [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V] in
/-- **Inclusions of twists compose.** -/
theorem IsTwistInclusion.comp {D M M' M'' : MMP.Mori.Divisor V} {hM : cU' D M' = cU' D M}
    {hM' : cU' D M'' = cU' D M'}
    {K K' K'' : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
    {F F' F'' : ℕ → V.Modules}
    {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
    {e' : ∀ p, K'.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F' p)}
    {e'' : ∀ p, K''.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F'' p)}
    {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W))}
    {ι' : ∀ (p : ℕ) (W : V.Opens), (F' p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M' W))}
    {ι'' : ∀ (p : ℕ) (W : V.Opens), (F'' p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M'' W))}
    {φ : K' ⟶ K} {φ' : K'' ⟶ K'}
    (h : IsTwistInclusion π D M M' hM e e' ι ι' φ)
    (h' : IsTwistInclusion π D M' M'' hM' e' e'' ι' ι'' φ') :
    IsTwistInclusion π D M M'' (hM'.trans hM) e e'' ι ι'' (φ' ≫ φ) := by
  intro p W x
  refine (h p W ((φ'.f p).val.app (op W) x)).trans ?_
  rw [h' p W x]
  exact piece_map_map _ _ _ _ _

end MMP.LcBpf
