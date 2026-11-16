module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.WeightZeroChart
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamRestriction
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters

/-!
# Relative differential forms of a `k`-scheme on an affine open

Let `k` be a field and `f : V ⟶ Spec k` a scheme over `k`. For an affine open `W ⊆ V` write
`L = Γ(V, W)`, a `k`-algebra through `f` (`MMP.Mori.sectionAlgebra`). The sections over `W` of
the sheaf `Ω^q_{V/k}` of relative differential `q`-forms are the algebraic forms
`⋀^q_L Ω_{L/k}`:

`Γ(Ω^q_{V/k}, W) ≃ ⋀^q_L Ω[L⁄k]`,

and this identification is compatible with restriction to a smaller affine open, with the de
Rham differential and with the wedge product.

## Main definitions

* `MMP.DeRham.kaehlerBaseEquiv`: for a ring map `φ : R ⟶ B` and a ring `k ≃ R` mapping to `B`
  compatibly, `Ω[B⁄R] ≃ Ω[B⁄k]`.
* `MMP.DeRham.kaehlerSpecEquiv`: its instance `Ω[Γ(V, W)⁄Γ(Spec k, ⊤)] ≃ Ω[Γ(V, W)⁄k]`.
* `MMP.DeRham.formsAlgEquiv`: **the comparison** `Γ(Ω^q_{V/k}, W) ≃ ⋀^q Ω[Γ(V, W)⁄k]`.

## Main results

* `MMP.DeRham.formsAlgEquiv_restrict`: the comparison commutes with restriction, read on the
  algebraic side through `KaehlerDifferential.mapExteriorPower`.
* `MMP.DeRham.formsAlgEquiv_d`: the comparison carries the de Rham differential of the complex
  `f.deRhamComplex` to `KaehlerDifferential.deRhamDifferential`.
* `MMP.DeRham.formsAlgEquiv_mul`: the comparison carries the product of the exterior algebra of
  `Ω_{V/k}` to `exteriorPower.wedgeMul`.

## Implementation notes

The comparison of Stacks, `Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso`, is
taken over the affine open `⊤` of `Spec k`, so its Kähler differentials are over `Γ(Spec k, ⊤)`;
these are transported to Kähler differentials over `k` along `Scheme.ΓSpecIso`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry KaehlerDifferential
open Stacks.AlgebraicGeometry.AffineOpenDeRham

universe u

namespace MMP.DeRham

/-! ### Kähler differentials over isomorphic bases -/

section Generic

variable {R B : CommRingCat.{u}} (φ : R ⟶ B) {k : Type u} [CommRing k] [Algebra k B]
  (σ : R ≃+* k) (hσ : (algebraMap k B).comp σ.toRingHom = φ.hom)

/-- The Kähler differentials of a ring map `φ : R ⟶ B` and of `B` over a ring `k ≃ R` whose
structure map is compatible with `φ` agree: `Ω[B⁄R] ≃ Ω[B⁄k]`, sending `d b` to `d b`. -/
def kaehlerBaseEquiv : ↥(CommRingCat.KaehlerDifferential φ) ≃ₗ[B] Ω[B⁄k] :=
  letI : Algebra R B := φ.hom.toAlgebra
  letI : Algebra R k := σ.toRingHom.toAlgebra
  letI : Algebra k R := σ.symm.toRingHom.toAlgebra
  haveI : IsScalarTower R k B := IsScalarTower.of_algebraMap_eq' hσ.symm
  haveI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' <| by
    ext c
    simp [← hσ, RingHom.algebraMap_toAlgebra]
  show Ω[B⁄R] ≃ₗ[B] Ω[B⁄k] from
  LinearEquiv.ofLinearMap (map R k B B) (map k R B B)
    (Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b ↦ by simp))
    (Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b ↦ by simp))

/-- `kaehlerBaseEquiv` sends `d b` to `d b`. -/
@[simp]
theorem kaehlerBaseEquiv_d (b : B) :
    kaehlerBaseEquiv φ σ hσ (CommRingCat.KaehlerDifferential.d b) = D k B b := by
  let : Algebra R B := φ.hom.toAlgebra
  let : Algebra R k := σ.toRingHom.toAlgebra
  have : IsScalarTower R k B := IsScalarTower.of_algebraMap_eq' hσ.symm
  exact map_D R k B B b

/-- The identification `⋀^q Ω[B⁄R] ≃ ⋀^q Ω[B⁄k]` carries the de Rham differential of
`φ : R ⟶ B` to the de Rham differential of `B` over `k`. -/
theorem exteriorPower_map_kaehlerBaseEquiv_ringDeRhamComplex_d (q : ℕ)
    (x : ⋀[B]^q ↥(CommRingCat.KaehlerDifferential φ)) :
    exteriorPower.map (q + 1) (kaehlerBaseEquiv φ σ hσ).toLinearMap
        (((Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex φ).d q
          (q + 1)).hom x) =
      deRhamDifferential (A := k) q
        (exteriorPower.map q (kaehlerBaseEquiv φ σ hσ).toLinearMap x) := by
  let : Algebra R B := φ.hom.toAlgebra
  have hd : ∀ y : ⋀[B]^q (Ω[B⁄R]),
      ((Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex φ).d q (q + 1)).hom y =
        deRhamDifferential (A := R) q y := by
    intro y
    change ((KaehlerDifferential.deRhamComplex R B).d q (q + 1)).hom y = _
    rw [KaehlerDifferential.deRhamComplex_d]
    rfl
  let e : Ω[B⁄R] ≃ₗ[B] Ω[B⁄k] := kaehlerBaseEquiv φ σ hσ
  have he : ∀ b : B, e (D R B b) = D k B b := kaehlerBaseEquiv_d φ σ hσ
  let F : ⋀[B]^q (Ω[B⁄R]) →+ ⋀[B]^(q + 1) (Ω[B⁄k]) :=
    (exteriorPower.map (q + 1) e.toLinearMap).toAddMonoidHom.comp
      (deRhamDifferential (A := R) (B := B) q).toAddMonoidHom
  let G : ⋀[B]^q (Ω[B⁄R]) →+ ⋀[B]^(q + 1) (Ω[B⁄k]) :=
    (deRhamDifferential (A := k) (B := B) q).toAddMonoidHom.comp
      (exteriorPower.map q e.toLinearMap).toAddMonoidHom
  have key : F.toIntLinearMap = G.toIntLinearMap := by
    refine LinearMap.ext_on (R := ℤ)
      (Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ) (D R B)
        (span_range_derivation R B) q) ?_
    rintro _ ⟨b, rfl⟩
    simp only [F, G, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp,
      LinearMap.toAddMonoidHom_coe, Function.comp_apply]
    rw [deRhamDifferential_smul_ιMulti_D, map_smul, exteriorPower.map_apply_ιMulti,
      exteriorPower.map_apply_ιMulti]
    simp only [Function.comp_def, LinearEquiv.coe_coe, he]
    exact (deRhamDifferential_smul_ιMulti_D (A := k) q b).symm
  rw [hd x]
  exact LinearMap.congr_fun key x

end Generic

/-! ### The comparison on an affine open of a `k`-scheme -/

variable {k : Type u} [Field k] {V : Scheme.{u}} (f : V ⟶ Spec (.of k))

/-- The structure maps `Γ(Spec k, ⊤) → Γ(V, W)` and `k → Γ(V, W)` are compatible along
`Scheme.ΓSpecIso`. -/
theorem sectionAlgebra_algebraMap_comp_ΓSpecIso (W : V.Opens) :
    letI := MMP.Mori.sectionAlgebra f W
    (algebraMap k Γ(V, W)).comp
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toRingHom =
      (f.appLE ⊤ W (by simp)).hom := by
  let := MMP.Mori.sectionAlgebra f W
  ext c
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ W _).hom
      ((Scheme.ΓSpecIso (.of k)).hom c) = (f.appLE ⊤ W _).hom c
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id_assoc]

/-- The Kähler differentials of `Γ(V, W)` over `Γ(Spec k, ⊤)` are those over `k`. -/
abbrev kaehlerSpecEquiv (W : V.Opens) :
    letI := MMP.Mori.sectionAlgebra f W
    ↥(CommRingCat.KaehlerDifferential (f.appLE ⊤ W (by simp))) ≃ₗ[Γ(V, W)] Ω[Γ(V, W)⁄k] :=
  letI := MMP.Mori.sectionAlgebra f W
  kaehlerBaseEquiv _ (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
    (sectionAlgebra_algebraMap_comp_ΓSpecIso f W)

/-- **The sections of the relative differential forms of a `k`-scheme over an affine open** `W`
are the algebraic forms of `Γ(V, W)` over `k`: `Γ(Ω^q_{V/k}, W) ≃ ⋀^q Ω[Γ(V, W)⁄k]`. -/
def formsAlgEquiv (q : ℕ) (W : V.affineOpens) :
    letI := MMP.Mori.sectionAlgebra f W
    Γ(f.relativeDifferentialForms (q : ℤ), W) ≃ₗ[Γ(V, W)] ⋀[Γ(V, W)]^q (Ω[Γ(V, W)⁄k]) :=
  letI := MMP.Mori.sectionAlgebra f W
  (formsSectionsIso f W.2 (isAffineOpen_top _) (by simp) q).toLinearEquiv.trans
    (Stacks.AffineExteriorPower.exteriorPowerCongr (kaehlerSpecEquiv f W) q)

/-- `formsAlgEquiv` is the comparison `formsSectionsIso` followed by the change of base
`kaehlerSpecEquiv`. -/
theorem formsAlgEquiv_apply (q : ℕ) (W : V.affineOpens)
    (ω : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    letI := MMP.Mori.sectionAlgebra f W
    formsAlgEquiv f q W ω = exteriorPower.map q (kaehlerSpecEquiv f W).toLinearMap
      ((formsSectionsIso f W.2 (isAffineOpen_top _) (by simp) q).hom ω) := by
  let := MMP.Mori.sectionAlgebra f W
  unfold formsAlgEquiv
  rw [LinearEquiv.trans_apply]
  erw [Iso.toLinearEquiv_apply]
  rfl

/-- **The comparison of forms commutes with restriction**: restricting a relative form from `W`
to a smaller affine open `W'` is the map of algebraic forms induced by the restriction of
functions `Γ(V, W) → Γ(V, W')`. -/
theorem formsAlgEquiv_restrict (q : ℕ) {W W' : V.affineOpens} (h : (W' : V.Opens) ≤ W)
    (ω : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    letI := MMP.Mori.sectionAlgebra f W
    letI := MMP.Mori.sectionAlgebra f W'
    letI : Algebra Γ(V, W) Γ(V, W') := (V.presheaf.map (homOfLE h).op).hom.toAlgebra
    haveI := MMP.Flips.ResolutionInputs.isScalarTower_section_res f h
    formsAlgEquiv f q W' ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op ω) =
      mapExteriorPower k Γ(V, W) Γ(V, W') q (formsAlgEquiv f q W ω) := by
  let := MMP.Mori.sectionAlgebra f W
  let := MMP.Mori.sectionAlgebra f W'
  let : Algebra Γ(V, W) Γ(V, W') := (V.presheaf.map (homOfLE h).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f h
  refine (formsAlgEquiv_apply f q W' _).trans ?_
  refine (congrArg (exteriorPower.map q (kaehlerSpecEquiv f W').toLinearMap)
    (formsSectionsIso_hom_restrict W.2 W'.2 (isAffineOpen_top _) (by simp) (by simp) h q
      ω)).trans ?_
  refine Eq.trans ?_ (congrArg _ (formsAlgEquiv_apply f q W ω).symm)
  refine eq_of_smul_ιMulti_d (f.appLE ⊤ W (by simp)) q
    (fun x ↦ exteriorPower.map q (kaehlerSpecEquiv f W').toLinearMap
      (formsRestriction f (by simp) (by simp) h q x))
    (fun x ↦ mapExteriorPower k Γ(V, W) Γ(V, W') q
      (exteriorPower.map q (kaehlerSpecEquiv f W).toLinearMap x)) ?_ ?_ ?_ ?_ _
  · simp only [formsRestriction, formsMap_zero, map_zero]
  · intro y z hy hz
    simp only [formsRestriction, formsMap_add, map_add] at hy hz ⊢
    rw [hy, hz]
  · intro b y hy
    have e₁ := formsMap_smul (f.appLE ⊤ W (by simp)) (f.appLE ⊤ W' (by simp))
      (V.presheaf.map (homOfLE h).op)
      (Scheme.Hom.appLE_map f (U := ⊤) (V := W) (V' := W') (by simp) (homOfLE h).op) q b y
    refine (congrArg (exteriorPower.map q (kaehlerSpecEquiv f W').toLinearMap) e₁).trans ?_
    refine (map_smul _ _ _).trans ?_
    refine (congrArg _ hy).trans ?_
    refine Eq.trans ?_ (congrArg (mapExteriorPower k Γ(V, W) Γ(V, W') q) (map_smul _ b _)).symm
    refine Eq.trans ?_ (map_smul _ b _).symm
    exact algebraMap_smul Γ(V, W') b _
  · intro c
    simp only [formsRestriction, formsMap_ιMulti_d, exteriorPower.map_apply_ιMulti,
      mapExteriorPower_ιMulti, Function.comp_def, LinearEquiv.coe_coe, kaehlerBaseEquiv_d,
      map_D]
    rfl

/-- **The comparison of forms commutes with the de Rham differential**: the differential of the
relative de Rham complex `f.deRhamComplex`, read on sections over an affine open `W`, is the de
Rham differential of `Γ(V, W)` over `k`. -/
theorem formsAlgEquiv_d (q : ℕ) (W : V.affineOpens)
    (ω : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    letI := MMP.Mori.sectionAlgebra f W
    formsAlgEquiv f (q + 1) W (((f.deRhamComplex).d q (q + 1)).val.app (op W) ω) =
      deRhamDifferential (A := k) q (formsAlgEquiv f q W ω) := by
  let := MMP.Mori.sectionAlgebra f W
  refine (formsAlgEquiv_apply f (q + 1) W _).trans ?_
  refine (congrArg (exteriorPower.map (q + 1) (kaehlerSpecEquiv f W).toLinearMap)
    (formsSectionsIso_hom_deRhamComplex_d f W.2 (isAffineOpen_top _) (by simp) q ω)).trans ?_
  refine (exteriorPower_map_kaehlerBaseEquiv_ringDeRhamComplex_d _ _ _ q _).trans ?_
  exact congrArg _ (formsAlgEquiv_apply f q W ω).symm

/-- **The comparison of forms is multiplicative**: it carries the product of the exterior algebra
of `Ω_{V/k}` over `W` to the wedge product of algebraic forms. -/
theorem formsAlgEquiv_mul (p q : ℕ) (W : V.affineOpens)
    (α : Γ(f.relativeDifferentialForms (p : ℤ), W))
    (β : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    letI := MMP.Mori.sectionAlgebra f W
    formsAlgEquiv f (p + q) W
        ((eqToHom (congrArg (Stacks.AffineExteriorPower.pieceModules
          (Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f)))
          (Nat.cast_add p q).symm)).val.app (op (W : V.Opens))
          (((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f)).mul
            (p : ℤ) q).app (op (W : V.Opens)) α β)) =
      exteriorPower.wedgeMul p q (formsAlgEquiv f p W α) (formsAlgEquiv f q W β) := by
  let := MMP.Mori.sectionAlgebra f W
  refine (formsAlgEquiv_apply f (p + q) W _).trans ?_
  refine (congrArg (exteriorPower.map (p + q) (kaehlerSpecEquiv f W).toLinearMap)
    (formsSectionsIso_hom_mul f W.2 (isAffineOpen_top _) (by simp) p q α β)).trans ?_
  refine (exteriorPower.wedgeMul_map p q _ _ _).trans ?_
  exact congrArg₂ (fun a b ↦ exteriorPower.wedgeMul p q a b) (formsAlgEquiv_apply f p W α).symm
    (formsAlgEquiv_apply f q W β).symm

end MMP.DeRham

end
