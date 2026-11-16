module

public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero

/-!
# Étale coordinates

Sections `x_1, …, x_n` of `𝒪_X` over an affine open `U` of a scheme over a field `k` are étale
coordinates when the morphism `U → 𝔸ⁿ_k` they define is étale. Then `𝒪_X(U)` is an étale
`k[X_1, …, X_n]`-algebra, so `dx_1, …, dx_n` is a basis of `Ω_{𝒪_X(U)/k}` (and of `Ω_{𝒪_X(W)/k}`
for every affine `W ⊆ U`), and every `x_i` is a nonzerodivisor of `𝒪_X(U)`, being the image of
the variable `X_i` under a flat ring homomorphism.

## Main results

* `MMP.Resolution.isLocalCoordinatesOn_of_isLocalCoordinates`: étale coordinates are local
  coordinates.
* `MMP.Resolution.mem_nonZeroDivisors_of_isLocalCoordinates`: an étale coordinate is a
  nonzerodivisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP.Resolution

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Étale coordinates `x_1, …, x_n` on an affine open `U` (an étale morphism `U → 𝔸ⁿ_k`) make
`Γ(X, U)` an étale `k[X_1, …, X_n]`-algebra with `X_i ↦ x_i`. -/
theorem exists_etale_mvPolynomial (sX : X ⟶ Spec (.of k)) {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} {x : Fin n → Γ(X, U)} (hx : IsLocalCoordinates sX U x) :
    letI := MMP.Mori.sectionAlgebra sX U
    ∃ φ : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, U), φ.Etale ∧
      (∀ i, φ (MvPolynomial.X i) = x i.down) ∧
      ∀ a, φ (MvPolynomial.C a) = algebraMap k Γ(X, U) a := by
  have : IsAffine U.toScheme := hU
  set g := AffineSpace.homOfVector (n := ULift.{u} (Fin n)) (U.ι ≫ sX)
    fun i => U.topIso.inv.hom (x i.down) with hg
  have hgE : RingHom.Etale g.appTop.hom := HasRingHomProperty.appTop @Etale g hx
  let E : Γ(AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)), ⊤) ≃+*
      MvPolynomial (ULift.{u} (Fin n)) k :=
    ((Scheme.Γ.mapIso (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)).op).symm ≪≫
      Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
  let EU := U.topIso.commRingCatIsoToRingEquiv
  let φ : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, U) :=
    EU.toRingHom.comp (g.appTop.hom.comp E.symm.toRingHom)
  have hEX : ∀ i, E.symm (MvPolynomial.X i) = AffineSpace.coord (Spec (.of k)) i := by
    refine fun i => E.injective ?_
    rw [RingEquiv.apply_symm_apply]
    change _ = (Scheme.ΓSpecIso _).hom.hom
      ((AffineSpace.SpecIso _ (.of k)).inv.appTop.hom (AffineSpace.coord (Spec (.of k)) i))
    rw [AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply]
  have hEC : ∀ a, E.symm (MvPolynomial.C a) =
      (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)).appTop.hom
        ((Scheme.ΓSpecIso (.of k)).inv.hom a) := fun a => by
    change (AffineSpace.SpecIso _ (.of k)).hom.appTop.hom
      ((Scheme.ΓSpecIso (.of (MvPolynomial _ k))).inv.hom (MvPolynomial.C a)) = _
    have hover : (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)).hom ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial _ k)) =
        AffineSpace _ (Spec (.of k)) ↘ Spec (.of k) :=
      (Iso.eq_inv_comp _).mp (AffineSpace.SpecIso_inv_over (n := ULift.{u} (Fin n)) (.of k)).symm
    have key : (Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} (Fin n)) k))).inv.hom
        (MvPolynomial.C a) =
        (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial _ k))).appTop.hom
          ((Scheme.ΓSpecIso (.of k)).inv.hom a) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    rw [key, ← hover, Scheme.Hom.comp_appTop]
    rfl
  let := MMP.Mori.sectionAlgebra sX U
  refine ⟨φ, RingHom.Etale.respectsIso.1 _ _ (RingHom.Etale.respectsIso.2 _ _ hgE),
    fun i => ?_, fun a => ?_⟩
  · change U.topIso.hom.hom (g.appTop.hom (E.symm (MvPolynomial.X i))) = _
    rw [hEX, hg, AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply,
      Iso.inv_hom_id, CommRingCat.id_apply]
  · change U.topIso.hom.hom (g.appTop.hom (E.symm (MvPolynomial.C a))) = _
    rw [hEC]
    have e1 : (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)).appTop ≫
        g.appTop ≫ U.topIso.hom = sX.appLE ⊤ U le_top := by
      rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hg, AffineSpace.homOfVector_over,
        Scheme.Hom.comp_appTop, Category.assoc, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
      erw [← Functor.map_comp]
      rfl
    exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)) e1

/-- Étale coordinates on an affine open are local coordinates on it: their differentials form a
basis of `Ω_{𝒪(W)/k}` on every affine open `W ⊆ U`. -/
theorem isLocalCoordinatesOn_of_isLocalCoordinates (sX : X ⟶ Spec (.of k))
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} {x : Fin n → Γ(X, U)}
    (hx : IsLocalCoordinates sX U x) : IsLocalCoordinatesOn sX U x := by
  let := MMP.Mori.sectionAlgebra sX U
  obtain ⟨φ, hφ, hφX, hφC⟩ := exists_etale_mvPolynomial sX hU hx
  let : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := φ.toAlgebra
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (hφC a).symm)
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := hφ
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k
    (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U)
  let b : Module.Basis (Fin n) Γ(X, U) (KaehlerDifferential k Γ(X, U)) :=
    (hbc.basis (KaehlerDifferential.mvPolynomialBasis k _)).reindex Equiv.ulift
  have hb : ∀ i, b i = KaehlerDifferential.D k Γ(X, U) (x i) := by
    intro i
    simp only [b, Module.Basis.reindex_apply, IsBaseChange.basis_apply,
      KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
    exact congrArg _ (hφX _)
  exact fun W h => MMP.Flips.ResolutionInputs.exists_basis_res sX hU W.2 h x b hb

/-- An étale coordinate on an affine open is a nonzerodivisor there. -/
theorem mem_nonZeroDivisors_of_isLocalCoordinates (sX : X ⟶ Spec (.of k))
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} {x : Fin n → Γ(X, U)}
    (hx : IsLocalCoordinates sX U x) (i : Fin n) : x i ∈ nonZeroDivisors Γ(X, U) := by
  obtain ⟨φ, hφ, hφX, -⟩ := exists_etale_mvPolynomial sX hU hx
  let : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := hφ
  have hreg : IsSMulRegular Γ(X, U) (MvPolynomial.X (ULift.up i) : MvPolynomial _ k) :=
    Module.Flat.isSMulRegular_of_isRegular (isRegular_iff_ne_zero.mpr (MvPolynomial.X_ne_zero _))
  have hmul : ∀ t : Γ(X, U), (MvPolynomial.X (ULift.up i) : MvPolynomial _ k) • t = x i * t :=
    fun t => (Algebra.smul_def _ _).trans (congrArg (· * t) (hφX _))
  refine mem_nonZeroDivisors_iff.mpr ⟨fun t ht => hreg ?_, fun t ht => hreg ?_⟩
  · change _ • t = _ • (0 : Γ(X, U))
    rw [hmul, hmul, mul_zero, ht]
  · change _ • t = _ • (0 : Γ(X, U))
    rw [hmul, hmul, mul_zero, mul_comm, ht]

end MMP.Resolution

end
