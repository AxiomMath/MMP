module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Preadmissible.ConductorDescent
public import MMP.AlgebraicGeometry.Singularities.DltFloor.Sdlt
import MMP.AlgebraicGeometry.Singularities.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.StalkValuationRing
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier

/-!
# Preadmissible lifting when the floor image has the structure-sheaf property

Let `(X, B)` be a `ℚ`-factorial projective dlt pair on a normal complex variety of dimension
`n + 1` whose adjoint `D = K_X + B` is semiample, with semiample contraction `f : X ⟶ R`
(`f_* 𝒪_X = 𝒪_R`) and `kD ∼_ℚ f^*H` for an ample Cartier divisor `H` on `R`. Let `S = ⌊B⌋ ≠ 0`
with its reduced structure, `V = f(S)` with its reduced structure, and suppose
`f_* 𝒪_S = 𝒪_V`. For every even `m` divisible by `k`, the projection formula identifies
`H⁰(S, mD|_S)` with `H⁰(V, M|_V)` and `H⁰(X, mD)` with `H⁰(R, M)`, `M = (m/k)H`; Serre
vanishing for `𝓘_V(aM)` then lifts the `a`-th powers of finitely many admissible floor sections
to sections on `X` for all large `a`, and these lifts are preadmissible because their floor
restrictions are admissible. If the given floor sections generate `mD|_S`, these lifts together
with the pull-backs of generators of `𝓘_V(aM)` generate `𝒪_X(amD)`: near every point a single
section of `amD` generates, and its residue along every floor component is either zero (a section
of `𝓘_V(aM)` pulled back) or the `a`-th power of one of the given systems.

## Main results

* `MMP.Fourfold.exists_isPoincareResidue_pow_of_mem_admissibleSections`: equal positive powers
  of finitely many admissible floor sections lift to preadmissible sections, and preadmissible
  sections generate `𝒪_X(amD)` in that degree when the given admissible floor sections generate
  `mD|_S`, by sections whose floor residues are either all zero or the `a`-th powers of one of
  the given systems.

## Implementation notes

The normal components of the floor are given as data `C P`, `j P`, `BC P` indexed by the prime
divisors `P` with `⌊coeff_P B⌋ ≠ 0`, each the adjunction step onto `P` with its different
(`MMP.Fourfold.IsAdjunctionStep`). An admissible section of `mD|_S` is an admissible system
`t ∈ MMP.Fourfold.admissibleSections RS` on the collection of dlt pairs `(C_P, B_{C_P})`; on a dlt
floor these are exactly the sections of `mD|_S` whose restrictions to all floor strata are
admissible. A section `s` of `amD` *lifts* `t^a` when its Poincaré residue
(`MMP.Fourfold.IsPoincareResidue`) along every `j_P` is `t_P^{⊗a}`; the power is written in
coordinates: if `t_P = c · ω^{⊗m}` then `t_P^{⊗a} = c^a · ω^{⊗am}` (`MMP.Fourfold.formPow`).
The preadmissible sections of `amD` are `MMP.Fourfold.preadmissibleSections` of any residue
restriction structure on the single pair `(X, B)` in degree `am`, and generation is
`MMP.Mori.GeneratesOn`. `kD ∼_ℚ f^*H` is a Cartier divisor `M` on `X` with `M = f^*H`
(`MMP.Mori.Divisor.IsPullback`) and `M ∼_ℚ k(K_X + B)`
(`MMP.Mori.QDivisor.QLinearlyEquivalent`): the semiample contraction only gives
`𝒪_X(k(K_X + B)) ≅ f^*𝒪_R(H)`, and the conclusion, about sections of `am(K_X + B)` and their
residues, does not depend on the representative. `f_* 𝒪_X = 𝒪_R` and `f_* 𝒪_S = 𝒪_V` are the
bijectivity of `f.app U`, resp. `f_S.app U`, on every open `U`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold
open MMP.Mori hiding IsPair

namespace Proof_lem_fourfold_admissible_lifting_stein_floor

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

open scoped WithZero

/-! ### Crepant identifications of floor models -/

open MMP.Threefold.Mori.Helpers MMP.Threefold.Mori.ModelIndependence in
/-- **Orders of pulled-back forms along a valuation.** Let `σ : k(X') ≅ k(X)`, `Γ` a prime
divisor of `X` and `(Y, f, E)` a divisor over `X'` whose valuation is `v_Γ ∘ σ`. Then
`ord_Γ(σ^* τ) = ord_E(f^* τ)`: the isomorphism `φ = σ ∘ (f^*)⁻¹ : k(Y) → k(X)` carries `v_E` to
`v_Γ`, hence `𝒪_{Y,E}` onto `𝒪_{X,Γ}`, and `σ^* = φ^* ∘ f^*`. -/
private theorem ordForm_pluriformPullback_eq_ordPullback {k : Type u} [Field k] [CharZero k]
    {X X' : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hX' : IsNormalVariety k sX') {n : ℕ} (hn : topologicalKrullDim X = n)
    (hn' : topologicalKrullDim X' = n)
    (σ : FunctionFieldEquiv sX sX') (Γ : MMP.Mori.PrimeDivisor X) (D : DivisorOver k sX')
    (hv : ∀ g : X'.functionField, D.valuation g = Γ.divisorialValuation ((σ.toHom) g))
    {m : ℤ} (τ : RationalPluriForms sX' n m) :
    Γ.ordForm (pluriformPullback sX sX' σ.toHom n m τ) = D.ordPullback τ := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX') := D.isNormalVariety.1.toLocallyOfFiniteType
  let A := functionFieldAlgebra sX
  let A' := functionFieldAlgebra sX'
  let AY := functionFieldAlgebra (D.f ≫ sX')
  let Af := functionFieldMapAlgebra D.f
  have hT1 := isScalarTower_functionFieldMap sX' D.f
  have hb := D.isBirationalMorphism.functionFieldMap_bijective
  let F := RingEquiv.ofBijective _ hb
  let φ : D.Y.functionField →+* X.functionField := (σ.toHom).toRingHom.comp F.symm.toRingHom
  have hφ : ∀ g, φ (functionFieldMap D.f g) = (σ.toHom) g := fun g => by
    change (σ.toHom) (F.symm (F g)) = _
    rw [F.symm_apply_apply]
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨g, rfl⟩ := σ.surjective z
    exact ⟨functionFieldMap D.f g, hφ g⟩
  have hval : ∀ y : D.Y.functionField,
      Γ.divisorialValuation (φ y) = D.E.divisorialValuation y := by
    intro y
    obtain ⟨g, rfl⟩ := hb.2 y
    rw [hφ g, ← hv g]
    rfl
  have hord : ∀ y : D.Y.functionField,
      X.ord (φ y) Γ.genericPoint = D.Y.ord y D.E.genericPoint := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp [Scheme.ord_zero]
    · have hey : φ y ≠ 0 := (map_ne_zero φ).mpr hy
      have h1 := hval y
      rw [Γ.divisorialValuation_eq_exp_neg_ord hey, D.E.divisorialValuation_eq_exp_neg_ord hy,
        WithZero.exp_inj] at h1
      omega
  have h12 : ∀ a1 : D.E.localRing, ∃ a2 : Γ.localRing,
      algebraMap Γ.localRing X.functionField a2 =
        φ (algebraMap D.E.localRing D.Y.functionField a1) := by
    intro a1
    have : D.E.divisorialValuation (algebraMap D.E.localRing D.Y.functionField a1) ≤ 1 :=
      (D.E.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [← hval] at this
    obtain ⟨a2, ha2⟩ := (Γ.divisorialValuation_le_one_iff _).mp this
    exact ⟨a2, ha2⟩
  have h21 : ∀ a2 : Γ.localRing, ∃ a1 : D.E.localRing,
      φ (algebraMap D.E.localRing D.Y.functionField a1) =
        algebraMap Γ.localRing X.functionField a2 := by
    intro a2
    obtain ⟨y, hy⟩ := hφs (algebraMap Γ.localRing X.functionField a2)
    have : D.E.divisorialValuation y ≤ 1 := by
      rw [← hval, hy]
      exact (Γ.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (D.E.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by rwa [ha1]⟩
  obtain ⟨ψ, hψb, hψ⟩ := exists_ringHom_bijective_of_range φ h12 h21
  have hd' : (Algebra.trdeg k X'.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX') hn'
  have htr : Algebra.trdeg k X'.functionField = Algebra.trdeg k D.Y.functionField :=
    trdeg_functionField_eq_of_bijective sX' D.f hb
  have htrX : Algebra.trdeg k X.functionField = Algebra.trdeg k X'.functionField :=
    trdeg_functionField_eq (sX := sX) (sX' := sX') hn hn'
  have hd1 : (Algebra.trdeg k D.Y.functionField).toNat = n := by rwa [← htr]
  letI := stalkAlgebra (D.f ≫ sX') D.E.genericPoint
  letI := stalkAlgebra sX Γ.genericPoint
  haveI := isScalarTower_stalk_functionField (D.f ≫ sX') D.E.genericPoint
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  letI Aφ : Algebra D.Y.functionField X.functionField := φ.toAlgebra
  have hTφ : IsScalarTower k D.Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change algebraMap k X.functionField c = φ (algebraMap k D.Y.functionField c)
    rw [IsScalarTower.algebraMap_apply k X'.functionField D.Y.functionField c]
    change _ = φ (functionFieldMap D.f (algebraMap k X'.functionField c))
    rw [hφ]
    exact ((σ.toHom).commutes c).symm
  letI : Algebra D.E.localRing Γ.localRing := ψ.toAlgebra
  letI : Algebra D.E.localRing X.functionField :=
    ((algebraMap Γ.localRing X.functionField).comp ψ).toAlgebra
  have hS1 : IsScalarTower k D.E.localRing Γ.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply IsFractionRing.injective Γ.localRing X.functionField
    change _ = algebraMap Γ.localRing X.functionField (ψ (algebraMap k D.E.localRing c))
    rw [hψ, ← IsScalarTower.algebraMap_apply k D.E.localRing D.Y.functionField c,
      ← IsScalarTower.algebraMap_apply k Γ.localRing X.functionField c]
    exact IsScalarTower.algebraMap_apply k D.Y.functionField X.functionField c
  have hS2 : IsScalarTower D.E.localRing Γ.localRing X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS3 : IsScalarTower D.E.localRing D.Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => hψ a
  have hS4 : IsScalarTower k D.E.localRing X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = algebraMap Γ.localRing X.functionField (ψ (algebraMap k D.E.localRing c))
    rw [IsScalarTower.algebraMap_apply k Γ.localRing X.functionField c,
      IsScalarTower.algebraMap_apply k D.E.localRing Γ.localRing c]
    rfl
  have : Algebra.EssFiniteType k D.Y.functionField :=
    essFiniteType_functionField (sX := D.f ≫ sX')
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX' D.f hb hd'
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator (k := k) (K := D.Y.functionField)
    (K' := X.functionField) (htr.symm.trans htrX.symm) hd1
  have hω0φ : IsPullbackGenerator X.functionField
      (topFormsMap k X'.functionField D.Y.functionField n ω0) :=
    IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  obtain ⟨σE, hσE, h0σE⟩ := D.E.exists_topForms_generator (sX := D.f ≫ sX') hd1
  have hωT : IsPullbackGenerator X.functionField
      (topFormsMap k D.E.localRing D.Y.functionField n σE) :=
    IsPullbackGenerator.of_span hω1 (span_singleton_topFormsMap (nonZeroDivisors _) hσE) h0σE
  have key := ordAt_pullbackForms_eq (k := k) (K := D.Y.functionField) (K' := X.functionField)
    (A := D.E.localRing) (A' := Γ.localRing) (d := n) (m := m) hψb
    (v := fun y => D.Y.ord y D.E.genericPoint) (v' := fun y => X.ord y Γ.genericPoint)
    (fun x y hx hy => D.E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => D.E.ord_algebraMap_of_isUnit ha)
    (fun x y hx hy => Γ.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => Γ.ord_algebraMap_of_isUnit ha)
    (fun x => hord x) hσE hωT (pullbackForms (K' := D.Y.functionField) m τ)
  let Aσ : Algebra X'.functionField X.functionField := (σ.toHom).toRingHom.toAlgebra
  have tσ : @IsScalarTower k X'.functionField X.functionField _ Aσ.toSMul _ := by
    letI := Aσ; exact IsScalarTower.of_algebraMap_eq fun c => ((σ.toHom).commutes c).symm
  have t3 : @IsScalarTower X'.functionField D.Y.functionField X.functionField Af.toSMul
      Aφ.toSMul Aσ.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ Af Aφ Aσ fun g => (hφ g).symm
  have hcomp := @pullbackForms_comp k _ n m X'.functionField D.Y.functionField
    X.functionField _ _ _ A' AY A Af Aφ Aσ hT1 hTφ tσ t3 ω0 hω0 hω0φ τ
  calc Γ.ordForm (pluriformPullback sX sX' σ.toHom n m τ)
      = ordAt Γ.localRing (fun y => X.ord y Γ.genericPoint)
          (@pullbackForms k _ X'.functionField X.functionField _ _ A' A Aσ tσ n m τ) := rfl
    _ = ordAt Γ.localRing (fun y => X.ord y Γ.genericPoint)
          (pullbackForms (K' := X.functionField) m
            (pullbackForms (K' := D.Y.functionField) m τ)) := by rw [hcomp]
    _ = D.ordPullback τ := key

section ResidueFunctoriality

variable {k : Type u} [Field k] {X X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']

/-- `φ^*(c w^{⊗a}) = φ(c) (φ^*w)^{⊗a}` for every `d`-form `w`, on varieties of dimension `d`. -/
private theorem pluriformPullback_smul_formPow' [CharZero k] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sX'] {d : ℕ} (hX : topologicalKrullDim X = d)
    (hX' : topologicalKrullDim X' = d) (φ : FunctionFieldHom sX sX')
    (w : letI := functionFieldAlgebra sX'; ⋀[X'.functionField]^d Ω[X'.functionField⁄k])
    (a : ℕ) (c : X'.functionField) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    pluriformPullback sX sX' φ d a (c • formPow w a) =
      φ c • formPow (topFormsMap k X'.functionField X.functionField d w) a := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_functionFieldHom hX hX' φ
    have e1 : (formPow w 0 : PluriForms k X'.functionField d (0 : ℕ)) = formPow ω 0 := by
      unfold formPow; congr 1; funext i; exact i.elim0
    have e2 : (formPow (topFormsMap k X'.functionField X.functionField d w) 0 :
        PluriForms k X.functionField d (0 : ℕ)) =
        formPow (topFormsMap k X'.functionField X.functionField d ω) 0 := by
      unfold formPow; congr 1; funext i; exact i.elim0
    rw [e1, e2]
    exact pluriformPullback_smul_formPow φ hω 0 c
  by_cases hw : w = 0
  · have h0 : ∀ {K : Type u} [Field K] [Algebra k K],
        (formPow (0 : ⋀[K]^d Ω[K⁄k]) a : PluriForms k K d a) = 0 := by
      intro K _ _
      unfold formPow
      exact (PiTensorProduct.tprod K).map_coord_zero ⟨0, ha⟩ rfl
    subst hw
    rw [map_zero (topFormsMap k X'.functionField X.functionField d), h0, h0, smul_zero, smul_zero]
    exact map_zero (pluriformPullback sX sX' φ d a)
  · obtain ⟨b⟩ := exists_basis_topForms (sX := sX') hX'
    have hspan : Submodule.span X'.functionField {w} = ⊤ := by
      have hc : b.repr w () ≠ 0 := by
        intro h
        apply hw
        rw [← b.sum_repr w]
        simp [h]
      obtain ⟨r, hr⟩ : ∃ r, r = b.repr w () := ⟨_, rfl⟩
      rw [← hr] at hc
      refine Submodule.eq_top_iff'.mpr fun x => Submodule.mem_span_singleton.mpr
        ⟨b.repr x () / r, ?_⟩
      have hx : x = b.repr x () • b () := by
        conv_lhs => rw [← b.sum_repr x]
        simp
      have hw' : w = r • b () := by
        conv_lhs => rw [← b.sum_repr w]
        simp [hr]
      rw [hw', smul_smul, div_mul_cancel₀ _ hc, ← hx]
    exact pluriformPullback_smul_formPow φ
      (isPullbackGenerator_functionFieldHom hX hX' φ hspan hw) a c

/-- The image of `c • ιMulti (D ∘ v)` under `φ^*`. -/
private theorem topFormsMap_smul_ιMulti_D (φ : FunctionFieldHom sX sX') {d : ℕ}
    (c : X'.functionField) (v : Fin d → X'.functionField) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    topFormsMap k X'.functionField X.functionField d
        (c • exteriorPower.ιMulti X'.functionField d
          fun i => KaehlerDifferential.D k X'.functionField (v i)) =
      φ c • exteriorPower.ιMulti X.functionField d
          fun i => KaehlerDifferential.D k X.functionField (φ (v i)) := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  rw [LinearMap.map_smul, topFormsMap_ιMulti, algebra_compatible_smul X.functionField c]
  simp only [KaehlerDifferential.map_D]
  rfl

/-- **Poincaré residues are functorial under isomorphisms of the local rings.** Let
`σ : k(Y') → k(Y)` and `σ_T : k(T') → k(T)` be `k`-homomorphisms of function fields, and
`ψ : 𝒪_{Y',T'} → 𝒪_{Y,T}` a ring homomorphism of the local rings along the divisors, compatible
with `σ` and `σ_T` and preserving orders. Then `Res_T(σ^*τ) = σ_T^* Res_{T'}(τ)`. -/
private theorem isPoincareResidue_pluriformPullback [CharZero k] {T T' : Scheme.{u}} [IsIntegral T]
    [IsIntegral T'] [IsLocallyNoetherian X] [IsLocallyNoetherian X'] (j : T ⟶ X) (j' : T' ⟶ X')
    [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sX'] [LocallyOfFiniteType (j ≫ sX)] [LocallyOfFiniteType (j' ≫ sX')]
    {n : ℕ} (hX : topologicalKrullDim X = (n + 1 : ℕ))
    (hX' : topologicalKrullDim X' = (n + 1 : ℕ)) (hT : topologicalKrullDim T = n)
    (hT' : topologicalKrullDim T' = n) (σ : FunctionFieldHom sX sX')
    (σT : FunctionFieldHom (j ≫ sX) (j' ≫ sX'))
    (ψ : X'.presheaf.stalk (j' (genericPoint T')) →+* X.presheaf.stalk (j (genericPoint T)))
    (hψ : ∀ a, algebraMap _ X.functionField (ψ a) = σ (algebraMap _ X'.functionField a))
    (hψT : ∀ a, (j.stalkMap (genericPoint T)).hom (ψ a) =
      σT ((j'.stalkMap (genericPoint T')).hom a))
    (hord : ∀ a, X.ord (algebraMap _ X.functionField (ψ a)) (j (genericPoint T)) =
      X'.ord (algebraMap _ X'.functionField a) (j' (genericPoint T')))
    {m : ℕ} {τ : RationalPluriForms sX' (n + 1) m} {ρ : RationalPluriForms (j' ≫ sX') n m}
    (h : IsPoincareResidue sX' j' n m τ ρ) :
    IsPoincareResidue sX j n m (pluriformPullback sX sX' σ (n + 1) m τ)
      (pluriformPullback (j ≫ sX) (j' ≫ sX') σT n m ρ) := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (j' ≫ sX')
  let := functionFieldAlgebra (j ≫ sX)
  obtain ⟨t, g, x, ht, rfl, rfl⟩ := h
  refine ⟨ψ t, ψ g, fun i => ψ (x i), by rwa [hord], ?_, ?_⟩
  · have e := pluriformPullback_smul_formPow' hX hX' σ
      ((algebraMap _ X'.functionField t)⁻¹ • exteriorPower.ιMulti X'.functionField (n + 1)
        (Fin.cons (KaehlerDifferential.D k X'.functionField (algebraMap _ _ t))
          fun i => KaehlerDifferential.D k X'.functionField (algebraMap _ _ (x i)))) m
      (algebraMap _ X'.functionField g)
    have e2 := topFormsMap_smul_ιMulti_D σ (algebraMap _ X'.functionField t)⁻¹
      (Fin.cons (algebraMap _ X'.functionField t) fun i => algebraMap _ X'.functionField (x i) :
        Fin (n + 1) → X'.functionField)
    have hc : ∀ {K : Type u} [Field K] [Algebra k K] (a : K) (b : Fin n → K),
        (Fin.cons (KaehlerDifferential.D k K a) (fun i => KaehlerDifferential.D k K (b i)) :
          Fin (n + 1) → Ω[K⁄k]) = fun i => KaehlerDifferential.D k K ((Fin.cons a b : Fin (n + 1) → K) i) := by
      intro K _ _ a b
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    refine e.trans ?_
    rw [hc, e2, hc]
    simp only [hψ, map_inv₀, formPow]
    congr 4
    funext _
    congr 2
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  · have e := pluriformPullback_smul_formPow' hT hT' σT
      (exteriorPower.ιMulti T'.functionField n
        fun i => KaehlerDifferential.D k T'.functionField ((j'.stalkMap (genericPoint T')).hom (x i)))
      m ((j'.stalkMap (genericPoint T')).hom g)
    refine e.trans ?_
    have e2 := topFormsMap_smul_ιMulti_D σT 1
      (fun i => (j'.stalkMap (genericPoint T')).hom (x i))
    rw [one_smul, map_one, one_smul] at e2
    rw [e2]
    simp only [hψT, formPow]
    rfl

end ResidueFunctoriality

/-- A closed subscheme whose underlying set is a prime divisor of a variety of dimension `e + 1`
has dimension `e`. -/
private theorem topologicalKrullDim_eq_of_range_eq_support {k : Type u} [Field k] {Y T : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [LocallyOfFiniteType sY]
    (j : T ⟶ Y) [IsClosedImmersion j]
    (P : MMP.Mori.PrimeDivisor Y) (h : Set.range j.base = (P.support : Set Y)) {e : ℕ}
    (hY : topologicalKrullDim Y = (e + 1 : ℕ)) : topologicalKrullDim T = e := by
  have hemb := j.isClosedEmbedding.isEmbedding
  let φ := hemb.toHomeomorph
  have h1 : topologicalKrullDim T = topologicalKrullDim (Set.range j.base) :=
    le_antisymm φ.isInducing.topologicalKrullDim_le φ.symm.isInducing.topologicalKrullDim_le
  rw [h1, h, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have h2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY P.genericPoint
  rw [P.coheight_genericPoint, hY] at h2
  generalize topologicalKrullDim (closure {P.genericPoint} : Set Y) = a at h2 ⊢
  rcases a with _ | _ | a
  · exfalso
    change (⊥ : WithBot ℕ∞) + 1 = _ at h2
    rw [WithBot.bot_add] at h2
    exact WithBot.bot_ne_coe (h2.trans (by push_cast; rfl))
  · exfalso
    change ((⊤ : ℕ∞) : WithBot ℕ∞) + ((1 : ℕ∞) : WithBot ℕ∞) = (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) at h2
    rw [← WithBot.coe_add, WithBot.coe_inj, top_add] at h2
    exact ENat.top_ne_coe _ h2
  · have : ((a + 1 : ℕ) : WithBot ℕ∞) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← h2]; push_cast; rfl
    have : a + 1 = e + 1 := by exact_mod_cast this
    obtain rfl : a = e := by omega
    rfl

/-- The generic point of a closed subscheme with underlying set a prime divisor `P` is the generic
point of `P`. -/
private theorem map_genericPoint_eq_of_range_eq {Y T : Scheme.{u}} [IrreducibleSpace T]
    (j : T ⟶ Y) (P : MMP.Mori.PrimeDivisor Y) (hrange : Set.range j.base = (P.support : Set Y)) :
    j (genericPoint T) = P.genericPoint := by
  have h1 : closure ({j (genericPoint T)} : Set Y) = Set.range j.base := by
    apply le_antisymm
    · rw [hrange]
      exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure P ▸
        isClosed_closure).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (hrange ▸ Set.mem_range_self _))
    · rintro _ ⟨z, rfl⟩
      have hz : genericPoint T ⤳ z := (genericPoint_spec T).specializes trivial
      exact specializes_iff_mem_closure.mp (hz.map j.continuous)
  have h2 : closure ({j (genericPoint T)} : Set Y) = closure {P.genericPoint} := by
    rw [h1, hrange, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact (inseparable_iff_closure_eq.mpr h2).eq

section CrepantModel

variable {k : Type} [Field k]

/-- Pull-back of rational forms along a composite of birational morphisms. -/
private theorem pullbackRationalPluriForms_comp' [PerfectField k] {X Y Z : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f] [IsDominant g] [LocallyOfFiniteType (f ≫ sX)]
    (hf : Function.Bijective (functionFieldMap f)) (hg : Function.Bijective (functionFieldMap g))
    {d : ℕ} (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower k X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have hd' : (Algebra.trdeg k Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap k X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- **Log discrepancies along a crepant model.** Let `g : V ⟶ T` be a proper birational
morphism of normal varieties, `ρ ≠ 0` a rational top form on `T` with `div ρ` canonical, and
`C` the crepant boundary on `V`: `g^*(div ρ + B_T) = div(g^*ρ) + C`. Then every divisor `E`
proper over `V` has the same log discrepancy over `(V, C)` as over `(T, B_T)`. -/
private theorem exists_isLogDiscrepancy_compDivisorOver [PerfectField k] {T V : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [LocallyOfFiniteType sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (hT : IsNormalVariety k sT) (g : V ⟶ T) [IsProper g] (hg : IsBirationalMorphism g)
    (hV : IsNormalVariety k (g ≫ sT)) [IsDominant g] [LocallyOfFiniteType (g ≫ sT)] {d : ℕ}
    {ρ : RationalPluriForms sT d 1} (hρ : ρ ≠ 0) (hK : (divisorOfForm ρ).IsCanonicalDivisor sT d)
    (hρV : pullbackRationalPluriForms sT g ρ ≠ 0)
    (hKV : (divisorOfForm (pullbackRationalPluriForms sT g ρ)).IsCanonicalDivisor (g ≫ sT) d)
    {BT : QDivisor T} {C : QDivisor V} (hq : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsQCartier)
    {hgen : ∀ Z : irreducibleComponents V,
      g (componentGenericPoint V Z) ∉ (Divisor.toQDivisor (divisorOfForm ρ) + BT).supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsPullback g hgen
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sT g ρ)) + C))
    (E : DivisorOver k (g ≫ sT)) (hE : IsProper E.f) :
    ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy (g ≫ sT) d (QDivisor.toRDivisor C) E a ∧
      MMP.Intersection.IsLogDiscrepancy sT d (QDivisor.toRDivisor BT)
        (compDivisorOver g hV hg E) a := by
  set m := (Divisor.toQDivisor (divisorOfForm ρ) + BT).cartierIndex hq
  have hm : 0 < m := QDivisor.cartierIndex_pos hq
  obtain ⟨D0, hD0, hD0c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hq
  obtain ⟨D0V, hD0V, hpbV⟩ := hpb m hm D0 hD0 hD0c
  have hD0Vc : D0V.IsCartier := hpbV.isCartier hD0c
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have : LocallyOfFiniteType (E.f ≫ g ≫ sT) := E.isNormalVariety.1.toLocallyOfFiniteType
  have : CompactSpace E.Y := by
    have := E.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ g ≫ sT)
  have hgenY := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant E.f D0V
  set D0Y := D0V.pullback hD0Vc hgenY
  have hY : D0V.IsPullback E.f hgenY D0Y := Divisor.isPullback_pullback hD0Vc hgenY
  have hcomp : D0.IsPullback (E.f ≫ g)
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (E.f ≫ g) D0) D0Y :=
    MMP.ProgramBaseChange.divisor_isPullback_comp rfl hpbV hY _
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1 + (E.ordPullback (pullbackRationalPluriForms sT g ρ) : ℝ) -
    ∑ _i : Fin 1, (1 / (m : ℝ)) * (D0Y.coeff E.E : ℝ), ⟨hV, hE, _, hρV,
      ⟨_, hKV, fun Γ => coeff_divisorOfForm _ Γ⟩, 1, fun _ => 1 / (m : ℝ), fun _ => D0V,
      fun _ => D0Y, fun _ => hD0Vc, fun Γ => ?_, fun _ => ⟨hgenY, hY⟩, rfl⟩,
    ⟨hT, ?_, ρ, hρ, ⟨_, hK, fun Γ => coeff_divisorOfForm _ Γ⟩, 1, fun _ => 1 / (m : ℝ),
      fun _ => D0, fun _ => D0Y, fun _ => hD0c, fun Γ => ?_, fun _ => ⟨_, hcomp⟩, ?_⟩⟩
  · have h := congrArg (fun D : QDivisor V => D.coeff Γ) hD0V
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      coeff_divisorOfForm] at h
    have h' : ((D0V.coeff Γ : ℚ) : ℝ) = (m : ℝ) * (((Γ.ordForm (pullbackRationalPluriForms sT g ρ) :
        ℚ) : ℝ) + ((C.coeff Γ : ℚ) : ℝ)) := by
      rw [h, zsmul_eq_mul]; push_cast; ring
    rw [Fin.sum_univ_one, QDivisor.coeff_toRDivisor]
    push_cast at h' ⊢
    rw [h']
    field_simp
  · haveI := hE
    exact (inferInstance : IsProper (E.f ≫ g))
  · have h := congrArg (fun D : QDivisor T => D.coeff Γ) hD0
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      coeff_divisorOfForm] at h
    have h' : ((D0.coeff Γ : ℚ) : ℝ) = (m : ℝ) * (((Γ.ordForm ρ : ℚ) : ℝ) +
        ((BT.coeff Γ : ℚ) : ℝ)) := by
      rw [h, zsmul_eq_mul]; push_cast; ring
    rw [Fin.sum_univ_one, QDivisor.coeff_toRDivisor]
    push_cast at h' ⊢
    rw [h']
    field_simp
  · have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sT)
      hK.topologicalKrullDim_eq
    have hc := pullbackRationalPluriForms_comp' g E.f hg.functionFieldMap_bijective
      E.isBirationalMorphism.functionFieldMap_bijective hd ρ
    have : (compDivisorOver g hV hg E).ordPullback ρ =
        E.ordPullback (pullbackRationalPluriForms sT g ρ) := by
      change E.E.ordForm (pullbackRationalPluriForms sT (E.f ≫ g) ρ) =
        E.E.ordForm (pullbackRationalPluriForms (g ≫ sT) E.f (pullbackRationalPluriForms sT g ρ))
      rw [hc]
      rfl
    rw [this]
    rfl

/-- **A crepant proper birational morphism is a crepant birational map.** If `g : V ⟶ T` is a
proper birational morphism of normal varieties and `g^*(div ρ + B_T) = div(g^*ρ) + C`, then
`g^* : k(T) ≅ k(V)` identifies the divisorial log discrepancies of `(V, C)` and `(T, B_T)`. -/
private theorem isCrepantBirationalMap_of_isPullback [PerfectField k] {T V : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [LocallyOfFiniteType sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (hT : IsNormalVariety k sT) (g : V ⟶ T) [IsProper g] (hg : IsBirationalMorphism g)
    (hV : IsNormalVariety k (g ≫ sT)) [IsDominant g] [LocallyOfFiniteType (g ≫ sT)] {d : ℕ}
    {ρ : RationalPluriForms sT d 1} (hρ : ρ ≠ 0) (hK : (divisorOfForm ρ).IsCanonicalDivisor sT d)
    (hρV : pullbackRationalPluriForms sT g ρ ≠ 0)
    (hKV : (divisorOfForm (pullbackRationalPluriForms sT g ρ)).IsCanonicalDivisor (g ≫ sT) d)
    {BT : QDivisor T} {C : QDivisor V} (hq : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsQCartier)
    {hgen : ∀ Z : irreducibleComponents V,
      g (componentGenericPoint V Z) ∉ (Divisor.toQDivisor (divisorOfForm ρ) + BT).supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsPullback g hgen
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sT g ρ)) + C)) :
    IsCrepantBirationalMap (g ≫ sT) sT C BT
      (functionFieldAlgEquiv sT g hg.functionFieldMap_bijective) := by
  have hdT : topologicalKrullDim T = d := hK.topologicalKrullDim_eq
  have hdV : topologicalKrullDim V = d := hKV.topologicalKrullDim_eq
  intro v a
  constructor
  · rintro ⟨n', E, hEv, hEa⟩
    obtain rfl : n' = d := by
      have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hEa).symm.trans hdV
      exact_mod_cast this
    obtain ⟨a0, h1, h2⟩ := exists_isLogDiscrepancy_compDivisorOver hT g hg hV hρ hK hρV hKV hq hpb
      E hEa.2.1
    obtain rfl := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hEa h1 rfl
    refine ⟨n', compDivisorOver g hV hg E, ?_, h2⟩
    rw [valuation_compDivisorOver, hEv]
    rfl
  · rintro ⟨n', D, hDv, hDa⟩
    obtain rfl : n' = d := by
      have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hDa).symm.trans hdT
      exact_mod_cast this
    obtain ⟨E, hE⟩ := exists_divisorOver_comap_eq hV hg D
    obtain ⟨E', hE'⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hV E
    obtain ⟨a0, h1, h2⟩ := exists_isLogDiscrepancy_compDivisorOver hT g hg hV hρ hK hρV hKV hq hpb
      E'.toDivisorOver E'.isProper
    have hval : (compDivisorOver g hV hg E'.toDivisorOver).valuation = D.valuation := by
      rw [valuation_compDivisorOver, hE]
      change (E'.valuation).comap _ = _
      rw [hE']
    obtain rfl := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hDa h2 hval.symm
    refine ⟨n', E'.toDivisorOver, ?_, h1⟩
    change E'.valuation = v
    rw [hE']
    ext x
    obtain ⟨y, rfl⟩ := hg.functionFieldMap_bijective.2 x
    exact congrArg (fun w : Valuation T.functionField ℤᵐ⁰ => w y) (hE.symm.trans hDv)

/-- Two ring homomorphisms out of the function field of an integral scheme agree once the
induced morphisms of spectra agree after `Spec 𝒪_{X,η} ⟶ X`. -/
private theorem ringHom_ext_of_specMap_fromSpecStalk {X : Scheme.{0}} [IsIntegral X]
    {R : CommRingCat.{0}} {α β : X.functionField ⟶ R}
    (h : Spec.map α ≫ X.fromSpecStalk (genericPoint X) =
      Spec.map β ≫ X.fromSpecStalk (genericPoint X)) : α = β :=
  Spec.map_injective ((cancel_mono _).mp h)

/-- **The normalized graph of a birational map.** For a `k`-isomorphism `σ : k(X') ≅ k(X)` of
function fields of integral schemes proper over `k`, the normalization `W` of `X' ×_k X` in the
graph point `Spec k(X) ⟶ X' ×_k X` of `σ` is a normal integral scheme with proper birational
projections `p : W ⟶ X`, `q : W ⟶ X'` over `k` such that `q^* = p^* ∘ σ`. -/
private theorem exists_model_of_functionFieldEquiv {X X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']
    [IsProper sX] [IsProper sX'] (σ : FunctionFieldEquiv sX sX') :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsNormal W) (p : W ⟶ X) (q : W ⟶ X')
      (_ : IsDominant p) (_ : IsDominant q),
      IsProper p ∧ IsProper q ∧ IsBirational p ∧ IsBirational q ∧ p ≫ sX = q ≫ sX' ∧
      letI := functionFieldAlgebra sX
      letI := functionFieldAlgebra sX'
      functionFieldMap q = (functionFieldMap p).comp σ.toRingEquiv.toRingHom := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  set θ : X'.functionField →+* X.functionField := σ.toRingEquiv.toRingHom with hθ
  set F := X.fromSpecStalk (genericPoint X) with hF
  set F' := X'.fromSpecStalk (genericPoint X') with hF'
  have hα : (Spec.map (CommRingCat.ofHom θ) ≫ F') ≫ sX' = F ≫ sX := by
    rw [Category.assoc, hF', hF, MMP.fromSpecStalk_comp_eq,
      MMP.fromSpecStalk_comp_eq, ← Spec.map_comp]
    congr 1
    ext c
    exact σ.commutes c
  set γ : Spec X.functionField ⟶ Limits.pullback sX' sX :=
    Limits.pullback.lift (Spec.map (CommRingCat.ofHom θ) ≫ F') F hα with hγ
  haveI : QuasiCompact γ := quasiCompact_of_isField (by exact Field.toIsField _) _
  haveI : QuasiSeparated γ := QuasiSeparated.of_quasiSeparatedSpace _
  have hγs : γ ≫ Limits.pullback.snd sX' sX = F := Limits.pullback.lift_snd _ _ _
  have hγf : γ ≫ Limits.pullback.fst sX' sX = Spec.map (CommRingCat.ofHom θ) ≫ F' :=
    Limits.pullback.lift_fst _ _ _
  -- finiteness of the normalization
  haveI : LocallyOfFiniteType (Limits.pullback.snd sX' sX ≫ sX) := inferInstance
  have hP : IsNagataScheme (Limits.pullback sX' sX) :=
    isNagataScheme_of_locallyOfFiniteType (Limits.pullback.snd sX' sX ≫ sX)
      (isNagataScheme_spec_of_isNagataRing _ IsNagataRing.of_field)
  have : Finite (Spec X.functionField) :=
    inferInstanceAs (Finite (PrimeSpectrum X.functionField))
  haveI hfin : IsFinite γ.fromNormalization := by
    refine isFinite_fromNormalization γ hP
      (fun U _ => have : Finite U := Subtype.finite
        TopologicalSpace.NoetherianSpace.finite_irreducibleComponents) fun x => ?_
    let := (γ.residueFieldMap x.1).hom.toAlgebra
    have hsurj : Function.Surjective (γ.residueFieldMap x.1).hom := by
      have h := surjective_residueFieldMap_of_surjectiveOnStalks F x.1
      rw [Scheme.Hom.residueFieldMap_congr hγs.symm, Scheme.residueFieldMap_comp] at h
      exact fun z => ⟨_, (h z).choose_spec⟩
    have : Algebra.EssFiniteType (Limits.pullback sX' sX |>.residueField (γ x.1))
        ((Spec X.functionField).residueField x.1) := by
      rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
      exact (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
    exact IntermediateField.fg_top _ _
  haveI : IsNormal γ.normalization := isNormal_normalization_of_isField (by exact Field.toIsField _) _
  haveI : IsIntegral γ.normalization := inferInstance
  set u := γ.fromNormalization ≫ Limits.pullback.snd sX' sX with hu
  set v := γ.fromNormalization ≫ Limits.pullback.fst sX' sX with hv
  set j := γ.toNormalization with hj
  have hjγ : j ≫ γ.fromNormalization = γ := Scheme.Hom.toNormalization_fromNormalization γ
  have hju : j ≫ u = F := by rw [hu, ← Category.assoc, hjγ, hγs]
  have hjv : j ≫ v = Spec.map (CommRingCat.ofHom θ) ≫ F' := by
    rw [hv, ← Category.assoc, hjγ, hγf]
  letI := isDominant_fromSpecStalk_genericPoint X
  letI := isDominant_fromSpecStalk_genericPoint X'
  have : IsDominant (j ≫ u) := by rw [hju]; infer_instance
  haveI hud : IsDominant u := IsDominant.of_comp j _
  have : IsDominant (j ≫ v) := by
    rw [hjv]
    haveI : Surjective (Spec.map (CommRingCat.ofHom θ)) := surjective_specMap_of_field θ
    infer_instance
  haveI hvd : IsDominant v := IsDominant.of_comp j _
  haveI hjd : IsDominant j := inferInstance
  set E := (Spec X.functionField).fromSpecStalk (genericPoint (Spec X.functionField)) with hE
  have hFE : Spec.map (CommRingCat.ofHom (functionFieldMap F)) = E :=
    (cancel_mono F).mp (functionFieldMap_fromSpecStalk F)
  have h2 : (functionFieldMap j).comp (functionFieldMap u) = functionFieldMap F := by
    have : CommRingCat.ofHom ((functionFieldMap j).comp (functionFieldMap u)) =
        CommRingCat.ofHom (functionFieldMap F) := by
      refine ringHom_ext_of_specMap_fromSpecStalk ?_
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, functionFieldMap_fromSpecStalk u,
        ← Category.assoc, functionFieldMap_fromSpecStalk j, Category.assoc, hju, hFE]
    exact congrArg CommRingCat.Hom.hom this
  have h1 : (functionFieldMap j).comp (functionFieldMap v) = (functionFieldMap F).comp θ := by
    have : CommRingCat.ofHom ((functionFieldMap j).comp (functionFieldMap v)) =
        CommRingCat.ofHom ((functionFieldMap F).comp θ) := by
      refine ringHom_ext_of_specMap_fromSpecStalk ?_
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, functionFieldMap_fromSpecStalk v,
        ← Category.assoc, functionFieldMap_fromSpecStalk j, Category.assoc, hjv,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hFE]
    exact congrArg CommRingCat.Hom.hom this
  have hFb := bijective_functionFieldMap_fromSpecStalk_genericPoint X
  have hcompat : functionFieldMap v = (functionFieldMap u).comp θ := by
    ext a
    apply (functionFieldMap j).injective
    have e1 := congrArg (fun φ => φ a) h1
    have e2 := congrArg (fun φ => φ (θ a)) h2
    simp only [RingHom.comp_apply] at e1 e2
    rw [e1, ← e2]
    rfl
  refine ⟨γ.normalization, inferInstance, inferInstance, u, v, hud, hvd, inferInstance,
    inferInstance, ?_, ?_, ?_, hcompat⟩
  · refine isBirational_of_surjective_functionFieldMap u fun w => ?_
    obtain ⟨a, ha⟩ := hFb.2 (functionFieldMap j w)
    refine ⟨a, (functionFieldMap j).injective ?_⟩
    have e2 := congrArg (fun φ => φ a) h2
    simp only [RingHom.comp_apply] at e2
    rw [e2, ha]
  · refine isBirational_of_surjective_functionFieldMap v fun w => ?_
    obtain ⟨a, ha⟩ := hFb.2 (functionFieldMap j w)
    obtain ⟨b, rfl⟩ := σ.surjective a
    refine ⟨b, (functionFieldMap j).injective ?_⟩
    have e1 := congrArg (fun φ => φ b) h1
    simp only [RingHom.comp_apply] at e1
    rw [e1, ← ha]
    rfl
  · rw [hu, hv, Category.assoc, Category.assoc, Limits.pullback.condition]

/-- **Log discrepancies of the prime divisors of a model.** If `p : W ⟶ X` is a proper birational
morphism of normal varieties and `G = p^*(div τ + B)`, the prime divisor `F` of `W` has log
discrepancy `1 + ord_F(p^*τ) - coeff_F G` over `(X, B)`. -/
private theorem isLogDiscrepancy_of_isPullback {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hX : IsNormalVariety k sX) (p : W ⟶ X) [IsProper p] (hp : IsBirationalMorphism p)
    (hW : IsNormalVariety k (p ≫ sX)) [IsDominant p] [LocallyOfFiniteType (p ≫ sX)] {n : ℕ}
    {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) (hK : (divisorOfForm τ).IsCanonicalDivisor sX n)
    {B : QDivisor X} {G : QDivisor W} (hq : (Divisor.toQDivisor (divisorOfForm τ) + B).IsQCartier)
    {hgen : ∀ Z : irreducibleComponents W,
      p (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (divisorOfForm τ) + B).supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm τ) + B).IsPullback p hgen G) (F : Mori.PrimeDivisor W) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) ⟨W, p, hW, hp, F⟩
      (1 + ((F.ordForm (pullbackRationalPluriForms sX p τ) : ℤ) : ℝ) - ((G.coeff F : ℚ) : ℝ)) := by
  set m := (Divisor.toQDivisor (divisorOfForm τ) + B).cartierIndex hq
  have hm : 0 < m := QDivisor.cartierIndex_pos hq
  obtain ⟨D0, hD0, hD0c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hq
  obtain ⟨D0W, hD0W, hpbW⟩ := hpb m hm D0 hD0 hD0c
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨hX, inferInstance, τ, hτ, ⟨_, hK, fun Γ => coeff_divisorOfForm _ Γ⟩, 1,
    fun _ => 1 / (m : ℝ), fun _ => D0, fun _ => D0W, fun _ => hD0c, fun Γ => ?_,
    fun _ => ⟨_, hpbW⟩, ?_⟩
  · have h := congrArg (fun D : QDivisor X => D.coeff Γ) hD0
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      coeff_divisorOfForm] at h
    have h' : ((D0.coeff Γ : ℚ) : ℝ) = (m : ℝ) * (((Γ.ordForm τ : ℚ) : ℝ) +
        ((B.coeff Γ : ℚ) : ℝ)) := by
      rw [h, zsmul_eq_mul]; push_cast; ring
    rw [Fin.sum_univ_one, QDivisor.coeff_toRDivisor]
    push_cast at h' ⊢
    rw [h']
    field_simp
  · have h := congrArg (fun D : QDivisor W => D.coeff F) hD0W
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul] at h
    have h' : ((D0W.coeff F : ℚ) : ℝ) = (m : ℝ) * ((G.coeff F : ℚ) : ℝ) := by
      rw [h, zsmul_eq_mul]; push_cast; ring
    rw [Fin.sum_univ_one]
    push_cast at h' ⊢
    rw [h']
    field_simp
    rfl

/-- **Pull-back of a transported form to a common model.** If `p : W ⟶ X` and `q : W ⟶ X'` are
birational with `q^* = p^* ∘ σ`, then along every prime divisor `F` of `W` the forms `p^*(σ^*τ)`
and `q^*τ` have the same order. -/
private theorem ordForm_pullback_pluriformPullback_eq [CharZero k] {X X' W : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') {n : ℕ}
    (hn : topologicalKrullDim X = n) (hn' : topologicalKrullDim X' = n)
    (σ : FunctionFieldEquiv sX sX') (p : W ⟶ X) (q : W ⟶ X') (hp : IsBirationalMorphism p)
    (hq : IsBirationalMorphism q) (hWp : IsNormalVariety k (p ≫ sX))
    (hWq : IsNormalVariety k (q ≫ sX')) [IsDominant p] [IsDominant q]
    (hcompat : ∀ a, functionFieldMap q a = functionFieldMap p ((σ.toHom) a))
    (F : Mori.PrimeDivisor W) {m : ℤ} (τ : RationalPluriForms sX' n m) :
    F.ordForm (pullbackRationalPluriForms sX p (pluriformPullback sX sX' σ.toHom n m τ)) =
      F.ordForm (pullbackRationalPluriForms sX' q τ) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (p ≫ sX) := hWp.1.toLocallyOfFiniteType
  haveI := hX.1
  haveI := hWp.1
  have hnW : topologicalKrullDim W = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hp).symm.trans hn
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra (p ≫ sX)
  let ep : FunctionFieldEquiv (p ≫ sX) sX := functionFieldAlgEquiv sX p hp.functionFieldMap_bijective
  let σ' : FunctionFieldEquiv (p ≫ sX) sX' := σ.trans ep
  have h1 : pullbackRationalPluriForms sX p (pluriformPullback sX sX' σ.toHom n m τ) =
      pluriformPullback (p ≫ sX) sX' σ'.toHom n m τ := by
    have := pluriformPullback_comp (sX := p ≫ sX) (sX' := sX) (sX'' := sX') hnW hn hn' m
      ep.toHom σ.toHom τ
    exact this
  rw [h1]
  let D : DivisorOver k sX' := ⟨W, q, hWq, hq, F⟩
  have hv : ∀ g, D.valuation g = F.divisorialValuation ((σ'.toHom) g) := by
    intro g
    change F.divisorialValuation (functionFieldMap q g) = _
    rw [hcompat]
    rfl
  exact ordForm_pluriformPullback_eq_ordPullback hWp hX' hnW hn' σ' F D hv τ

/-- **Crepant birational maps have equal pull-backs on a common model.** If
`σ : (X, B) ⇢ (X', B')` is crepant, `p : W ⟶ X`, `q : W ⟶ X'` proper birational with
`q^* = p^* ∘ σ`, and `τ = σ^*τ'`, then `p^*(div τ + B) = q^*(div τ' + B')`. -/
private theorem pullback_eq_pullback_of_isCrepantBirationalMap [CharZero k] {X X' W : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral X']
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] [LocallyOfFiniteType sX']
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') {B : QDivisor X} {B' : QDivisor X'}
    (σ : FunctionFieldEquiv sX sX') (hσ : IsCrepantBirationalMap sX sX' B B' σ)
    (p : W ⟶ X) (q : W ⟶ X') [IsProper p] [IsProper q] (hp : IsBirationalMorphism p)
    (hq : IsBirationalMorphism q) (hWp : IsNormalVariety k (p ≫ sX))
    (hWq : IsNormalVariety k (q ≫ sX')) [IsDominant p] [IsDominant q]
    [LocallyOfFiniteType (p ≫ sX)] [LocallyOfFiniteType (q ≫ sX')]
    (hcompat : ∀ a, functionFieldMap q a = functionFieldMap p ((σ.toHom) a)) {n : ℕ}
    {τ' : RationalPluriForms sX' n 1} (hτ' : τ' ≠ 0)
    (hK' : (divisorOfForm τ').IsCanonicalDivisor sX' n)
    (hτ : pluriformPullback sX sX' σ.toHom n 1 τ' ≠ 0)
    (hK : (divisorOfForm (pluriformPullback sX sX' σ.toHom n 1 τ')).IsCanonicalDivisor sX n)
    (hQ : (Divisor.toQDivisor (divisorOfForm (pluriformPullback sX sX' σ.toHom n 1 τ')) +
      B).IsQCartier) (hQ' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsQCartier)
    {G G' : QDivisor W}
    {hgen : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor (divisorOfForm (pluriformPullback sX sX' σ.toHom n 1 τ')) + B).supp}
    {hgen' : ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ') + B').supp}
    (hG : (Divisor.toQDivisor (divisorOfForm (pluriformPullback sX sX' σ.toHom n 1 τ')) +
      B).IsPullback p hgen G)
    (hG' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsPullback q hgen' G') : G = G' := by
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hn' : topologicalKrullDim X' = n := hK'.topologicalKrullDim_eq
  refine Finsupp.ext fun F => ?_
  have h1 := isLogDiscrepancy_of_isPullback hX p hp hWp hτ hK hQ hG F
  have h2 := isLogDiscrepancy_of_isPullback hX' q hq hWq hτ' hK' hQ' hG' F
  obtain ⟨n'', D'', hD''v, hD''⟩ := (hσ _ _).mp ⟨n, _, rfl, h1⟩
  have hv : D''.valuation = (⟨W, q, hWq, hq, F⟩ : DivisorOver k sX').valuation := by
    rw [hD''v]
    ext g
    change F.divisorialValuation (functionFieldMap p ((σ.toHom) g)) =
      F.divisorialValuation (functionFieldMap q g)
    rw [hcompat]
  have he := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD'' h2 hv
  have hord := ordForm_pullback_pluriformPullback_eq hX hX' hn hn' σ p q hp hq hWp hWq hcompat F τ'
  rw [hord] at he
  have : ((G.coeff F : ℚ) : ℝ) = ((G'.coeff F : ℚ) : ℝ) := by linarith
  exact_mod_cast this

/-- **The divisor of a nonzero rational top form on a normal variety is canonical.** -/
private theorem isCanonicalDivisor_divisorOfForm [PerfectField k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX n := by
  letI := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hn
  have hb : (b () : RationalTopForms sX n) ≠ 0 := b.ne_zero ()
  have hK := MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hX hn hb
  exact hK.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ)

/-- A separated birational morphism of finite type onto a Noetherian integral scheme is a
birational morphism in the sense of rational maps. -/
private theorem isBirationalMorphism_of_isBirational' {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsNoetherian X] (f : Y ⟶ X) [IsSeparated f] [LocallyOfFiniteType f]
    (hf : IsBirational f) : IsBirationalMorphism f := by
  haveI := hf.isDominant
  obtain ⟨V, hV, hiso⟩ := exists_isIso_restrict_of_mem_genericPoints f hf (genericPoint X)
    (Stacks.Chow.genericPoint_mem_genericPoints X)
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ V) V
    ⟨genericPoint Y, show f (genericPoint Y) ∈ V by
      rwa [MMP.Positivity.map_genericPoint_eq_of_isDominant]⟩ ⟨_, hV⟩ le_rfl ?_
  simpa [Scheme.Hom.resLE] using hiso

/-- **The strict transform of a prime divisor.** If `p : W ⟶ X` is a proper birational morphism
onto a normal Noetherian integral scheme, every prime divisor `P` of `X` is the image of a prime
divisor `Q` of `W` over which `p` is an isomorphism near `η_P`; its valuation is that of `P`. -/
private theorem exists_primeDivisor_map_genericPoint_eq {X W : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsNoetherian X] [IsNormal X] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hX : IsNormalVariety k sX) (p : W ⟶ X) [IsProper p]
    (hp : IsBirational p)
    (hW : IsNormalVariety k (p ≫ sX)) (P : Mori.PrimeDivisor X) :
    ∃ (Q : Mori.PrimeDivisor W) (U : X.Opens), p Q.genericPoint = P.genericPoint ∧
      P.genericPoint ∈ U ∧ IsIso (p ∣_ U) ∧
      haveI := hp.isDominant
      ∀ g, Q.divisorialValuation (functionFieldMap p g) = P.divisorialValuation g := by
  haveI := hp.isDominant
  haveI := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
    P.coheight_genericPoint
  obtain ⟨U, hPU, hUiso⟩ := exists_isIso_restrict_of_isDiscreteValuationRing p hp P.genericPoint
  obtain ⟨x, hx⟩ : P.genericPoint ∈ Set.range p := by
    rw [← p.isClosedMap.isClosed_range.closure_eq, p.denseRange.closure_range]; trivial
  have hxb : p x ∈ biregularLocus p := le_biregularLocus (f := p) (V := U) hUiso (hx ▸ hPU)
  have hx1 : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus p hxb, hx]
    exact P.coheight_genericPoint
  set Q : Mori.PrimeDivisor W := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1
  have hQ : MMP.Mori.PrimeDivisor.genericPoint Q = x :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hx1
  haveI : LocallyOfFiniteType p := by
    have := hW.1.toLocallyOfFiniteType
    exact locallyOfFiniteType_of_comp p sX
  let D : DivisorOver k sX := ⟨W, p, hW, isBirationalMorphism_of_isBirational' p hp, Q⟩
  have hD := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX D P
    (by change p _ = _; rw [hQ, hx])
  refine ⟨Q, U, by rw [hQ, hx], hPU, hUiso, fun g => ?_⟩
  have h := congrArg (fun w => w g) hD
  change MMP.Mori.PrimeDivisor.divisorialValuation Q (functionFieldMap p g) =
    P.divisorialValuation (functionFieldMap (𝟙 X) g) at h
  rw [h, MMP.Mori.functionFieldMap_id_apply]

/-- **The normalization of a prime divisor.** A prime divisor `Q` of a normal variety `W` has a
normalization: a normal variety `N` with a proper morphism `ν : N ⟶ W` sending the generic point
of `N` to that of `Q`, whose stalk map there is surjective. -/
private theorem exists_normalization_primeDivisor' {W : Scheme.{0}} {sW : W ⟶ Spec (.of k)}
    [IsIntegral W] (hW : IsNormalVariety k sW) (Q : Mori.PrimeDivisor W) :
    ∃ (N : Scheme.{0}) (_ : IsIntegral N) (ν : N ⟶ W), IsNormalVariety k (ν ≫ sW) ∧ IsProper ν ∧
      ν (genericPoint N) = Q.genericPoint ∧ Function.Surjective (ν.stalkMap (genericPoint N)).hom := by
  have := Q.integral
  have := hW.1
  have : AlgebraicGeometry.IsVariety k (Q.idealSheaf.subschemeι ≫ sW) :=
    (MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨hvar, hnorm, hfin, -, -⟩, -, -, -, -⟩ :=
    MMP.Threefold.normalization_spec (Q.idealSheaf.subschemeι ≫ sW)
  set Z := Q.idealSheaf.subscheme
  set hZ := MMP.finite_irreducibleComponents_of_isIntegral Z
  set ν₀ := Z.normalization hZ
  have hbir : IsBirational ν₀ := Scheme.isBirational_normalization _ _
  haveI : IsIntegral (Z.normalizationScheme hZ) := hvar.toIsIntegral
  haveI := hbir.isDominant
  have hgen : ν₀ (genericPoint _) = genericPoint Z := map_genericPoint_of_isDominant ν₀
  refine ⟨_, inferInstance, ν₀ ≫ Q.idealSheaf.subschemeι, ⟨by rwa [Category.assoc],
    hnorm⟩, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, hgen]
    rfl
  · rw [Scheme.Hom.stalkMap_comp]
    have h1 : IsIso (ν₀.stalkMap (genericPoint _)) :=
      hbir.2 _ (by rw [genericPoints_eq_singleton]; rfl)
    have hA := Q.idealSheaf.subschemeι.stalkMap_surjective (ν₀ (genericPoint _))
    have hB := (ConcreteCategory.bijective_of_isIso (ν₀.stalkMap (genericPoint _))).2
    intro z
    obtain ⟨y, rfl⟩ := hB z
    obtain ⟨w, rfl⟩ := hA y
    exact ⟨w, rfl⟩

/-- A quasi-compact morphism from a reduced scheme whose image lies in the image of a closed
immersion `ι` factors through `ι`. -/
private theorem exists_comp_eq_of_range_subset {N Y Z : Scheme.{0}} [IsReduced N] (ι : Y ⟶ Z)
    [IsClosedImmersion ι] (g : N ⟶ Z) [QuasiCompact g] (h : Set.range g ⊆ Set.range ι) :
    ∃ α : N ⟶ Y, α ≫ ι = g := by
  have H : ι.ker ≤ g.ker := Stacks.Chow.ker_le_of_support_subset_range ι g.ker (by
    rw [Scheme.Hom.support_ker]
    exact closure_minimal h ι.isClosedEmbedding.isClosed_range)
  exact ⟨IsClosedImmersion.lift ι g H, IsClosedImmersion.lift_fac _ _ _⟩

/-- **Stalk maps and function field maps.** For a dominant morphism `f : W ⟶ X` of integral
schemes, a point `y` of `W` and a specialization `z` of `f y`, restricting from `z` to `f y`,
pulling back to `y` and passing to `k(W)` is `𝒪_{X,z} → k(X) → k(W)`. -/
private theorem stalkSpecializes_stalkMap_algebraMap {W X : Scheme.{0}} [IsIntegral W]
    [IsIntegral X] (f : W ⟶ X) [IsDominant f] (y : W) (z : X) (h : f y ⤳ z) :
    X.presheaf.stalkSpecializes h ≫ f.stalkMap y ≫
        CommRingCat.ofHom (algebraMap (W.presheaf.stalk y) W.functionField) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk z) X.functionField) ≫
        CommRingCat.ofHom (functionFieldMap f) := by
  have h0 : genericPoint W ⤳ y := (genericPoint_spec W).specializes trivial
  have h1 : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  change X.presheaf.stalkSpecializes h ≫ f.stalkMap y ≫ W.presheaf.stalkSpecializes h0 =
    X.presheaf.stalkSpecializes h1 ≫ ((X.presheaf.stalkCongr (Inseparable.of_eq
      (map_genericPoint_of_isDominant f).symm)).hom ≫ f.stalkMap (genericPoint W))
  rw [← Scheme.Hom.stalkSpecializes_stalkMap, TopCat.Presheaf.stalkCongr_hom, ← Category.assoc,
    ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  congr 1
  exact (TopCat.Presheaf.stalkSpecializes_comp _ _ _).symm

/-- **Stalk maps along a lift through a closed immersion.** If `α : N ⟶ T` lifts `ν ≫ p` through
`ι : T ⟶ X`, then for a germ `a` at the generic point of `T`, pulling back along `p` and `ν` gives
`α^*(a|_T)`. -/
private theorem stalkMap_apply_eq_functionFieldMap_apply {X T W N : Scheme.{0}} [IsIntegral T]
    [IsIntegral N] (p : W ⟶ X) (ι : T ⟶ X) (ν : N ⟶ W) (α : N ⟶ T) [IsDominant α]
    (hα : α ≫ ι = ν ≫ p) (hp : p (ν (genericPoint N)) ⤳ ι (genericPoint T))
    (a : X.presheaf.stalk (ι (genericPoint T))) :
    (ν.stalkMap (genericPoint N)).hom ((p.stalkMap _).hom ((X.presheaf.stalkSpecializes hp).hom a)) =
      functionFieldMap α ((ι.stalkMap (genericPoint T)).hom a) := by
  have hα0 : α (genericPoint N) ⤳ genericPoint T := by rw [map_genericPoint_of_isDominant α]
  have hαf : functionFieldMap α = (T.presheaf.stalkSpecializes hα0 ≫ α.stalkMap _).hom := by
    unfold functionFieldMap
    rw [TopCat.Presheaf.stalkCongr_hom]
  have key : X.presheaf.stalkSpecializes hp ≫ p.stalkMap _ ≫ ν.stalkMap (genericPoint N) =
      ι.stalkMap (genericPoint T) ≫ T.presheaf.stalkSpecializes hα0 ≫
        α.stalkMap (genericPoint N) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (ι (genericPoint T)))).1
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc, ← hα,
      Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map (T.presheaf.stalkSpecializes hα0)),
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map (α.stalkMap (genericPoint N))),
      Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc]
  rw [hαf]
  exact congrArg (fun φ => φ.hom a) key

/-- **Function field maps through a common model.** Let `p : W ⟶ X`, `q : W ⟶ X'` be dominant with
`q^* = p^* ∘ σ`, let `ι : T ⟶ X`, `ι' : T' ⟶ X'` be integral closed subschemes, and `ψ` a map of
local rings at their generic points compatible with `σ`, inducing `σ_T : k(T') → k(T)`. If
`ν : N ⟶ W` sends the generic point of `N` to a point over `T` and `T'`, and `α : N ⟶ T`,
`β : N ⟶ T'` lift `ν ≫ p` and `ν ≫ q`, then `β^* = α^* ∘ σ_T`. -/
private theorem functionFieldMap_eq_comp_of_stalkMap {X X' T T' W N : Scheme.{0}} [IsIntegral X]
    [IsIntegral X'] [IsIntegral T] [IsIntegral T'] [IsIntegral W] [IsIntegral N]
    (σ : X'.functionField →+* X.functionField) (p : W ⟶ X) (q : W ⟶ X') [IsDominant p]
    [IsDominant q] (hcompat : functionFieldMap q = (functionFieldMap p).comp σ)
    (ι : T ⟶ X) (ι' : T' ⟶ X') [IsClosedImmersion ι']
    (ψ : X'.presheaf.stalk (ι' (genericPoint T')) →+* X.presheaf.stalk (ι (genericPoint T)))
    (hψ : ∀ a, algebraMap _ X.functionField (ψ a) = σ (algebraMap _ X'.functionField a))
    (σT : T'.functionField →+* T.functionField)
    (hσT : ∀ a, σT ((ι'.stalkMap (genericPoint T')).hom a) =
      (ι.stalkMap (genericPoint T)).hom (ψ a))
    (ν : N ⟶ W) (α : N ⟶ T) (β : N ⟶ T') [IsDominant α] [IsDominant β]
    (hα : α ≫ ι = ν ≫ p) (hβ : β ≫ ι' = ν ≫ q)
    (hp : p (ν (genericPoint N)) ⤳ ι (genericPoint T))
    (hq : q (ν (genericPoint N)) ⤳ ι' (genericPoint T')) :
    functionFieldMap β = (functionFieldMap α).comp σT := by
  set y := ν (genericPoint N)
  have key3 : ∀ a, (X'.presheaf.stalkSpecializes hq ≫ q.stalkMap y).hom a =
      (X.presheaf.stalkSpecializes hp ≫ p.stalkMap y).hom (ψ a) := by
    intro a
    apply IsFractionRing.injective (W.presheaf.stalk y) W.functionField
    have e1 := congrArg (fun φ => φ.hom a) (stalkSpecializes_stalkMap_algebraMap q y _ hq)
    have e2 := congrArg (fun φ => φ.hom (ψ a)) (stalkSpecializes_stalkMap_algebraMap p y _ hp)
    refine e1.trans (Eq.trans ?_ e2.symm)
    change functionFieldMap q (algebraMap _ _ a) = functionFieldMap p (algebraMap _ _ (ψ a))
    rw [hcompat, RingHom.comp_apply, hψ]
  ext b
  obtain ⟨a, rfl⟩ := ι'.stalkMap_surjective (genericPoint T') b
  rw [RingHom.comp_apply, hσT, ← stalkMap_apply_eq_functionFieldMap_apply q ι' ν β hβ hq,
    ← stalkMap_apply_eq_functionFieldMap_apply p ι ν α hα hp]
  exact congrArg (ν.stalkMap (genericPoint N)).hom (key3 a)

/-- **Birationality of a lift.** If `α : N ⟶ T` lifts `ν ≫ p` through `ι : T ⟶ X`, `p` is an
isomorphism of stalks at `ν(η_N)`, `ν(η_N)` lies over `ι(η_T)` and the stalk map of `ν` at the
generic point is surjective, then `α^* : k(T) → k(N)` is surjective. -/
private theorem surjective_functionFieldMap_of_lift {X T W N : Scheme.{0}} [IsIntegral T]
    [IsIntegral N] (p : W ⟶ X) (ι : T ⟶ X) (ν : N ⟶ W) (α : N ⟶ T) [IsDominant α]
    (hα : α ≫ ι = ν ≫ p) (hpν : p (ν (genericPoint N)) = ι (genericPoint T))
    (hiso : IsIso (p.stalkMap (ν (genericPoint N))))
    (hν : Function.Surjective (ν.stalkMap (genericPoint N)).hom) :
    Function.Surjective (functionFieldMap α) := by
  have hp : p (ν (genericPoint N)) ⤳ ι (genericPoint T) := by rw [hpν]
  have hsp : IsIso (X.presheaf.stalkSpecializes hp) := by
    have := (X.presheaf.stalkCongr (Inseparable.of_eq hpν.symm)).isIso_hom
    rw [TopCat.Presheaf.stalkCongr_hom] at this
    exact this
  intro z
  obtain ⟨w, rfl⟩ := hν z
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (p.stalkMap _)).2 w
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (X.presheaf.stalkSpecializes hp)).2 b
  exact ⟨_, (stalkMap_apply_eq_functionFieldMap_apply p ι ν α hα hp a).symm⟩

/-- `MMP.Fourfold.IsCrepantBirationalMap` for a crepant proper birational morphism
`g : V ⟶ T`, for any structure morphism `s_V = g ≫ s_T` of `V` and any `k`-isomorphism
`e : k(T) ≅ k(V)` acting as `g^*`. -/
private theorem isCrepantBirationalMap_of_isPullback_of_functionFieldEquiv [PerfectField k]
    {T V : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [LocallyOfFiniteType sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (hT : IsNormalVariety k sT) (g : V ⟶ T) [IsProper g] (hg : IsBirationalMorphism g)
    (hV : IsNormalVariety k (g ≫ sT)) [IsDominant g] [LocallyOfFiniteType (g ≫ sT)] {d : ℕ}
    {ρ : RationalPluriForms sT d 1} (hρ : ρ ≠ 0) (hK : (divisorOfForm ρ).IsCanonicalDivisor sT d)
    (hρV : pullbackRationalPluriForms sT g ρ ≠ 0)
    (hKV : (divisorOfForm (pullbackRationalPluriForms sT g ρ)).IsCanonicalDivisor (g ≫ sT) d)
    {BT : QDivisor T} {C : QDivisor V} (hq : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsQCartier)
    {hgen : ∀ Z : irreducibleComponents V,
      g (componentGenericPoint V Z) ∉ (Divisor.toQDivisor (divisorOfForm ρ) + BT).supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm ρ) + BT).IsPullback g hgen
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sT g ρ)) + C))
    {sV : V ⟶ Spec (.of k)} (hsV : g ≫ sT = sV) (e : FunctionFieldEquiv sV sT)
    (he : ∀ a, e a = functionFieldMap g a) :
    IsCrepantBirationalMap sV sT C BT e := by
  subst hsV
  have : e = functionFieldAlgEquiv sT g hg.functionFieldMap_bijective := by
    letI := functionFieldAlgebra sT
    letI := functionFieldAlgebra (g ≫ sT)
    exact AlgEquiv.ext he
  subst this
  exact isCrepantBirationalMap_of_isPullback hT g hg hV hρ hK hρV hKV hq hpb

/-- A normal integral scheme proper over a normal variety is a normal variety. -/
private theorem isNormalVariety_comp_of_isProper {X Y : Scheme.{0}} [IsIntegral Y] [IsNormal Y]
    {s : X ⟶ Spec (.of k)} (hs : IsNormalVariety k s) (f : Y ⟶ X) [IsProper f] :
    IsNormalVariety k (f ≫ s) := by
  obtain ⟨-, h1, h2, h3⟩ := (MMP.Mori.isVariety_iff k s).mp hs.1
  exact ⟨(MMP.Mori.isVariety_iff k (f ≫ s)).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

/-- **Crepancy between points.** A normal variety of dimension zero carries no divisors over it,
so every isomorphism of function fields of two such varieties is crepant. -/
private theorem isCrepantBirationalMap_of_topologicalKrullDim_eq_zero {T T' : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} {sT' : T' ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] [IsIntegral T'] [IsLocallyNoetherian T'] [IsNormal T']
    (hT : topologicalKrullDim T = 0) (hT' : topologicalKrullDim T' = 0) (B : QDivisor T)
    (B' : QDivisor T') (σ : FunctionFieldEquiv sT sT') :
    IsCrepantBirationalMap sT sT' B B' σ := by
  have key : ∀ {S : Scheme.{0}} {s : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S]
      [IsNormal S], topologicalKrullDim S = 0 → ∀ (C : QDivisor S) v a,
      ¬ HasLogDiscrepancy s C v a := by
    intro S s _ _ _ hS C v a h
    obtain ⟨n, D, -, hD⟩ := h
    obtain ⟨hSv, -⟩ := hD
    have := D.isIntegral
    haveI := hSv.1
    haveI := D.isNormalVariety.1
    have hY : topologicalKrullDim D.Y = 0 :=
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism s (D.f ≫ s)
        D.isBirationalMorphism).symm.trans hS
    have h1 := AlgebraicGeometry.coheight_le_topologicalKrullDim D.E.genericPoint
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hY] at h1
    exact absurd h1 (by decide)
  intro v a
  exact ⟨fun h => absurd h (key hT B v a), fun h => absurd h (key hT' B' _ a)⟩

/-- A birational morphism `g : V ⟶ T` gives a `k`-isomorphism `k(T) ≅ k(V)` acting as `g^*` for
every structure morphism `s_V = g ≫ s_T` of `V`. -/
private theorem exists_functionFieldEquiv_of_comp_eq {V T : Scheme.{0}} [IsIntegral V]
    [IsIntegral T] {sT : T ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} (g : V ⟶ T) [IsDominant g]
    (hg : Function.Bijective (functionFieldMap g)) (h : g ≫ sT = sV) :
    ∃ e : FunctionFieldEquiv sV sT, ∀ a, e a = functionFieldMap g a := by
  subst h
  exact ⟨functionFieldAlgEquiv sT g hg, fun _ => rfl⟩

/-- The generic point of a prime divisor along which a `ℚ`-divisor has coefficient zero is not in
its support. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {Y : Scheme.{0}} {D : QDivisor Y}
    {P : Mori.PrimeDivisor Y} (h : D.coeff P = 0) : P.genericPoint ∉ D.supp := by
  intro hm
  obtain ⟨E, hE, hPE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hm
  obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPE
  exact hE h

/-- The pull-back predicate only depends on the morphism, not on how it is written. -/
private theorem isPullback_of_hom_eq {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f g : X ⟶ Y} (h : f = g) {D : QDivisor Y}
    {hf : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp}
    {hg : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ D.supp} {D' : QDivisor X}
    (H : D.IsPullback f hf D') : D.IsPullback g hg D' := by
  subst h
  exact H

/-- The pull-back predicate only depends on the divisor pulled back. -/
private theorem isPullback_of_eq_source {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {D₁ D₂ : QDivisor Y} (h : D₁ = D₂)
    {h₁ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D₁.supp}
    {h₂ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D₂.supp} {D' : QDivisor X}
    (H : D₁.IsPullback f h₁ D') : D₂.IsPullback f h₂ D' := by
  subst h
  exact H

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_of_isPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {D : QDivisor Y} (hD : D.IsQCartier)
    {hf : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp} {D' : QDivisor X}
    (H : D.IsPullback f hf D') : D'.IsQCartier := by
  obtain ⟨C, hC, hCc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hD
  obtain ⟨C', hC', hpb⟩ := H _ (QDivisor.cartierIndex_pos hD) C hC hCc
  exact ⟨_, by exact_mod_cast (QDivisor.cartierIndex_pos hD).ne', C', hC', hpb.isCartier hCc⟩

/-- Pull-backs of `ℚ`-divisors compose. -/
private theorem qDivisor_isPullback_comp' {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian Z] [IsNormal Z] (p : Y ⟶ X) (q : Z ⟶ Y) {M : QDivisor X}
    {MY : QDivisor Y} {MZ : QDivisor Z}
    {hM : ∀ C : irreducibleComponents Y, p (componentGenericPoint Y C) ∉ M.supp}
    {hMY : ∀ C : irreducibleComponents Z, q (componentGenericPoint Z C) ∉ MY.supp}
    (h₁ : M.IsPullback p hM MY) (h₂ : MY.IsPullback q hMY MZ)
    (hM' : ∀ C : irreducibleComponents Z, (q ≫ p) (componentGenericPoint Z C) ∉ M.supp) :
    M.IsPullback (q ≫ p) hM' MZ := fun m hm D hD hDc => by
  obtain ⟨D', hD', hpb⟩ := h₁ m hm D hD hDc
  obtain ⟨D'', hD'', hpb'⟩ := h₂ m hm D' hD' (hpb.isCartier hDc)
  exact ⟨D'', hD'', MMP.ProgramBaseChange.divisor_isPullback_comp rfl hpb hpb' _⟩

/-- A morphism out of an irreducible scheme whose generic point maps to the generic point of a
prime divisor `P_f` lands in the image of any closed immersion onto `P_f`. -/
private theorem range_comp_subset_of_map_genericPoint {N W Y Z : Scheme.{0}} [IrreducibleSpace N]
    (ν : N ⟶ W) (f : W ⟶ Y) (ιf : Z ⟶ Y) (Pf : Mori.PrimeDivisor Y)
    (hr : Set.range ιf.base = (Pf.support : Set Y))
    (h : f (ν (genericPoint N)) = Pf.genericPoint) :
    Set.range (ν ≫ f).base ⊆ Set.range ιf.base := by
  rintro _ ⟨z, rfl⟩
  rw [hr, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have hz : genericPoint N ⤳ z := (genericPoint_spec N).specializes trivial
  have h2 := hz.map (ν ≫ f).base.hom.continuous
  change (ν ≫ f) (genericPoint N) ⤳ (ν ≫ f) z at h2
  rw [Scheme.Hom.comp_apply, h] at h2
  exact specializes_iff_mem_closure.mp h2

/-- **Crepant maps induce crepant maps on floor divisors.** Let `σ : (X, B) ⇢ (X', B')` be a
crepant birational map of normal varieties proper over `k`, and `T ⊂ X`, `T' ⊂ X'` normal floor
divisors with their differents `B_T`, `B_{T'}`, such that `σ` identifies the local rings
`𝒪_{X',T'} ≅ 𝒪_{X,T}` and so induces `σ_T : k(T') ≅ k(T)`. Then `σ_T` is a crepant birational map
`(T, B_T) ⇢ (T', B_{T'})`: on the normalization `N` of the strict transform of `T` on a common
model `W`, both adjunction pairs pull back to the restriction of the common pull-back
`p^*(K_X + B) = q^*(K_{X'} + B')`. -/
private theorem isCrepantBirationalMap_of_isAdjunctionStep [IsAlgClosed k] [CharZero k]
    {X X' T T' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsProper sX] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [LocallyOfFiniteType sX'] [IsProper sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') {n : ℕ}
    (hn : topologicalKrullDim X = (n + 1 : ℕ)) (hn' : topologicalKrullDim X' = (n + 1 : ℕ))
    {B : QDivisor X} {B' : QDivisor X'} {K : Divisor X} {K' : Divisor X'}
    (hK : K.IsCanonicalDivisor sX (n + 1)) (hK' : K'.IsCanonicalDivisor sX' (n + 1))
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) (hKB' : (Divisor.toQDivisor K' + B').IsQCartier)
    (σ : FunctionFieldEquiv sX sX') (hσ : IsCrepantBirationalMap sX sX' B B' σ)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsIntegral T'] [IsLocallyNoetherian T'] [IsNormal T'] [CompactSpace T']
    {ι : T ⟶ X} {ι' : T' ⟶ X'} [IsClosedImmersion ι] [IsClosedImmersion ι']
    {BT : QDivisor T} {BT' : QDivisor T'}
    (hι : IsAdjunctionStep sX B ι BT) (hι' : IsAdjunctionStep sX' B' ι' BT')
    (P : Mori.PrimeDivisor X) (P' : Mori.PrimeDivisor X')
    (hrP : Set.range ι.base = (P.support : Set X)) (hrP' : Set.range ι'.base = (P'.support : Set X'))
    (hP' : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g))
    (ψ : X'.presheaf.stalk (ι' (genericPoint T')) →+* X.presheaf.stalk (ι (genericPoint T)))
    (hψ : ∀ a, algebraMap _ X.functionField (ψ a) = (σ.toHom) (algebraMap _ X'.functionField a))
    (hord : ∀ a, X.ord (algebraMap _ X.functionField (ψ a)) (ι (genericPoint T)) =
      X'.ord (algebraMap _ X'.functionField a) (ι' (genericPoint T')))
    (σT : FunctionFieldEquiv (ι ≫ sX) (ι' ≫ sX'))
    (hσT : ∀ a, (σT.toHom) ((ι'.stalkMap (genericPoint T')).hom a) =
      (ι.stalkMap (genericPoint T)).hom (ψ a)) :
    IsCrepantBirationalMap (ι ≫ sX) (ι' ≫ sX') BT BT' σT := by
  have hT := hι.1
  have hT' := hι'.1
  haveI : LocallyOfFiniteType (ι ≫ sX) := hT.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι' ≫ sX') := hT'.1.toLocallyOfFiniteType
  have hdT : topologicalKrullDim T = n := topologicalKrullDim_eq_of_range_eq_support sX ι P hrP hn
  have hdT' : topologicalKrullDim T' = n :=
    topologicalKrullDim_eq_of_range_eq_support sX' ι' P' hrP' hn'
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · exact isCrepantBirationalMap_of_topologicalKrullDim_eq_zero (by exact_mod_cast hdT)
      (by exact_mod_cast hdT') BT BT' σT
  obtain ⟨Q'⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdT' hnpos.ne'
  -- a form `τ'` with a simple pole along `T'` and its residue `ρ'`
  obtain ⟨τ', hτ'0, hτ'P, -, ρ', hρ', hρ'0, -⟩ :=
    MMP.Fourfold.exists_form_of_residue_order sX' hX' (by exact_mod_cast hn') ι' hT'
      P' hrP' Q'
  -- its transport `τ = σ^*τ'`, with residue `ρ = σ_T^*ρ'`
  set τ := pluriformPullback sX sX' σ.toHom (n + 1) 1 τ' with hτdef
  set ρ := pluriformPullback (ι ≫ sX) (ι' ≫ sX') σT.toHom n 1 ρ' with hρdef
  have hρres : IsPoincareResidue sX ι n 1 τ ρ :=
    isPoincareResidue_pluriformPullback ι ι' hn hn' hdT hdT' σ.toHom σT.toHom ψ hψ
      (fun a => (hσT a).symm) hord hρ'
  have hτP : P.ordForm τ = -1 := by
    have hv : ∀ g, (DivisorOver.ofPrimeDivisor k hX' P').valuation g =
        P.divisorialValuation ((σ.toHom) g) := by
      intro g
      change P'.divisorialValuation (functionFieldMap (𝟙 X') g) = _
      rw [MMP.Mori.functionFieldMap_id_apply, hP']
    rw [hτdef, ordForm_pluriformPullback_eq_ordPullback hX hX' hn hn' σ P _ hv τ',
      DivisorOver.ordPullback_ofPrimeDivisor hX' hn' P' τ', hτ'P]
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, Mori.PrimeDivisor.ordForm_zero] at hτP
    exact absurd hτP (by decide)
  have hD : (Divisor.toQDivisor (divisorOfForm τ) + B).IsQCartier :=
    hKB.add_of_linearlyEquivalent (by
      simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ0).symm)
  have hD' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsQCartier :=
    hKB'.add_of_linearlyEquivalent (by
      simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX' hK' hτ'0).symm)
  -- adjunction on both sides
  obtain ⟨hgenT, hpbT⟩ := hι.isPullback_divisorOfForm_add_of_isPoincareResidue
    (by exact_mod_cast hn) P hrP τ hτ0 hτP ρ hρres hD
  obtain ⟨hgenT', hpbT'⟩ := hι'.isPullback_divisorOfForm_add_of_isPoincareResidue
    (by exact_mod_cast hn') P' hrP' τ' hτ'0 hτ'P ρ' hρ' hD'
  -- a common model `W` and the common pull-back `G = G'`
  obtain ⟨W, _, _, p, q, _, _, hpP, hqP, hpb, hqb, hpq, hcompat⟩ :=
    exists_model_of_functionFieldEquiv σ
  have hWp : IsNormalVariety k (p ≫ sX) := isNormalVariety_comp_of_isProper hX p
  have hWq : IsNormalVariety k (q ≫ sX') := isNormalVariety_comp_of_isProper hX' q
  haveI : LocallyOfFiniteType (p ≫ sX) := hWp.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sX') := hWq.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace W := by
    have := hWp.1
    exact QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : IsNoetherian X := {}
  haveI : IsNoetherian X' := {}
  have hpB : IsBirationalMorphism p := isBirationalMorphism_of_isBirational' p hpb
  have hqB : IsBirationalMorphism q := isBirationalMorphism_of_isBirational' q hqb
  have hcompat' : ∀ a, functionFieldMap q a = functionFieldMap p ((σ.toHom) a) := fun a => by
    rw [hcompat]
    rfl
  have hgenG := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p
    (Divisor.toQDivisor (divisorOfForm τ) + B)
  have hgenG' := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q
    (Divisor.toQDivisor (divisorOfForm τ') + B')
  set G := QDivisor.pullback _ hD hgenG
  have hG := QDivisor.isPullback_pullback hD hgenG
  have hG' := QDivisor.isPullback_pullback hD' hgenG'
  have hGG' := pullback_eq_pullback_of_isCrepantBirationalMap hX hX' σ hσ p q hpB hqB hWp hWq
    hcompat' hτ'0 (isCanonicalDivisor_divisorOfForm hX' hn' hτ'0) hτ0
    (isCanonicalDivisor_divisorOfForm hX hn hτ0) hD hD' hG hG'
  -- the strict transform `Q` of `T` on `W`, over both `T` and `T'`
  obtain ⟨Q, U, hQP, hPU, hUiso, hQv⟩ := exists_primeDivisor_map_genericPoint_eq hX p hpb hWp P
  have hqQ : q Q.genericPoint = P'.genericPoint := by
    let D1 : DivisorOver k sX' := ⟨W, q, hWq, hqB, Q⟩
    have hv : D1.valuation = (DivisorOver.ofPrimeDivisor k hX' P').valuation := by
      ext g
      change Q.divisorialValuation (functionFieldMap q g) =
        P'.divisorialValuation (functionFieldMap (𝟙 X') g)
      rw [MMP.Mori.functionFieldMap_id_apply, hcompat', hQv, hP']
    exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX'.1 hv
  -- the normalization `ν : N ⟶ W` of `Q` and the lifts `α : N ⟶ T`, `β : N ⟶ T'`
  obtain ⟨N, _, ν, hNv, hνP, hνη, hνsurj⟩ := exists_normalization_primeDivisor' hWp Q
  haveI := hνP
  haveI : IsNormal N := hNv.2
  have hιη := map_genericPoint_eq_of_range_eq ι P hrP
  have hι'η := map_genericPoint_eq_of_range_eq ι' P' hrP'
  have hpν : p (ν (genericPoint N)) = ι (genericPoint T) := by rw [hνη, hQP, hιη]
  have hqν : q (ν (genericPoint N)) = ι' (genericPoint T') := by rw [hνη, hqQ, hι'η]
  obtain ⟨α, hα⟩ := exists_comp_eq_of_range_subset ι (ν ≫ p)
    (range_comp_subset_of_map_genericPoint ν p ι P hrP (by rw [hpν, hιη]))
  obtain ⟨β, hβ⟩ := exists_comp_eq_of_range_subset ι' (ν ≫ q)
    (range_comp_subset_of_map_genericPoint ν q ι' P' hrP' (by rw [hqν, hι'η]))
  have hαη : α (genericPoint N) = genericPoint T := ι.isClosedEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hα, Scheme.Hom.comp_apply, hpν])
  have hβη : β (genericPoint N) = genericPoint T' := ι'.isClosedEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hβ, Scheme.Hom.comp_apply, hqν])
  haveI : IsDominant α := ⟨Dense.mono (s₁ := {genericPoint T})
    (Set.singleton_subset_iff.mpr ⟨_, hαη⟩) (dense_iff_closure_eq.mpr (genericPoint_spec T))⟩
  haveI : IsDominant β := ⟨Dense.mono (s₁ := {genericPoint T'})
    (Set.singleton_subset_iff.mpr ⟨_, hβη⟩) (dense_iff_closure_eq.mpr (genericPoint_spec T'))⟩
  -- `β^* = α^* ∘ σ_T`, and `α`, `β` are birational
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra (ι ≫ sX)
  letI := functionFieldAlgebra (ι' ≫ sX')
  have hαβ : functionFieldMap β = (functionFieldMap α).comp (σT.toHom).toRingHom :=
    functionFieldMap_eq_comp_of_stalkMap (σ.toHom).toRingHom p q hcompat ι ι' ψ hψ
      (σT.toHom).toRingHom hσT ν α β hα hβ (by rw [hpν]) (by rw [hqν])
  haveI : IsNoetherian T := {}
  haveI : IsNoetherian T' := {}
  have hpiso : IsIso (p.stalkMap (ν (genericPoint N))) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus p
      (le_biregularLocus (f := p) (V := U) hUiso (by rwa [hpν, hιη]))
  have hαs := surjective_functionFieldMap_of_lift p ι ν α hα hpν hpiso hνsurj
  have hαbij : Function.Bijective (functionFieldMap α) := ⟨(functionFieldMap α).injective, hαs⟩
  have hβbij : Function.Bijective (functionFieldMap β) := by
    rw [hαβ]
    exact hαbij.comp σT.bijective
  haveI : IsProper α := by
    have : IsProper (α ≫ ι) := by rw [hα]; infer_instance
    exact IsProper.of_comp α ι
  haveI : IsProper β := by
    have : IsProper (β ≫ ι') := by rw [hβ]; infer_instance
    exact IsProper.of_comp β ι'
  have hαB : IsBirationalMorphism α :=
    isBirationalMorphism_of_isBirational' α (isBirational_of_surjective_functionFieldMap α hαs)
  have hβB : IsBirationalMorphism β :=
    isBirationalMorphism_of_isBirational' β (isBirational_of_surjective_functionFieldMap β hβbij.2)
  -- `N` as a normal variety over `k`
  have hsN : α ≫ ι ≫ sX = ν ≫ p ≫ sX := by rw [← Category.assoc, hα, Category.assoc]
  have hsβ : β ≫ ι' ≫ sX' = α ≫ ι ≫ sX := by
    rw [← Category.assoc, hβ, Category.assoc, ← hpq, hsN]
  have hNα : IsNormalVariety k (α ≫ ι ≫ sX) := hsN ▸ hNv
  have hNβ : IsNormalVariety k (β ≫ ι' ≫ sX') := hsβ ▸ hNα
  haveI : LocallyOfFiniteType (α ≫ ι ≫ sX) := hNα.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (β ≫ ι' ≫ sX') := hNβ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian (α ≫ ι ≫ sX)
  haveI : CompactSpace N := by
    have := hNα.1
    exact QuasiCompact.compactSpace_of_compactSpace (α ≫ ι ≫ sX)
  -- the common pull-back `G` vanishes along `Q`
  have hBP := hι.coeff_eq_one hrP
  have hDP : (Divisor.toQDivisor (divisorOfForm τ) + B).coeff P = 0 := by
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτP, hBP]
    norm_num
  have hGQ : G.coeff Q = 0 := by
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy
      (⟨hX, n + 1, K, hK, hKB⟩ : Mori.IsPair sX B) (isCanonicalDivisor_divisorOfForm hX hn hτ0)
      (DivisorOver.ofPrimeDivisor k hX P)
    have hc' : c = -B.coeff P := hc.eq_neg_coeff_of_ofPrimeDivisor hX
    have hlogP := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (show IsProper (𝟙 X) by infer_instance)
    have hlogQ := isLogDiscrepancy_of_isPullback hX p hpB hWp hτ0
      (isCanonicalDivisor_divisorOfForm hX hn hτ0) hD hG Q
    have hval : (⟨W, p, hWp, hpB, Q⟩ : DivisorOver k sX).valuation =
        (DivisorOver.ofPrimeDivisor k hX P).valuation := by
      ext g
      change Q.divisorialValuation (functionFieldMap p g) =
        P.divisorialValuation (functionFieldMap (𝟙 X) g)
      rw [MMP.Mori.functionFieldMap_id_apply, hQv]
    have he := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlogQ hlogP hval
    haveI : IsIso (p.stalkMap Q.genericPoint) := by rwa [← hνη]
    have hordQ : Q.ordForm (pullbackRationalPluriForms sX p τ) = P.ordForm τ :=
      MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hpB.functionFieldMap_bijective
        (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) Q P hQP τ
    rw [hordQ, hτP, hc', hBP] at he
    have : ((G.coeff Q : ℚ) : ℝ) = 0 := by push_cast at he ⊢; linarith
    exact_mod_cast this
  -- `H = (ν ≫ p)^*(div τ + B)`, computed through `T` and through `W`
  have hgenH : ∀ Z : irreducibleComponents N,
      (ν ≫ p) (componentGenericPoint N Z) ∉ (Divisor.toQDivisor (divisorOfForm τ) + B).supp := by
    intro Z
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hpν, hιη]
    exact genericPoint_notMem_supp_of_coeff_eq_zero hDP
  have hH := QDivisor.isPullback_pullback hD hgenH
  set H := QDivisor.pullback _ hD hgenH
  have hqT := isQCartier_of_isPullback hD hpbT
  have hqT' := isQCartier_of_isPullback hD' hpbT'
  have hgenα := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' α
    (Divisor.toQDivisor (divisorOfForm ρ) + BT)
  have hgenβ := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' β
    (Divisor.toQDivisor (divisorOfForm ρ') + BT')
  have hEα := QDivisor.isPullback_pullback hqT hgenα
  have hEβ := QDivisor.isPullback_pullback hqT' hgenβ
  have hHα : H = QDivisor.pullback _ hqT hgenα :=
    (QDivisor.IsQCartier.existsUnique_isPullback hD hgenH).unique hH
      (isPullback_of_hom_eq hα (qDivisor_isPullback_comp' ι α hpbT hEα (by rwa [hα])))
  have hgenν : ∀ Z : irreducibleComponents N, ν (componentGenericPoint N Z) ∉ G.supp := by
    intro Z
    rw [componentGenericPoint_eq_genericPoint, hνη]
    exact genericPoint_notMem_supp_of_coeff_eq_zero hGQ
  have hqG := isQCartier_of_isPullback hD hG
  have hHν := QDivisor.isPullback_pullback hqG hgenν
  have hHHν : H = QDivisor.pullback _ hqG hgenν :=
    (QDivisor.IsQCartier.existsUnique_isPullback hD hgenH).unique hH
      (qDivisor_isPullback_comp' p ν hG hHν hgenH)
  have hgenν' : ∀ Z : irreducibleComponents N,
      ν (componentGenericPoint N Z) ∉ (QDivisor.pullback _ hD' hgenG').supp := by
    rwa [← hGG']
  have hgenH' : ∀ Z : irreducibleComponents N,
      (ν ≫ q) (componentGenericPoint N Z) ∉ (Divisor.toQDivisor (divisorOfForm τ') + B').supp := by
    intro Z
    rw [componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply, hqν, hι'η]
    have hBP' := hι'.coeff_eq_one hrP'
    refine genericPoint_notMem_supp_of_coeff_eq_zero ?_
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτ'P, hBP']
    norm_num
  have hH' : (Divisor.toQDivisor (divisorOfForm τ') + B').IsPullback (ν ≫ q) hgenH' H := by
    rw [hHHν]
    exact qDivisor_isPullback_comp' q ν hG' (isPullback_of_eq_source (h₂ := hgenν') hGG' hHν)
      hgenH'
  have hHβ : H = QDivisor.pullback _ hqT' hgenβ :=
    (QDivisor.IsQCartier.existsUnique_isPullback hD' hgenH').unique hH'
      (isPullback_of_hom_eq hβ (qDivisor_isPullback_comp' ι' β hpbT' hEβ
        (by rwa [hβ])))
  -- the forms `α^*ρ` and `β^*ρ'` on `N` have the same divisor
  have hcompatN : ∀ a, functionFieldMap β a = functionFieldMap α ((σT.toHom) a) := fun a => by
    rw [hαβ]
    rfl
  have hρ0 : ρ ≠ 0 := by
    intro h0
    apply hρ'0
    have e := pluriformPullback_comp (sX := ι' ≫ sX') (sX' := ι ≫ sX) (sX'' := ι' ≫ sX') hdT' hdT
      hdT' 1 (FunctionFieldEquiv.toHom (ι' ≫ sX') (ι ≫ sX) σT.symm) σT.toHom ρ'
    have h1 : (FunctionFieldEquiv.toHom (ι' ≫ sX') (ι ≫ sX) σT.symm).comp σT.toHom =
        FunctionFieldEquiv.toHom (ι' ≫ sX') (ι' ≫ sX') 1 := by
      ext a
      exact σT.symm_apply_apply a
    rw [← hρdef, h0, map_zero, h1, pluriformPullback_one hdT'] at e
    exact e.symm
  haveI := hT.1
  haveI := hT'.1
  haveI := hNα.1
  haveI := hNβ.1
  have hdN : topologicalKrullDim N = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι ≫ sX) (α ≫ ι ≫ sX)
      hαB).symm.trans hdT
  have hdNβ : topologicalKrullDim N = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι' ≫ sX') (β ≫ ι' ≫ sX')
      hβB).symm.trans hdT'
  have hρα0 : pullbackRationalPluriForms (ι ≫ sX) α ρ ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' α hαbij
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ι ≫ sX) hdT) hρ0
  have hρβ0 : pullbackRationalPluriForms (ι' ≫ sX') β ρ' ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' β hβbij
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ι' ≫ sX') hdT') hρ'0
  have hdivαβ : divisorOfForm (pullbackRationalPluriForms (ι ≫ sX) α ρ) =
      divisorOfForm (pullbackRationalPluriForms (ι' ≫ sX') β ρ') := by
    refine Finsupp.ext fun F => ?_
    change (divisorOfForm _).coeff F = (divisorOfForm _).coeff F
    rw [coeff_divisorOfForm, coeff_divisorOfForm, hρdef]
    exact ordForm_pullback_pluriformPullback_eq hT hT' hdT hdT' σT α β hαB hβB hNα hNβ hcompatN F ρ'
  -- the crepant boundary `C` on `N`, and crepancy of `N ⟶ T` and of `N ⟶ T'`
  set C : QDivisor N := H - Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms (ι ≫ sX) α ρ))
  have hCα : Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms (ι ≫ sX) α ρ)) + C = H :=
    add_sub_cancel _ _
  have hCβ : Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms (ι' ≫ sX') β ρ')) + C =
      H := by
    rw [← hdivαβ]
    exact hCα
  obtain ⟨eα, heα⟩ := exists_functionFieldEquiv_of_comp_eq (sT := ι ≫ sX) α hαbij rfl
  obtain ⟨eβ, heβ⟩ := exists_functionFieldEquiv_of_comp_eq (sT := ι' ≫ sX') β hβbij hsβ
  have crepA : IsCrepantBirationalMap (α ≫ ι ≫ sX) (ι ≫ sX) C BT eα :=
    isCrepantBirationalMap_of_isPullback_of_functionFieldEquiv hT α hαB hNα hρ0
      (isCanonicalDivisor_divisorOfForm hT hdT hρ0) hρα0 (isCanonicalDivisor_divisorOfForm hNα hdN hρα0) hqT (by rwa [hCα, hHα]) rfl eα
      heα
  have crepB : IsCrepantBirationalMap (α ≫ ι ≫ sX) (ι' ≫ sX') C BT' eβ :=
    isCrepantBirationalMap_of_isPullback_of_functionFieldEquiv hT' β hβB hNβ hρ'0
      (isCanonicalDivisor_divisorOfForm hT' hdT' hρ'0) hρβ0
      (isCanonicalDivisor_divisorOfForm hNβ hdNβ hρβ0) hqT' (by rwa [hCβ, hHβ]) hsβ eβ heβ
  letI := functionFieldAlgebra (α ≫ ι ≫ sX)
  have hσT' : eβ.trans eα.symm = σT := by
    ext a
    change eα.symm (eβ a) = σT a
    rw [AlgEquiv.symm_apply_eq, heα, heβ, hcompatN]
    rfl
  rw [← hσT']
  exact crepA.symm.trans crepB

end CrepantModel

/-! ### Floor models and single adjunction steps -/

/-- Two reduced closed subschemes with the same underlying set are isomorphic over the ambient
scheme. -/
private theorem exists_iso_comp_eq_of_range_eq {T₁ T₂ Z : Scheme.{0}} [IsReduced T₁]
    [IsReduced T₂] (i₁ : T₁ ⟶ Z) (i₂ : T₂ ⟶ Z) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h : Set.range i₁.base = Set.range i₂.base) : ∃ ψ : T₁ ≅ T₂, ψ.hom ≫ i₂ = i₁ := by
  obtain ⟨α, hα⟩ := exists_comp_eq_of_range_subset i₂ i₁ h.le
  obtain ⟨β, hβ⟩ := exists_comp_eq_of_range_subset i₁ i₂ h.ge
  refine ⟨⟨α, β, ?_, ?_⟩, hα⟩
  · rw [← cancel_mono i₁, Category.assoc, hβ, hα, Category.id_comp]
  · rw [← cancel_mono i₂, Category.assoc, hα, hβ, Category.id_comp]

/-- **An adjunction step onto a floor component.** On a dlt pair `(Y, B_Y)` of dimension `d + 1`
over `ℂ`, every prime divisor `Q` with `coeff_Q B_Y ≥ 1` is the image of an adjunction step
`T ⟶ Y` with its different `B_T`, and `(T, B_T)` is dlt. -/
private theorem exists_isAdjunctionStep_of_one_le_coeff {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY]
    {BY : QDivisor Y} (hdlt : MMP.Intersection.IsDltPair sY BY) {d : ℕ}
    (hd : topologicalKrullDim Y = (d + 1 : ℕ)) (Q : Mori.PrimeDivisor Y)
    (hQ : 1 ≤ BY.coeff Q) :
    ∃ (T : Scheme.{0}) (jT : T ⟶ Y) (BT : QDivisor T) (hj : IsAdjunctionStep sY BY jT BT),
      Set.range jT.base = (Q.support : Set Y) ∧
        haveI : IsIntegral T := hj.1.1.toIsIntegral
        haveI : IsNormal T := hj.1.2
        haveI : IsLocallyNoetherian T := by
          have := hj.1.1
          exact LocallyOfFiniteType.isLocallyNoetherian (jT ≫ sY)
        MMP.Intersection.IsDltPair (jT ≫ sY) BT := by
  have hinter : (⋂ P ∈ ({Q} : Finset (Mori.PrimeDivisor Y)), (P.support : Set Y)) =
      Q.support := by simp
  have hS : IsDltStratum sY BY (Q.support : Set Y) := by
    refine ⟨hdlt, {Q}, Finset.singleton_nonempty _, by simpa using hQ, ?_, ?_⟩
    · rw [hinter]
      exact ⟨Q.genericPoint, by
        rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
    · rw [hinter]
      refine ⟨⟨?_, le_rfl⟩, fun T hT _ => hT.2⟩
      rw [PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
  obtain ⟨⟨⟨T, ι, BT, hrange, ⟨F⟩⟩, hdltF⟩, -⟩ := hS.exists_isStratumAdjunctionPair_and_isDltPair
  have hdltT := hdltF F hrange
  cases F with
  | refl h =>
    exfalso
    have h1 : genericPoint Y ∈ Set.range (𝟙 Y : Y ⟶ Y).base := ⟨_, rfl⟩
    rw [hrange] at h1
    exact MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support Q h1
  | @step S T ι₀ BS F₀ jT BT hj =>
    cases F₀ with
    | refl h =>
      have hj' : IsAdjunctionStep sY BY jT BT := by
        simpa only [Category.id_comp] using hj
      refine ⟨T, jT, BT, hj', by simpa using hrange, ?_⟩
      simpa only [Category.comp_id] using hdltT
    | step F₁ j₁ BT₁ hj₁ =>
      exfalso
      haveI : IsIntegral T := hj.1.1.toIsIntegral
      haveI := (StratumAdjunctionData.step (.step F₁ j₁ BS hj₁) jT BT hj).isClosedImmersion
      have hdT : topologicalKrullDim T = d :=
        topologicalKrullDim_eq_of_range_eq_support sY _ Q hrange hd
      have hlen := StratumAdjunctionData.dim_add_length (sX := sY) hd
        (StratumAdjunctionData.step (.step F₁ j₁ BS hj₁) jT BT hj) hdT
      simp only [StratumAdjunctionData.length] at hlen
      omega

/-- An isomorphism of integral schemes induces a bijection of function fields. -/
private theorem functionFieldMap_bijective_of_isIso {A A' : Scheme.{0}} [IsIntegral A]
    [IsIntegral A'] (e : A ≅ A') : Function.Bijective (functionFieldMap e.hom) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨functionFieldMap e.inv, fun t => ?_, fun t => ?_⟩
  · rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr (Iso.inv_hom_id e), functionFieldMap_id_apply]
  · rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr (Iso.hom_inv_id e), functionFieldMap_id_apply]

/-- **A crepant birational map matching two prime divisors matches their coefficients.** -/
private theorem coeff_eq_of_isCrepantBirationalMap {Y Y' : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    {sY : Y ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)} {BY : QDivisor Y} {BY' : QDivisor Y'}
    (hP : MMP.Mori.IsPair sY BY) (hP' : MMP.Mori.IsPair sY' BY') {d d' : ℕ} {K : Divisor Y}
    {K' : Divisor Y'} (hK : K.IsCanonicalDivisor sY d) (hK' : K'.IsCanonicalDivisor sY' d')
    (σ : FunctionFieldEquiv sY sY') (hσ : IsCrepantBirationalMap sY sY' BY BY' σ)
    (P : Mori.PrimeDivisor Y) (P' : Mori.PrimeDivisor Y')
    (hPP : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g)) :
    BY'.coeff P' = BY.coeff P := by
  have hX := hP.isNormalVariety
  have hXj := hP'.isNormalVariety
  set DΓ := DivisorOver.ofPrimeDivisor ℂ hX P
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK DΓ
  have hc' : c = -BY.coeff P := hc.eq_neg_coeff_of_ofPrimeDivisor hX
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 Y) by infer_instance)
  obtain ⟨n', D, hDv, hDlog⟩ := (hσ DΓ.valuation (1 + c)).mp ⟨d, DΓ, rfl, hlog⟩
  set DΓ' := DivisorOver.ofPrimeDivisor ℂ hXj P'
  obtain ⟨c₂, hc₂⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP' hK' DΓ'
  have hc₂' : c₂ = -BY'.coeff P' := hc₂.eq_neg_coeff_of_ofPrimeDivisor hXj
  have hlog' := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc₂
    (show IsProper (𝟙 Y') by infer_instance)
  have hv : D.valuation = DΓ'.valuation := by
    ext g
    rw [hDv]
    change P.divisorialValuation (functionFieldMap (𝟙 Y) _) =
      P'.divisorialValuation (functionFieldMap (𝟙 Y') g)
    rw [functionFieldMap_id_apply, functionFieldMap_id_apply, hPP]
    rfl
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hDlog hlog' hv
  have h2 : ((c : ℚ) : ℝ) = ((c₂ : ℚ) : ℝ) := by linarith
  have h3 : c = c₂ := by exact_mod_cast h2
  rw [hc', hc₂'] at h3
  linarith

/-- The divisorial valuation of a prime divisor depends only on its generic point. -/
private theorem divisorialValuation_eq_of_genericPoint_eq {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {E E' : Mori.PrimeDivisor Y}
    (h : E.genericPoint = E'.genericPoint) (g : Y.functionField) :
    E.divisorialValuation g = E'.divisorialValuation g := by
  by_cases hg : g = 0
  · rw [hg, map_zero, map_zero]
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg, h]

/-- **Divisorial valuations under an isomorphism.** If `ψ : Y ≅ Z` carries the generic point of
`Q` to that of `Q'`, then `v_{Q'} = v_Q ∘ ψ^*`. -/
private theorem divisorialValuation_eq_of_iso {Y Z : Scheme.{0}} [IsIntegral Y] [IsNoetherian Y]
    [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sY : Y ⟶ Spec (.of ℂ)}
    (hYn : IsNormalVariety ℂ sY) (ψ : Y ≅ Z) (hZn : IsNormalVariety ℂ (ψ.inv ≫ sY))
    (Q : Mori.PrimeDivisor Y) (Q' : Mori.PrimeDivisor Z) (h : ψ.hom Q.genericPoint = Q'.genericPoint)
    (g : Z.functionField) :
    Q'.divisorialValuation g = Q.divisorialValuation (functionFieldMap ψ.hom g) := by
  have hbir : IsBirational ψ.inv := by
    have : IsIso (ψ.inv.stalkMap (genericPoint Z)) :=
      ((isIso_iff_isIso_stalkMap ψ.inv).mp inferInstance).2 _
    exact isBirational_of_isIso_stalkMap_genericPoint ψ.inv
  obtain ⟨Q'', -, hQ''g, -, -, hQ''v⟩ :=
    exists_primeDivisor_map_genericPoint_eq (k := ℂ) hYn ψ.inv hbir hZn Q
  have hgen : Q''.genericPoint = Q'.genericPoint := by
    rw [← h, ← hQ''g, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have h1 := hQ''v (functionFieldMap ψ.hom g)
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_congr (Iso.inv_hom_id ψ),
    functionFieldMap_id_apply, divisorialValuation_eq_of_genericPoint_eq hgen] at h1
  exact h1

/-- **Orders under a valuation-preserving map of function fields.** If `φ : k(Z) → k(Y)` carries
`v_Q` to `v_{Q'}`, i.e. `v_{Q'} = v_Q ∘ φ`, then `ord_Q(φ x) = ord_{Q'}(x)`. -/
private theorem ord_eq_of_divisorialValuation_eq {Y Z : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {Q : Mori.PrimeDivisor Y} {Q' : Mori.PrimeDivisor Z} (φ : Z.functionField →+* Y.functionField)
    (hv : ∀ g, Q'.divisorialValuation g = Q.divisorialValuation (φ g)) (x : Z.functionField) :
    Y.ord (φ x) Q.genericPoint = Z.ord x Q'.genericPoint := by
  by_cases hx : x = 0
  · rw [hx, map_zero, Scheme.ord_zero, Scheme.ord_zero]
    rfl
  have h1 := hv x
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hx,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero φ).mpr hx)] at h1
  have h2 := WithZero.exp_injective h1
  omega

/-- **The local rings of two prime divisors identified by an isomorphism.** Let `ψ : Y ≅ Z`
carry `T ⟶ Y` onto `T' ⟶ Z` through `ψ_T : T ≅ T'`, the images being the prime divisors `Q`,
`Q'`. Then `ψ^*` carries `v_{Q'}` to `v_Q`, and the stalk map `𝒪_{Z,Q'} → 𝒪_{Y,Q}` of `ψ` is
compatible with `ψ^*` on function fields, with `ψ_T^*` on the divisors, and preserves orders. -/
private theorem exists_stalkHom_of_iso
    {Y Z T T' : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hYn : IsNormalVariety ℂ sY) (hZn : IsNormalVariety ℂ sZ)
    (ψ : Y ≅ Z) (hψs : ψ.hom ≫ sZ = sY)
    (σ : FunctionFieldEquiv sY sZ) (hσ : ∀ a, σ a = functionFieldMap ψ.hom a)
    [IsIntegral T] [IsIntegral T'] {jT : T ⟶ Y} {jT' : T' ⟶ Z}
    (Q : Mori.PrimeDivisor Y) (Q' : Mori.PrimeDivisor Z)
    (hQr : Set.range jT.base = (Q.support : Set Y)) (hQ'r : Set.range jT'.base = (Q'.support : Set Z))
    (ψT : T ≅ T') (hψT : ψT.hom ≫ jT' = jT ≫ ψ.hom)
    (σT : FunctionFieldEquiv (jT ≫ sY) (jT' ≫ sZ)) (hσT : ∀ a, σT a = functionFieldMap ψT.hom a) :
    (∀ g, Q'.divisorialValuation g = Q.divisorialValuation ((σ.toHom) g)) ∧
    ∃ ψs : Z.presheaf.stalk (jT' (genericPoint T')) →+* Y.presheaf.stalk (jT (genericPoint T)),
      (∀ a, algebraMap _ Y.functionField (ψs a) = (σ.toHom) (algebraMap _ Z.functionField a)) ∧
      (∀ a, Y.ord (algebraMap _ Y.functionField (ψs a)) (jT (genericPoint T)) =
        Z.ord (algebraMap _ Z.functionField a) (jT' (genericPoint T'))) ∧
      ∀ a, (jT.stalkMap (genericPoint T)).hom (ψs a) =
        (σT.toHom) ((jT'.stalkMap (genericPoint T')).hom a) := by
  haveI : IsNoetherian Y := {}
  have hsZ : ψ.inv ≫ sY = sZ := by rw [← hψs, Iso.inv_hom_id_assoc]
  have hr : Set.range (jT ≫ ψ.hom).base = (Q'.support : Set Z) := by
    rw [← hψT, ← hQ'r, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (ConcreteCategory.bijective_of_isIso ψT.hom.base).2.range_eq, Set.image_univ]
  have e1 : jT (genericPoint T) = Q.genericPoint := map_genericPoint_eq_of_range_eq jT Q hQr
  have e2 : jT' (genericPoint T') = Q'.genericPoint := map_genericPoint_eq_of_range_eq jT' Q' hQ'r
  have hgen : ψ.hom Q.genericPoint = Q'.genericPoint := by
    rw [← e1]
    exact map_genericPoint_eq_of_range_eq (jT ≫ ψ.hom) Q' hr
  have hvQ : ∀ g, Q'.divisorialValuation g = Q.divisorialValuation ((σ.toHom) g) := fun g => by
    rw [divisorialValuation_eq_of_iso hYn ψ (by rwa [hsZ]) Q Q' hgen g]
    exact congrArg _ (hσ g).symm
  have hsp : ψ.hom (jT (genericPoint T)) ⤳ jT' (genericPoint T') := by
    rw [e1, e2, hgen]
  let ψs := (Z.presheaf.stalkSpecializes hsp ≫ ψ.hom.stalkMap (jT (genericPoint T))).hom
  have hψs' : ∀ a, algebraMap _ Y.functionField (ψs a) =
      (σ.toHom) (algebraMap _ Z.functionField a) := by
    intro a
    have h := congrArg (fun φ => φ.hom a)
      (stalkSpecializes_stalkMap_algebraMap ψ.hom (jT (genericPoint T)) _ hsp)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    change _ = σ _
    rw [hσ]
    exact h
  refine ⟨hvQ, ψs, hψs', fun a => ?_, fun a => ?_⟩
  · rw [hψs']
    generalize algebraMap _ Z.functionField a = x
    rw [e1, e2]
    exact ord_eq_of_divisorialValuation_eq (σ.toHom : Z.functionField →+* Y.functionField) hvQ x
  · have h := stalkMap_apply_eq_functionFieldMap_apply ψ.hom jT' jT ψT.hom hψT hsp a
    change _ = σT _
    rw [hσT]
    exact h

/-- **An isomorphism of adjunction steps over a crepant isomorphism is crepant.** Let
`ψ : Y ≅ Z` be an isomorphism of normal projective varieties over `ℂ` identifying `(Y, B_Y)`
and `(Z, B_Z)` crepantly, and `T ⟶ Y`, `T' ⟶ Z` adjunction steps identified by an isomorphism
`ψ_T : T ≅ T'` over `ψ`. Then `ψ_T` identifies the adjunction pairs `(T, B_T)` and `(T', B_T')`
crepantly. -/
private theorem isCrepantBirationalMap_of_isAdjunctionStep_of_iso
    {Y Z T T' : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] [IsProper sY]
    [LocallyOfFiniteType sZ] [IsProper sZ]
    (hYn : IsNormalVariety ℂ sY) (hZn : IsNormalVariety ℂ sZ) {d : ℕ}
    (hd : topologicalKrullDim Y = (d + 1 : ℕ)) (hdZ : topologicalKrullDim Z = (d + 1 : ℕ))
    {BY : QDivisor Y} {BZ : QDivisor Z} {K : Divisor Y} {KZ : Divisor Z}
    (hK : K.IsCanonicalDivisor sY (d + 1)) (hKZ : KZ.IsCanonicalDivisor sZ (d + 1))
    (hKB : (Divisor.toQDivisor K + BY).IsQCartier)
    (hKBZ : (Divisor.toQDivisor KZ + BZ).IsQCartier)
    (ψ : Y ≅ Z) (hψs : ψ.hom ≫ sZ = sY)
    (σ : FunctionFieldEquiv sY sZ) (hσ : ∀ a, σ a = functionFieldMap ψ.hom a)
    (hσc : IsCrepantBirationalMap sY sZ BY BZ σ)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [IsIntegral T'] [IsLocallyNoetherian T']
    [IsNormal T'] {jT : T ⟶ Y} {jT' : T' ⟶ Z} {BT : QDivisor T} {BT' : QDivisor T'}
    (hj : IsAdjunctionStep sY BY jT BT) (hjT' : IsAdjunctionStep sZ BZ jT' BT')
    (ψT : T ≅ T') (hψT : ψT.hom ≫ jT' = jT ≫ ψ.hom)
    (σT : FunctionFieldEquiv (jT ≫ sY) (jT' ≫ sZ)) (hσT : ∀ a, σT a = functionFieldMap ψT.hom a) :
    IsCrepantBirationalMap (jT ≫ sY) (jT' ≫ sZ) BT BT' σT := by
  obtain ⟨-, Q, -, hQr, hci, -⟩ := id hj
  obtain ⟨-, Q', -, hQ'r, hci', -⟩ := id hjT'
  haveI := hci
  haveI := hci'
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace jT
  haveI : CompactSpace T' := QuasiCompact.compactSpace_of_compactSpace jT'
  obtain ⟨hvQ, ψs, hψs, hord, hψT'⟩ :=
    exists_stalkHom_of_iso hYn hZn ψ hψs σ hσ Q Q' hQr hQ'r ψT hψT σT hσT
  exact isCrepantBirationalMap_of_isAdjunctionStep (k := ℂ) hYn hZn hd hdZ hK hKZ hKB hKBZ σ hσc
    hj hjT' Q Q' hQr hQ'r hvQ ψs hψs hord σT fun a => (hψT' a).symm

/-- **Poincaré residues under an isomorphism of adjunction steps.** If `ψ_T : T ≅ T'` lies over
`ψ : Y ≅ Z` and `T ⟶ Y`, `T' ⟶ Z` are closed immersions onto prime divisors, then
`Res_T(ψ^*τ) = ψ_T^* Res_{T'}(τ)`. -/
private theorem isPoincareResidue_pluriformPullback_of_iso
    {Y Z T T' : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY]
    [LocallyOfFiniteType sZ] (hYn : IsNormalVariety ℂ sY) (hZn : IsNormalVariety ℂ sZ) {d : ℕ}
    (hd : topologicalKrullDim Y = (d + 1 : ℕ)) (hdZ : topologicalKrullDim Z = (d + 1 : ℕ))
    (ψ : Y ≅ Z) (hψs : ψ.hom ≫ sZ = sY)
    (σ : FunctionFieldEquiv sY sZ) (hσ : ∀ a, σ a = functionFieldMap ψ.hom a)
    [IsIntegral T] [IsIntegral T'] {jT : T ⟶ Y} {jT' : T' ⟶ Z} [IsClosedImmersion jT]
    [IsClosedImmersion jT'] [LocallyOfFiniteType (jT ≫ sY)] [LocallyOfFiniteType (jT' ≫ sZ)]
    (Q : Mori.PrimeDivisor Y) (Q' : Mori.PrimeDivisor Z)
    (hQr : Set.range jT.base = (Q.support : Set Y)) (hQ'r : Set.range jT'.base = (Q'.support : Set Z))
    (ψT : T ≅ T') (hψT : ψT.hom ≫ jT' = jT ≫ ψ.hom)
    (σT : FunctionFieldEquiv (jT ≫ sY) (jT' ≫ sZ)) (hσT : ∀ a, σT a = functionFieldMap ψT.hom a)
    {N : ℕ} {τ : RationalPluriForms sZ (d + 1) N} {ρ : RationalPluriForms (jT' ≫ sZ) d N}
    (h : IsPoincareResidue sZ jT' d N τ ρ) :
    IsPoincareResidue sY jT d N (pluriformPullback sY sZ σ.toHom (d + 1) N τ)
      (pluriformPullback (jT ≫ sY) (jT' ≫ sZ) σT.toHom d N ρ) := by
  obtain ⟨-, ψs, hψs, hord, hψT'⟩ :=
    exists_stalkHom_of_iso hYn hZn ψ hψs σ hσ Q Q' hQr hQ'r ψT hψT σT hσT
  exact isPoincareResidue_pluriformPullback jT jT' hd hdZ
    (topologicalKrullDim_eq_of_range_eq_support sY jT Q hQr hd)
    (topologicalKrullDim_eq_of_range_eq_support sZ jT' Q' hQ'r hdZ) σ.toHom σT.toHom ψs hψs
    hψT' hord h

/-- **One adjunction step, carried across a crepant isomorphism.** Let `ψ : Y ≅ Z` be an
isomorphism of normal projective varieties over `ℂ` identifying the pairs `(Y, B_Y)` and
`(Z, B_Z)` crepantly, with `(Z, B_Z)` dlt. For an adjunction step `T ⟶ Y` onto `Q` there is an
adjunction step `T' ⟶ Z` onto `ψ(Q)` with `(T', B_T')` dlt, and an isomorphism `T ≅ T'` over `ψ`
identifying `(T, B_T)` and `(T', B_T')` crepantly. -/
private theorem exists_isAdjunctionStep_iso_of_isAdjunctionStep
    {Y Z T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] [IsProper sY]
    [LocallyOfFiniteType sZ] [IsProper sZ]
    (hYn : IsNormalVariety ℂ sY) (hZn : IsNormalVariety ℂ sZ) {d : ℕ}
    (hd : topologicalKrullDim Y = (d + 1 : ℕ)) (hdZ : topologicalKrullDim Z = (d + 1 : ℕ))
    {BY : QDivisor Y} {BZ : QDivisor Z} {K : Divisor Y} {KZ : Divisor Z}
    (hK : K.IsCanonicalDivisor sY (d + 1)) (hKZ : KZ.IsCanonicalDivisor sZ (d + 1))
    (hKB : (Divisor.toQDivisor K + BY).IsQCartier)
    (hKBZ : (Divisor.toQDivisor KZ + BZ).IsQCartier)
    (hPY : MMP.Mori.IsPair sY BY) (hPZ : MMP.Mori.IsPair sZ BZ)
    (hdltZ : MMP.Intersection.IsDltPair sZ BZ)
    (ψ : Y ≅ Z) (hψs : ψ.hom ≫ sZ = sY)
    (σ : FunctionFieldEquiv sY sZ) (hσ : ∀ a, σ a = functionFieldMap ψ.hom a)
    (hσc : IsCrepantBirationalMap sY sZ BY BZ σ)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] {jT : T ⟶ Y} {BT : QDivisor T}
    (hj : IsAdjunctionStep sY BY jT BT) :
    ∃ (T' : Scheme.{0}) (jT' : T' ⟶ Z) (BT' : QDivisor T') (hjT' : IsAdjunctionStep sZ BZ jT' BT')
      (ψT : T ≅ T'), ψT.hom ≫ jT' = jT ≫ ψ.hom ∧
      haveI : IsIntegral T' := hjT'.1.1.toIsIntegral
      haveI : IsNormal T' := hjT'.1.2
      haveI : IsLocallyNoetherian T' := by
        have := hjT'.1.1
        exact LocallyOfFiniteType.isLocallyNoetherian (jT' ≫ sZ)
      MMP.Intersection.IsDltPair (jT' ≫ sZ) BT' ∧
      ∃ σT : FunctionFieldEquiv (jT ≫ sY) (jT' ≫ sZ),
        (∀ a, σT a = functionFieldMap ψT.hom a) ∧
        IsCrepantBirationalMap (jT ≫ sY) (jT' ≫ sZ) BT BT' σT := by
  classical
  obtain ⟨-, Q, hQ1, hQr, hci, -⟩ := id hj
  haveI := hci
  haveI : IsNoetherian Y := {}
  have hsZ : ψ.inv ≫ sY = sZ := by rw [← hψs, Iso.inv_hom_id_assoc]
  have hbir : IsBirational ψ.inv := by
    have : IsIso (ψ.inv.stalkMap (genericPoint Z)) :=
      ((isIso_iff_isIso_stalkMap ψ.inv).mp inferInstance).2 _
    exact isBirational_of_isIso_stalkMap_genericPoint ψ.inv
  obtain ⟨Q', -, hQ'g, -, -, -⟩ := exists_primeDivisor_map_genericPoint_eq (k := ℂ) hYn ψ.inv
    hbir (by rwa [hsZ]) Q
  have hgen : ψ.hom Q.genericPoint = Q'.genericPoint := by
    rw [← hQ'g, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hvQ : ∀ g, Q'.divisorialValuation g = Q.divisorialValuation ((σ.toHom) g) := by
    intro g
    rw [divisorialValuation_eq_of_iso hYn ψ (by rwa [hsZ]) Q Q' hgen g]
    exact congrArg _ (hσ g).symm
  have hcoef : BZ.coeff Q' = BY.coeff Q :=
    coeff_eq_of_isCrepantBirationalMap hPY hPZ hK hKZ σ hσc Q Q' hvQ
  obtain ⟨T', jT', BT', hjT', hrT', hdltT'⟩ :=
    exists_isAdjunctionStep_of_one_le_coeff hdltZ hdZ Q' (hcoef ▸ hQ1)
  haveI : IsIntegral T' := hjT'.1.1.toIsIntegral
  haveI : IsNormal T' := hjT'.1.2
  haveI : IsLocallyNoetherian T' := by
    have := hjT'.1.1
    exact LocallyOfFiniteType.isLocallyNoetherian (jT' ≫ sZ)
  obtain ⟨-, -, -, -, hci', -⟩ := id hjT'
  haveI := hci'
  have hrange : Set.range (jT ≫ ψ.hom).base = Set.range jT'.base := by
    rw [hrT', Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hQr,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have h := (Scheme.homeoOfIso ψ).image_closure {Q.genericPoint}
    rw [Set.image_singleton] at h
    change ψ.hom.base '' _ = _
    erw [h]
    change closure {ψ.hom Q.genericPoint} = _
    rw [hgen]
  obtain ⟨ψT, hψT⟩ := exists_iso_comp_eq_of_range_eq (jT ≫ ψ.hom) jT' hrange
  have hsT : ψT.hom ≫ jT' ≫ sZ = jT ≫ sY := by
    rw [← Category.assoc, hψT, Category.assoc, hψs]
  obtain ⟨σT, hσT⟩ := exists_functionFieldEquiv_of_comp_eq (k := ℂ) ψT.hom
    (functionFieldMap_bijective_of_isIso ψT) hsT
  exact ⟨T', jT', BT', hjT', ψT, hψT, hdltT', σT, hσT,
    isCrepantBirationalMap_of_isAdjunctionStep_of_iso hYn hZn hd hdZ hK hKZ hKB hKBZ ψ hψs σ hσ
      hσc hj hjT' ψT hψT σT hσT⟩

/-! ### Changing the structure morphism by an equality -/

/-- A crepant birational map along equal structure morphisms. -/
private theorem exists_isCrepantBirationalMap_congr {S S' : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    {s₁ s₁' : S ⟶ Spec (.of ℂ)} {s₂ s₂' : S' ⟶ Spec (.of ℂ)} (h₁ : s₁ = s₁') (h₂ : s₂ = s₂')
    {B : QDivisor S} {B' : QDivisor S'} (σ : FunctionFieldEquiv s₁ s₂)
    (hσ : IsCrepantBirationalMap s₁ s₂ B B' σ) :
    ∃ σ' : FunctionFieldEquiv s₁' s₂', (∀ a, (σ'.toHom) a = (σ.toHom) a) ∧
      IsCrepantBirationalMap s₁' s₂' B B' σ' := by
  subst h₁ h₂
  exact ⟨σ, fun _ => rfl, hσ⟩

/-- Pull-backs of forms along equal structure morphisms agree. -/
private theorem pluriformPullback_heq {S S' : Scheme.{0}} [IsIntegral S] [IsIntegral S']
    {s₁ s₁' : S ⟶ Spec (.of ℂ)} {s₂ s₂' : S' ⟶ Spec (.of ℂ)} (h₁ : s₁ = s₁') (h₂ : s₂ = s₂')
    (σ : FunctionFieldEquiv s₁ s₂) (σ' : FunctionFieldEquiv s₁' s₂')
    (hσ : ∀ a, (σ'.toHom) a = (σ.toHom) a)
    {e : ℕ} {N : ℤ} {ρ : RationalPluriForms s₂ e N} {ρ' : RationalPluriForms s₂' e N}
    (hρ : HEq ρ ρ') :
    HEq (pluriformPullback s₁ s₂ σ.toHom e N ρ) (pluriformPullback s₁' s₂' σ'.toHom e N ρ') := by
  subst h₁ h₂
  letI := functionFieldAlgebra s₁
  letI := functionFieldAlgebra s₂
  have : σ' = σ := AlgEquiv.ext fun a => hσ a
  subst this
  rw [eq_of_heq hρ]

/-- Poincaré residues along equal structure morphisms. -/
private theorem isPoincareResidue_congr {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsIntegral T] (jT : T ⟶ Y) {s s' : Y ⟶ Spec (.of ℂ)} (h : s = s') {e N : ℕ}
    {τ : RationalPluriForms s (e + 1) N} {τ' : RationalPluriForms s' (e + 1) N}
    {ρ : RationalPluriForms (jT ≫ s) e N} {ρ' : RationalPluriForms (jT ≫ s') e N}
    (hτ : HEq τ τ') (hρ : HEq ρ ρ') (hr : IsPoincareResidue s jT e N τ ρ) :
    IsPoincareResidue s' jT e N τ' ρ' := by
  subst h
  rw [← eq_of_heq hτ, ← eq_of_heq hρ]
  exact hr

/-- Dlt pairs along equal structure morphisms. -/
private theorem isDltPair_congr {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {s s' : S ⟶ Spec (.of ℂ)} (h : s = s') {B : QDivisor S} (hB : MMP.Intersection.IsDltPair s B) :
    MMP.Intersection.IsDltPair s' B := h ▸ hB

/-! ### Powers of forms on a line -/

/-- **Equal forms have equal powers.** On a line `Ω^d_{K/ℂ}`, if `c ω^{⊗m} = c' ω'^{⊗m}` with
`m > 0`, then `c^a ω^{⊗am} = c'^a ω'^{⊗am}`. -/
private theorem smul_formPow_pow_eq {K : Type*} [Field K] [Algebra ℂ K] {d : ℕ}
    (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄ℂ])) {m : ℕ} {w w' : ⋀[K]^d Ω[K⁄ℂ]} {c c' : K}
    (h : (c • formPow w m : PluriForms ℂ K d m) = c' • formPow w' m) (a : ℕ) :
    (c ^ a • formPow w (a * m) : PluriForms ℂ K d ((a * m : ℕ) : ℤ)) =
      c' ^ a • formPow w' (a * m) := by
  rw [← basis_unit_repr_smul b w, ← basis_unit_repr_smul b w'] at h ⊢
  simp only [formPow_smul, smul_smul] at h ⊢
  have h1 := congrArg (fun τ => (ZTensorPower.basis b m).repr τ ()) h
  simp only [repr_smul_formPow] at h1
  have key : ∀ x y : K, x ^ a * y ^ (a * m) = (x * y ^ m) ^ a := fun x y => by ring
  rw [key, key, h1]

/-- **Powers of iterated residues.** Along a flag ending at a stratum of dimension `e`, if
`c ω^{⊗m}` has iterated residue `c₁ ω₁^{⊗m}`, then `c^a ω^{⊗am}` has iterated residue
`c₁^a ω₁^{⊗am}` for every `a > 0`. -/
private theorem isIteratedResidueRec_pow {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {BY : QDivisor Y} {n m : ℕ}
    (ω : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^n Ω[Y.functionField⁄ℂ])
    (c : Y.functionField) {S : Scheme.{0}} [IsIntegral S] {ι : S ⟶ Y} {BS : QDivisor S}
    (G : StratumAdjunctionData sY BY ι BS) {e : ℕ} (he : topologicalKrullDim S = e)
    (ω₁ : letI := functionFieldAlgebra (ι ≫ sY); ⋀[S.functionField]^e Ω[S.functionField⁄ℂ])
    (c₁ : S.functionField)
    (h : letI := functionFieldAlgebra sY; letI := functionFieldAlgebra (ι ≫ sY)
      IsIteratedResidueRec (c • (formPow ω m : RationalPluriForms sY n m)) G e
      (c₁ • (formPow ω₁ m : RationalPluriForms (ι ≫ sY) e m))) :
    letI := functionFieldAlgebra sY; letI := functionFieldAlgebra (ι ≫ sY)
    ∀ a, 0 < a → IsIteratedResidueRec
      (c ^ a • (formPow ω (a * m) : RationalPluriForms sY n ((a * m : ℕ) : ℤ))) G e
      (c₁ ^ a • (formPow ω₁ (a * m) : RationalPluriForms (ι ≫ sY) e ((a * m : ℕ) : ℤ))) := by
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (ι ≫ sY)
  intro a ha
  suffices H : ∀ N : ℕ, N = a * m → IsIteratedResidueRec
      (c ^ a • (formPow ω N : RationalPluriForms sY n N)) G e
      (c₁ ^ a • (formPow ω₁ N : RationalPluriForms (ι ≫ sY) e N)) from H _ rfl
  induction a, ha using Nat.le_induction with
  | base =>
    intro N hN
    rw [Nat.succ_eq_add_one, zero_add, one_mul] at hN
    subst hN
    simpa only [pow_one] using h
  | succ a ha ih =>
    intro N hN
    have hmul := IsIteratedResidueRec.mul G he (ih _ rfl) h
    rw [RationalPluriForms.mul_smul_formPow, RationalPluriForms.mul_smul_formPow, ← pow_succ,
      ← pow_succ] at hmul
    rw [Nat.succ_mul] at hN
    subst hN
    exact hmul

/-! ### Matching flags of `(X, B)` with flags of the floor components -/

/-- **Every flag of positive length of `(X, B)` is a flag of a floor component.** A flag
`X ⊃ T₁ ⊃ ⋯ ⊃ S` of iterated adjunction of `(X, B)` starts at a model `T₁` of a floor component
`P`; it is matched by a flag `C_P ⊃ ⋯ ⊃ S'` of `(C_P, B_{C_P})`, one step shorter, with an
isomorphism `S ≅ S'` over `X` which identifies the adjunction pairs crepantly and carries the
iterated residues of a form `τ` along `X ⊃ ⋯ ⊃ S` to those of its residue along `C_P`. -/
private theorem exists_flagMatch
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : Mori.IsProjectiveVariety ℂ sX) {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ)) {B : QDivisor X}
    {C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0}}
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    {j : ∀ P, C P ⟶ X} {BC : ∀ P, QDivisor (C P)} {m : ℕ}
    (hC : ∀ P, IsAdjunctionStep sX B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X))
    (RS : ResidueRestriction (fun P => j P ≫ sX) BC n m)
    (hcanX : ∀ {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
      (F : StratumAdjunctionData sX B ι BS),
      haveI := F.isIntegral_stratum
      haveI := F.isNormal_stratum
      haveI := F.isLocallyNoetherian_stratum
      ∃ (d : ℕ) (K : Divisor S), K.IsCanonicalDivisor (ι ≫ sX) d ∧
        (Divisor.toQDivisor K + BS).IsQCartier) :
    ∀ {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS),
      1 ≤ F.length →
      ∃ (P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}) (S' : Scheme.{0}) (ι' : S' ⟶ C P)
        (BS' : QDivisor S') (F' : StratumAdjunctionData (j P ≫ sX) (BC P) ι' BS') (ψ : S ≅ S'),
        F'.length + 1 = F.length ∧ ψ.hom ≫ ι' ≫ j P = ι ∧
        (haveI := F'.isIntegral_stratum
         haveI := F'.isNormal_stratum
         haveI := F'.isLocallyNoetherian_stratum
         MMP.Intersection.IsDltPair (ι' ≫ j P ≫ sX) BS') ∧
        haveI := F.isIntegral_stratum
        haveI := F.isNormal_stratum
        haveI := F.isLocallyNoetherian_stratum
        haveI := F'.isIntegral_stratum
        haveI := F'.isNormal_stratum
        haveI := F'.isLocallyNoetherian_stratum
        ∃ σ : FunctionFieldEquiv (ι ≫ sX) (ι' ≫ j P ≫ sX),
          (∀ a, (σ.toHom) a = functionFieldMap ψ.hom a) ∧
          IsCrepantBirationalMap (ι ≫ sX) (ι' ≫ j P ≫ sX) BS BS' σ ∧
          ∀ (N : ℕ) (τ : RationalPluriForms sX (n + 1) N)
            (ρP : RationalPluriForms (j P ≫ sX) n N), IsPoincareResidue sX (j P) n N τ ρP →
            ∀ (e : ℕ), topologicalKrullDim S = e →
            ∀ ρ' : RationalPluriForms (ι' ≫ j P ≫ sX) e N, IsIteratedResidueRec ρP F' e ρ' →
              IsIteratedResidueRec τ F e
                (pluriformPullback (ι ≫ sX) (ι' ≫ j P ≫ sX) σ.toHom e N ρ') := by
  classical
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  have hCproper : ∀ P, IsProper (j P ≫ sX) := fun P =>
    isProper_of_isProjectiveMorphism _ (RS.setting.isProjectiveVariety P).isProjective
  intro S ι BS F
  induction F with
  | refl h => intro hF; simp [StratumAdjunctionData.length] at hF
  | @step S₀ T ι₀ BS₀ F₀ jT BT hj ih =>
    intro _
    haveI := F₀.isIntegral_stratum
    haveI := F₀.isNormal_stratum
    haveI := F₀.isLocallyNoetherian_stratum
    haveI := F₀.isClosedImmersion
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : IsNormal T := hj.1.2
    haveI : IsLocallyNoetherian T := by
      have := hj.1.1
      exact LocallyOfFiniteType.isLocallyNoetherian (jT ≫ ι₀ ≫ sX)
    by_cases h0 : F₀.length = 0
    · -- the first step `X ⊃ T`, matched with `C_P` itself
      cases F₀ with
      | step F₁ j₁ BT₁ hj₁ => simp [StratumAdjunctionData.length] at h0
      | refl hp =>
        have hj' : IsAdjunctionStep sX B jT BT := by simpa only [Category.id_comp] using hj
        obtain ⟨-, Q, hQ1, hQr, hci, -⟩ := id hj'
        haveI := hci
        have hfl : ⌊B.coeff Q⌋ ≠ 0 := by
          have : (1 : ℤ) ≤ ⌊B.coeff Q⌋ := Int.le_floor.mpr (by exact_mod_cast hQ1)
          omega
        let P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} := ⟨Q, hfl⟩
        have hPr : Set.range (j P).base = (Q.support : Set X) := (hC P).2
        obtain ⟨-, -, -, -, hciP, -⟩ := id (hC P).1
        haveI := hciP
        obtain ⟨ψ, hψ⟩ := exists_iso_comp_eq_of_range_eq jT (j P) (hQr.trans hPr.symm)
        obtain ⟨-, d, K, hK, hKB⟩ := hp
        have hd : d = n + 1 := by
          have := hK.topologicalKrullDim_eq
          rw [hdim] at this
          exact_mod_cast this.symm
        subst hd
        have hσ0 : ∀ a, (1 : FunctionFieldEquiv sX sX) a = functionFieldMap (Iso.refl X).hom a :=
          fun a => (functionFieldMap_id_apply a).symm
        have hσc0 : IsCrepantBirationalMap sX sX B B 1 := (crepantBirationalAutomorphisms sX B).one_mem
        have hψX : ψ.hom ≫ j P = jT ≫ (Iso.refl X).hom := by rw [hψ]; rfl
        have hsT : ψ.hom ≫ j P ≫ sX = jT ≫ sX := by rw [← Category.assoc, hψ]
        obtain ⟨σT, hσT⟩ := exists_functionFieldEquiv_of_comp_eq (k := ℂ) ψ.hom
          (functionFieldMap_bijective_of_isIso ψ) hsT
        have hcrep := isCrepantBirationalMap_of_isAdjunctionStep_of_iso hXn hXn hdim hdim hK hK hKB
          hKB (Iso.refl X) (Category.id_comp sX) 1 hσ0 hσc0 hj' (hC P).1 ψ hψX σT hσT
        obtain ⟨σ, hσσ, hσcrep⟩ := exists_isCrepantBirationalMap_congr
          (show jT ≫ sX = (jT ≫ 𝟙 X) ≫ sX by simp)
          (show j P ≫ sX = 𝟙 (C P) ≫ j P ≫ sX by simp) σT hcrep
        refine ⟨P, C P, 𝟙 _, BC P, .refl (RS.setting.isPair P).isPair, ψ,
          by simp [StratumAdjunctionData.length], by simp [hψ],
          isDltPair_congr (Category.id_comp _).symm (RS.setting.isDltPair P),
          σ, fun a => (hσσ a).trans (hσT a), hσcrep, ?_⟩
        intro N τ ρP hres e he ρ' hiter
        obtain ⟨rfl, hρ⟩ := hiter
        have hclean := isPoincareResidue_pluriformPullback_of_iso hXn hXn hdim hdim (Iso.refl X)
          (Category.id_comp sX) 1 hσ0 Q Q hQr hPr ψ hψX σT hσT hres
        rw [pluriformPullback_one (by exact_mod_cast hdim)] at hclean
        have h₁ : (jT ≫ 𝟙 X) ≫ sX = jT ≫ sX := by rw [Category.comp_id]
        have h₂ : 𝟙 (C P) ≫ j P ≫ sX = j P ≫ sX := Category.id_comp _
        have hpb := pluriformPullback_heq h₁ h₂ σ σT (fun a => (hσσ a).symm) hρ
        refine ⟨cast (by rw [Category.id_comp]) τ, ⟨rfl, cast_heq _ _⟩,
          cast (by rw [Category.id_comp])
            (pluriformPullback (jT ≫ sX) (j P ≫ sX) σT.toHom n N ρP), ?_, ?_⟩
        · exact isPoincareResidue_congr jT (Category.id_comp sX).symm (cast_heq _ _).symm
            (cast_heq _ _).symm hclean
        · exact hpb.trans (cast_heq _ _).symm
    · obtain ⟨P, S', ι', BS', F', ψ, hlen, hcomp, hdlt', hrest⟩ := ih (by omega)
      haveI := F'.isIntegral_stratum
      haveI := F'.isNormal_stratum
      haveI := F'.isLocallyNoetherian_stratum
      haveI := F'.isClosedImmersion
      obtain ⟨σ, hσ, hσc, hres⟩ := hrest
      haveI := hCproper P
      haveI : CompactSpace (C P) := QuasiCompact.compactSpace_of_compactSpace (j P ≫ sX)
      haveI : CompactSpace S₀ := QuasiCompact.compactSpace_of_compactSpace ι₀
      haveI : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace ι'
      have hS₀n : IsNormalVariety ℂ (ι₀ ≫ sX) := F₀.isNormalVariety
      have hS'n : IsNormalVariety ℂ (ι' ≫ j P ≫ sX) := F'.isNormalVariety
      haveI : LocallyOfFiniteType (ι₀ ≫ sX) := hS₀n.1.toLocallyOfFiniteType
      haveI : LocallyOfFiniteType (ι' ≫ j P ≫ sX) := hS'n.1.toLocallyOfFiniteType
      haveI : LocallyOfFiniteType (jT ≫ ι₀ ≫ sX) := hj.1.1.toLocallyOfFiniteType
      obtain ⟨-, Q, hQ1, hQr, hci, -⟩ := id hj
      haveI := hci
      -- dimensions: `T` has dimension `d`, the ambient strata `S₀ ≅ S'` dimension `d + 1`
      set d := (letI := functionFieldAlgebra (jT ≫ ι₀ ≫ sX)
        (Algebra.trdeg ℂ T.functionField).toNat) with hd
      have hdT : topologicalKrullDim T = d := topologicalKrullDim_eq_toNat_trdeg (jT ≫ ι₀ ≫ sX)
      have hdS₀ : topologicalKrullDim S₀ = (d + 1 : ℕ) := by
        rw [topologicalKrullDim_eq_toNat_trdeg (ι₀ ≫ sX), ← hj.trdeg_add_one]
      have hdS' : topologicalKrullDim S' = (d + 1 : ℕ) := by
        have h1 := StratumAdjunctionData.dim_add_length (sX := sX) hdim F₀ hdS₀
        have h2 := StratumAdjunctionData.dim_add_length (sX := j P ≫ sX)
          (RS.setting.topologicalKrullDim_eq P) F'
          (topologicalKrullDim_eq_toNat_trdeg (ι' ≫ j P ≫ sX))
        rw [topologicalKrullDim_eq_toNat_trdeg (ι' ≫ j P ≫ sX)]
        congr 1
        norm_cast
        omega
      -- canonical divisors and `ℚ`-Cartier adjoints on both sides
      obtain ⟨d₁, K, hK, hKB⟩ := hcanX F₀
      obtain ⟨d₂, K', hK', hK'C⟩ := RS.setting.isCartierDivisor P F'
      have hd₁ : d₁ = d + 1 := by
        have := hK.topologicalKrullDim_eq
        rw [hdS₀] at this
        exact_mod_cast this.symm
      have hd₂ : d₂ = d + 1 := by
        have := hK'.topologicalKrullDim_eq
        rw [hdS'] at this
        exact_mod_cast this.symm
      subst hd₁ hd₂
      have hKB' : (Divisor.toQDivisor K' + BS').IsQCartier :=
        ⟨m, by exact_mod_cast RS.setting.pos.ne', hK'C⟩
      have hψs : ψ.hom ≫ ι' ≫ j P ≫ sX = ι₀ ≫ sX := by
        rw [← hcomp]
        simp only [Category.assoc]
      have hσ' : ∀ a, σ a = functionFieldMap ψ.hom a := hσ
      obtain ⟨T', jT', BT', hjT', ψT, hψT, hdltT', σT, hσT, hσTc⟩ :=
        exists_isAdjunctionStep_iso_of_isAdjunctionStep hS₀n hS'n hdS₀ hdS' hK hK' hKB hKB'
          ⟨hS₀n, _, K, hK, hKB⟩ ⟨hS'n, _, K', hK', hKB'⟩ hdlt' ψ hψs σ hσ' hσc hj
      haveI : IsIntegral T' := hjT'.1.1.toIsIntegral
      haveI : IsNormal T' := hjT'.1.2
      haveI : IsLocallyNoetherian T' := by
        have := hjT'.1.1
        exact LocallyOfFiniteType.isLocallyNoetherian (jT' ≫ ι' ≫ j P ≫ sX)
      haveI : LocallyOfFiniteType (jT' ≫ ι' ≫ j P ≫ sX) := hjT'.1.1.toLocallyOfFiniteType
      obtain ⟨-, Q', -, hQ'r, hci', -⟩ := id hjT'
      haveI := hci'
      obtain ⟨σn, hσn, hσnc⟩ := exists_isCrepantBirationalMap_congr
        (show jT ≫ ι₀ ≫ sX = (jT ≫ ι₀) ≫ sX by rw [Category.assoc])
        (show jT' ≫ ι' ≫ j P ≫ sX = (jT' ≫ ι') ≫ j P ≫ sX by rw [Category.assoc]) σT hσTc
      refine ⟨P, T', jT' ≫ ι', BT', F'.step jT' BT' hjT', ψT,
        by simp only [StratumAdjunctionData.length]; omega, ?_,
        isDltPair_congr (by rw [Category.assoc]) hdltT', σn, fun a => (hσn a).trans (hσT a),
        hσnc, ?_⟩
      · rw [Category.assoc, ← Category.assoc ψT.hom, hψT, Category.assoc, hcomp]
      intro N τ ρP hresP e he ρ' hiter
      obtain ⟨ρ₀', hρ₀', ρ'', hr'', hρ''⟩ := hiter
      have he' : e = d := by
        rw [hdT] at he
        exact_mod_cast he.symm
      subst he'
      have IH := hres N τ ρP hresP (d + 1) hdS₀ ρ₀' hρ₀'
      have hfun := isPoincareResidue_pluriformPullback_of_iso hS₀n hS'n hdS₀ hdS' ψ hψs σ hσ' Q Q'
        hQr hQ'r ψT hψT σT hσT hr''
      refine ⟨_, IH, _, hfun, ?_⟩
      exact pluriformPullback_heq (by rw [Category.assoc]) (by rw [Category.assoc]) σn σT
        (fun a => (hσn a).symm) hρ''

/-! ### Sections pulled back from the base of the contraction -/

/-- A function regular near the generic point of a prime divisor has non-negative order along
it. -/
private theorem ord_germToFunctionField_nonneg {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : Mori.PrimeDivisor Y) {U : Y.Opens} [Nonempty U]
    (hU : E.genericPoint ∈ U) (s : Γ(Y, U)) :
    0 ≤ Y.ord (Y.germToFunctionField U s) E.genericPoint := by
  by_cases hs : Y.germToFunctionField U s = 0
  · rw [hs, Scheme.ord_zero]
    rfl
  have h1 : E.divisorialValuation (Y.germToFunctionField U s) ≤ 1 := by
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨Y.presheaf.germ U E.genericPoint hU s,
      Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hU s⟩
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hs] at h1
  have h2 : -Y.ord (Y.germToFunctionField U s) E.genericPoint ≤ 0 := by
    have := WithZero.exp_le_exp.mp (h1.trans_eq WithZero.exp_zero.symm)
    exact this
  omega

/-- A local equation of `D` on `U` gives one of `n • D` on `U`. -/
private theorem isLocalEquation_pow {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    {D : Divisor Y} {U : Y.Opens} {φ : (RationalFunctions Y)ˣ} (h : D.IsLocalEquation U φ)
    (n : ℕ) : (n • D).IsLocalEquation U (φ ^ n) := by
  induction n with
  | zero => simpa using Divisor.isLocalEquation_zero U
  | succ n ih => simpa [succ_nsmul, pow_succ] using ih.add h

/-- The unique irreducible component of an integral scheme. -/
private def univComponent (Y : Scheme.{0}) [IsIntegral Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

/-- `ev((e^n)⁻¹) = ev(e)⁻¹ ^ n` for a unit `e` of `K(Y)`. -/
private theorem evalFF_inv_pow {Y : Scheme.{0}} [IsIntegral Y] (e : (RationalFunctions Y)ˣ)
    (n : ℕ) :
    MMP.Threefold.Mori.Helpers.evalFF (univComponent Y)
        (((e ^ n)⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) =
      (MMP.Threefold.Mori.Helpers.evalFF (univComponent Y) (e : RationalFunctions Y))⁻¹ ^ n := by
  have h1 : MMP.Threefold.Mori.Helpers.evalFF (univComponent Y)
      (((e ^ n)⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) *
        (MMP.Threefold.Mori.Helpers.evalFF (univComponent Y) (e : RationalFunctions Y)) ^ n =
      1 := by
    rw [← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, map_one]
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left h1

/-- A global divisorial section of `𝒪_Y(D)`, read in the function field. -/
private noncomputable def divisorialSectionValue {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {D : Divisor Y} (φ : Γ(D.divisorialSheaf, ⊤)) : Y.functionField :=
  MMP.Threefold.Mori.Helpers.evalFF (univComponent Y)
    (rationalFunctionsPresheafTopEquiv Y (show D.divisorialSubmodule ⊤ from φ).1)

/-- **A divisorial section is a regular function times a local generator.** If `e` is a local
equation of `D` on `U`, a global section `φ` of `𝒪_Y(n D)` is `h · e^{-n}` on `U` for a
function `h` on `U`. -/
private theorem exists_divisorialSectionValue_eq {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y} {U : Y.Opens} [Nonempty U]
    {e : (RationalFunctions Y)ˣ} (he : D.IsLocalEquation U e) (n : ℕ)
    (φ : Γ((n • D).divisorialSheaf, ⊤)) :
    ∃ h : Γ(Y, U), h • (n • D).divisorialSheaf.presheaf.map (homOfLE le_rfl).op
        (isLocalEquation_pow he n).invSection =
        (n • D).divisorialSheaf.presheaf.map (homOfLE le_top).op φ ∧
      divisorialSectionValue φ = Y.germToFunctionField U h *
      MMP.Threefold.Mori.Helpers.evalFF (univComponent Y) (((e ^ n)⁻¹ : (RationalFunctions Y)ˣ) :
        RationalFunctions Y) := by
  have hZU : componentGenericPoint Y (univComponent Y) ∈ U :=
    LocalFrame.componentGenericPoint_mem_of_isIntegral (univComponent Y)
      (⟨(Classical.arbitrary U).1, (Classical.arbitrary U).2⟩)
  obtain ⟨c, hc⟩ := ((isLocalEquation_pow he n).isLocalGenerator_invSection U le_rfl).2
    ((n • D).divisorialSheaf.presheaf.map (homOfLE le_top).op φ)
  refine ⟨c, hc, ?_⟩
  have h1 := congrFun (congrArg Subtype.val hc) ⟨univComponent Y, hZU⟩
  change Y.presheaf.germ U _ hZU c *
      (((e ^ n)⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) (univComponent Y) =
    (show (n • D).divisorialSubmodule ⊤ from φ).1 ⟨univComponent Y, trivial⟩ at h1
  change (Y.presheaf.stalkSpecializes _).hom
      ((show (n • D).divisorialSubmodule ⊤ from φ).1 ⟨univComponent Y, trivial⟩) = _
  rw [← h1, map_mul]
  congr 1
  exact TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hZU _ c

/-- The tensor power `w^{⊗N}` of a rational top form, as a rational `N`-canonical form. -/
private noncomputable def formPowR {Y : Scheme.{0}} [IsIntegral Y] (sY : Y ⟶ Spec (.of ℂ))
    {d : ℕ} (w : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^d Ω[Y.functionField⁄ℂ])
    (N : ℕ) : RationalPluriForms sY d N :=
  letI := functionFieldAlgebra sY
  formPow w N

/-- `(f w^{⊗a}) · (g w^{⊗b}) = (f g) w^{⊗(a+b)}`. -/
private theorem mul_smul_formPowR {Y : Scheme.{0}} [IsIntegral Y] {sY : Y ⟶ Spec (.of ℂ)}
    {d : ℕ} (w : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^d Ω[Y.functionField⁄ℂ])
    (a b : ℕ) (f g : Y.functionField) :
    RationalPluriForms.mul sY d a b (f • formPowR sY w a) (g • formPowR sY w b) =
      (f * g) • formPowR sY w (a + b) :=
  RationalPluriForms.mul_smul_formPow w a b f g

/-- **A rational top form whose divisor is the canonical divisor**, with its tensor powers:
`w^{⊗N} ≠ 0` and `div(w^{⊗N}) = N K_X` for `N > 0`. -/
private theorem exists_formPowR_ordForm_eq {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    {n : ℕ} (hdim : topologicalKrullDim X = (n + 1 : ℕ)) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX (n + 1)) :
    ∃ w : (letI := functionFieldAlgebra sX; ⋀[X.functionField]^(n + 1) Ω[X.functionField⁄ℂ]),
      ∀ N : ℕ, 0 < N → formPowR sX w N ≠ 0 ∧
        ∀ Γ : Mori.PrimeDivisor X, Γ.ordForm (formPowR sX w N) = N * K.coeff Γ := by
  letI := functionFieldAlgebra sX
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) (d := n + 1) (by rw [hdim])
  set c := (ZTensorPower.basis b 1).repr (ω : RationalPluriForms sX (n + 1) ((1 : ℕ) : ℤ)) ()
  have hω : ω = formPowR sX (c • b ()) 1 := by
    change ω = formPow (c • b ()) 1
    rw [formPow_smul, pow_one]
    exact eq_repr_smul_formPow b (ω : RationalPluriForms sX (n + 1) ((1 : ℕ) : ℤ))
  refine ⟨c • b (), fun N hN => ?_⟩
  induction N, hN using Nat.le_induction with
  | base => exact ⟨hω ▸ hω0, fun Γ => by rw [← hω, hωK]; simp⟩
  | succ N hN ih =>
    have hmul := mul_smul_formPowR (sY := sX) (c • b ()) N 1 1 1
    rw [one_smul, one_smul, one_mul, one_smul] at hmul
    have h1 : formPowR sX (c • b ()) 1 ≠ 0 := hω ▸ hω0
    have hd : topologicalKrullDim X = (n + 1 : ℕ) := hdim
    refine ⟨hmul ▸ RationalPluriForms.mul_ne_zero hd ih.1 h1, fun Γ => ?_⟩
    rw [← hmul, ordForm_mul Γ ih.1 h1, ih.2 Γ, ← hω, hωK]
    push_cast
    ring

/-- **Pull-backs of sections of `qH`.** Let `f : X ⟶ R` be dominant, `M = f^*H` for a Cartier
divisor `H`, `k(K_X + B) = M`, and `w` a top form with `div w = K_X`. For a global section `φ`
of `𝒪_R(acH)`, the form `f^*φ · w^{⊗ akc}` is a section of `akc(K_X + B)`. -/
private theorem pullback_smul_formPow_mem_logPluricanonicalSections
    {X R : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R]
    (f : X ⟶ R) [IsDominant f] {H : Divisor R} (hH : H.IsCartier)
    {hfH : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ H.supp}
    {M : Divisor X} (hM : H.IsPullback f hfH M) {K : Divisor X} {B : QDivisor X} {k c a : ℕ}
    {u : X.functionField} (hu0 : u ≠ 0)
    (hMu : ∀ Γ : Mori.PrimeDivisor X,
      (X.ord u Γ.genericPoint : ℚ) = M.coeff Γ - k * (K.coeff Γ + B.coeff Γ))
    (w : letI := functionFieldAlgebra sX; ⋀[X.functionField]^(n + 1) Ω[X.functionField⁄ℂ])
    (hw : ∀ N : ℕ, 0 < N → formPowR sX w N ≠ 0 ∧
      ∀ Γ : Mori.PrimeDivisor X, Γ.ordForm (formPowR sX w N) = N * K.coeff Γ)
    (hN : 0 < a * (k * c)) (φ : Γ(((a * c) • H).divisorialSheaf, ⊤)) :
    letI := functionFieldAlgebra sX
    (functionFieldMap f (divisorialSectionValue φ) * u ^ (a * c)) • formPowR sX w (a * (k * c)) ∈
      logPluricanonicalSections sX (n + 1) (a * (k * c)) B := by
  letI := functionFieldAlgebra sX
  refine ⟨fun h => absurd h (by simp), fun Γ _ hne => ?_⟩
  set g := functionFieldMap f (divisorialSectionValue φ) with hg
  have hgu0 : g * u ^ (a * c) ≠ 0 := by
    rintro h0
    exact hne (by simp [h0])
  have hg0 : g ≠ 0 := left_ne_zero_of_mul hgu0
  rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hdim hgu0 (hw _ hN).1, (hw _ hN).2 Γ,
    Scheme.ord_mul hg0 (pow_ne_zero _ hu0), Scheme.ord_pow hu0]
  -- the coefficient of `⌊akc B⌋`
  have hB : (DivisorWithCoeffs.roundDown (((a * (k * c) : ℕ) : ℤ) • B)).coeff Γ =
      ((a * c : ℕ) : ℤ) * M.coeff Γ - ((a * (k * c) : ℕ) : ℤ) * K.coeff Γ -
        ((a * c : ℕ) : ℤ) * X.ord u Γ.genericPoint := by
    have h1 := hMu Γ
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, Int.floor_eq_iff]
    simp only [zsmul_eq_mul]
    push_cast
    have hE : ((a : ℚ) * ((k : ℚ) * (c : ℚ))) * B.coeff Γ =
        (a : ℚ) * (c : ℚ) * (M.coeff Γ : ℚ) - (a : ℚ) * ((k : ℚ) * (c : ℚ)) * (K.coeff Γ : ℚ) -
          (a : ℚ) * (c : ℚ) * (X.ord u Γ.genericPoint : ℚ) := by
      linear_combination ((a : ℚ) * (c : ℚ)) * h1
    constructor <;> linarith
  rw [hB]
  -- a local equation of `H` at the image of the generic point of `Γ`
  obtain ⟨U, hU, e, he⟩ := hH (f Γ.genericPoint)
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  obtain ⟨h, -, hh⟩ := exists_divisorialSectionValue_eq he (a * c) φ
  have hMΓ := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hM he Γ hU (univComponent R)
  set v := MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
    ((e : RationalFunctions R)) with hv
  have hv0 : v ≠ 0 := (e.isUnit.map _).ne_zero
  have hinv : _ = v⁻¹ ^ (a * c) := evalFF_inv_pow e (a * c)
  rw [hinv] at hh
  haveI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨Γ.genericPoint, hU⟩⟩
  have hgh : g = X.germToFunctionField (f ⁻¹ᵁ U) (f.appLE U (f ⁻¹ᵁ U) le_rfl h) *
      (functionFieldMap f v)⁻¹ ^ (a * c) := by
    rw [hg, hh, map_mul, MMP.Spreading.functionFieldMap_germToFunctionField f U (f ⁻¹ᵁ U) le_rfl, map_pow,
      map_inv₀]
  have hfu0 : functionFieldMap f v ≠ 0 := (map_ne_zero _).mpr hv0
  have hh0 : X.germToFunctionField (f ⁻¹ᵁ U) (f.appLE U (f ⁻¹ᵁ U) le_rfl h) ≠ 0 := by
    intro h0
    apply hg0
    rw [hgh, h0, zero_mul]
  rw [hgh, Scheme.ord_mul hh0 (pow_ne_zero _ (inv_ne_zero hfu0)),
    MMP.Flips.ord_inv_pow hfu0, ← hMΓ]
  have := ord_germToFunctionField_nonneg Γ hU (f.appLE U (f ⁻¹ᵁ U) le_rfl h)
  push_cast
  nlinarith

/-- A function on `U` invertible on its basic open has order zero along every prime divisor
meeting that basic open. -/
private theorem ord_germToFunctionField_eq_zero {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : Mori.PrimeDivisor Y) {U : Y.Opens} [Nonempty U]
    (s : Γ(Y, U)) (hE : (E.support ∩ (Y.basicOpen s : Set Y)).Nonempty) :
    Y.ord (Y.germToFunctionField U s) E.genericPoint = 0 := by
  obtain ⟨y, hyE, hys⟩ := hE
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
  have hgen : E.genericPoint ∈ Y.basicOpen s :=
    ((Y.basicOpen s).isOpen.stableUnderGeneralization)
      (specializes_iff_mem_closure.mpr hyE) hys
  have hgU : E.genericPoint ∈ U := Y.basicOpen_le s hgen
  have hu : IsUnit (Y.presheaf.germ U E.genericPoint hgU s) :=
    (Y.mem_basicOpen s E.genericPoint hgU).mp hgen
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hgU s]
  exact Mori.PrimeDivisor.ord_algebraMap_of_isUnit E hu

/-- **Pull-backs of local generators generate.** In the setting of
`pullback_smul_formPow_mem_logPluricanonicalSections`, if `φ = h · e^{-ac}` on `U` for a local
equation `e` of `H`, then `f^*φ · w^{⊗ akc}` generates `𝒪_X(akc(K_X + B))` over the preimage of
the basic open of `h`. -/
private theorem generatesOn_pullback_smul_formPowR
    {X R : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R]
    (f : X ⟶ R) [IsDominant f] {H : Divisor R}
    {hfH : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ H.supp}
    {M : Divisor X} (hM : H.IsPullback f hfH M) {K : Divisor X} {B : QDivisor X} {k c a : ℕ}
    {u : X.functionField} (hu0 : u ≠ 0)
    (hMu : ∀ Γ : Mori.PrimeDivisor X,
      (X.ord u Γ.genericPoint : ℚ) = M.coeff Γ - k * (K.coeff Γ + B.coeff Γ))
    (w : letI := functionFieldAlgebra sX; ⋀[X.functionField]^(n + 1) Ω[X.functionField⁄ℂ])
    (hw : ∀ N : ℕ, 0 < N → formPowR sX w N ≠ 0 ∧
      ∀ Γ : Mori.PrimeDivisor X, Γ.ordForm (formPowR sX w N) = N * K.coeff Γ)
    (hN : 0 < a * (k * c)) (φ : Γ(((a * c) • H).divisorialSheaf, ⊤))
    {U : R.Opens} [Nonempty U] {e : (RationalFunctions R)ˣ} (he : H.IsLocalEquation U e)
    (h : Γ(R, U))
    (hφ : divisorialSectionValue φ = R.germToFunctionField U h *
      MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
        (((e ^ (a * c))⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R))
    {x : X} (hx : f x ∈ R.basicOpen h) :
    letI := functionFieldAlgebra sX
    GeneratesOn B (a * (k * c)) (f ⁻¹ᵁ R.basicOpen h)
      ((functionFieldMap f (divisorialSectionValue φ) * u ^ (a * c)) •
        formPowR sX w (a * (k * c))) := by
  letI := functionFieldAlgebra sX
  have hxU : f x ∈ U := R.basicOpen_le h hx
  haveI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hxU⟩⟩
  set v := MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
    ((e : RationalFunctions R)) with hv
  have hv0 : v ≠ 0 := (e.isUnit.map _).ne_zero
  have hinv : _ = v⁻¹ ^ (a * c) := evalFF_inv_pow e (a * c)
  set g := functionFieldMap f (divisorialSectionValue φ) with hg
  set h' := f.appLE U (f ⁻¹ᵁ U) le_rfl h with hh'
  have hgh : g = X.germToFunctionField (f ⁻¹ᵁ U) h' * (functionFieldMap f v)⁻¹ ^ (a * c) := by
    rw [hg, hφ, hinv, map_mul,
      MMP.Spreading.functionFieldMap_germToFunctionField f U (f ⁻¹ᵁ U) le_rfl, map_pow, map_inv₀]
  have hfu0 : functionFieldMap f v ≠ 0 := (map_ne_zero _).mpr hv0
  have hbo : X.basicOpen h' = f ⁻¹ᵁ R.basicOpen h := by
    rw [hh', Scheme.basicOpen_appLE]
    exact inf_eq_right.mpr (f.preimage_mono (R.basicOpen_le h))
  have hh0 : X.germToFunctionField (f ⁻¹ᵁ U) h' ≠ 0 := by
    have hxb : x ∈ X.basicOpen h' := by rwa [hbo]
    have hunit := (X.mem_basicOpen h' x (X.basicOpen_le h' hxb)).mp hxb
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (X.basicOpen_le h' hxb) h']
    exact (hunit.map _).ne_zero
  have hg0 : g ≠ 0 := by
    rw [hgh]
    exact mul_ne_zero hh0 (pow_ne_zero _ (inv_ne_zero hfu0))
  have hgu0 : g * u ^ (a * c) ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ hu0)
  refine ⟨smul_ne_zero hgu0 (hw _ hN).1, fun Γ hΓ => ?_⟩
  rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hdim hgu0 (hw _ hN).1, (hw _ hN).2 Γ,
    Scheme.ord_mul hg0 (pow_ne_zero _ hu0), Scheme.ord_pow hu0]
  have hΓU : Γ.genericPoint ∈ f ⁻¹ᵁ U := by
    obtain ⟨y, hyΓ, hy⟩ := hΓ
    exact Mori.PrimeDivisor.genericPoint_mem_of_nonempty (E := Γ) ⟨y, hyΓ, f.preimage_mono
      (R.basicOpen_le h) hy⟩
  have hMΓ := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hM he Γ hΓU (univComponent R)
  have hord0 : X.ord (X.germToFunctionField (f ⁻¹ᵁ U) h') Γ.genericPoint = 0 :=
    ord_germToFunctionField_eq_zero Γ h' (by rwa [hbo])
  rw [hgh, Scheme.ord_mul hh0 (pow_ne_zero _ (inv_ne_zero hfu0)),
    MMP.Flips.ord_inv_pow hfu0, ← hMΓ, hord0]
  have h1 := hMu Γ
  push_cast
  linear_combination ((a : ℚ) * (c : ℚ)) * h1

/-- **Powers of Poincaré residues**, in coordinates: if `c w^{⊗m}` has residue `c₁ ω^{⊗m}` along
an adjunction step, then `c^a w^{⊗am}` has residue `c₁^a ω^{⊗am}` for every `a > 0`. -/
private theorem isPoincareResidue_smul_formPowR_pow {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFiniteType sY] [IsIntegral T]
    {j : T ⟶ Y} {BY : QDivisor Y} {BT : QDivisor T} (hj : IsAdjunctionStep sY BY j BT) {n m : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (w : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄ℂ])
    (c : Y.functionField)
    (ω : letI := functionFieldAlgebra (j ≫ sY); ⋀[T.functionField]^n Ω[T.functionField⁄ℂ])
    (c₁ : T.functionField)
    (h : IsPoincareResidue sY j n m (c • formPowR sY w m) (c₁ • formPowR (j ≫ sY) ω m)) :
    ∀ a, 0 < a → IsPoincareResidue sY j n (a * m) (c ^ a • formPowR sY w (a * m))
      (c₁ ^ a • formPowR (j ≫ sY) ω (a * m)) := by
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  intro a ha
  suffices H : ∀ N : ℕ, N = a * m → IsPoincareResidue sY j n N (c ^ a • formPowR sY w N)
      (c₁ ^ a • formPowR (j ≫ sY) ω N) from H _ rfl
  induction a, ha using Nat.le_induction with
  | base =>
    intro N hN
    rw [Nat.succ_eq_add_one, zero_add, one_mul] at hN
    subst hN
    simpa only [pow_one] using h
  | succ a ha ih =>
    intro N hN
    have hmul := IsPoincareResidue.mul hj hY (ih _ rfl) h
    rw [mul_smul_formPowR, mul_smul_formPowR, ← pow_succ, ← pow_succ] at hmul
    rw [Nat.succ_mul] at hN
    subst hN
    exact hmul

/-- **The residue of a pulled-back section.** Let `φ = h e^{-ar}` on `U` be a global section of
`𝒪_R(arH)`, `e` a local equation of `H` on `U`, and `T ⟶ X` an adjunction step whose generic
point lies over `U`. If the generator `f^*e^{-r} w^{⊗kr}` has residue `c₁ ω^{⊗kr}` along `T`,
then `f^*φ · w^{⊗akr}` has residue `h|_T · c₁^a ω^{⊗akr}`. -/
private theorem isPoincareResidue_pullback_smul_formPowR
    {X R : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R] (f : X ⟶ R) [IsDominant f]
    {B : QDivisor X} {T : Scheme.{0}} [IsIntegral T] {jT : T ⟶ X} {BT : QDivisor T}
    (hj : IsAdjunctionStep sX B jT BT) {D : Divisor R} {U : R.Opens} [Nonempty U]
    (hU : f (jT (genericPoint T)) ∈ U) {e : (RationalFunctions R)ˣ} {r a k : ℕ} (ha : 0 < a)
    (u : X.functionField)
    (w : letI := functionFieldAlgebra sX; ⋀[X.functionField]^(n + 1) Ω[X.functionField⁄ℂ])
    (φ : Γ(D.divisorialSheaf, ⊤)) (h : Γ(R, U))
    (hφ : divisorialSectionValue φ = R.germToFunctionField U h *
      (MMP.Threefold.Mori.Helpers.evalFF (univComponent R) (e : RationalFunctions R))⁻¹ ^ (a * r))
    (ω : letI := functionFieldAlgebra (jT ≫ sX); ⋀[T.functionField]^n Ω[T.functionField⁄ℂ])
    (c₁ : T.functionField)
    (hρ : IsPoincareResidue sX jT n (k * r)
      (((functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
        (e : RationalFunctions R)))⁻¹ * u) ^ r • formPowR sX w (k * r))
      (c₁ • formPowR (jT ≫ sX) ω (k * r))) :
    haveI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨_, hU⟩⟩
    IsPoincareResidue sX jT n (a * (k * r))
      ((functionFieldMap f (divisorialSectionValue φ) * u ^ (a * r)) • formPowR sX w (a * (k * r)))
      (((jT.stalkMap (genericPoint T)).hom (X.presheaf.germ (f ⁻¹ᵁ U) (jT (genericPoint T)) hU
        (f.appLE U (f ⁻¹ᵁ U) le_rfl h)) * c₁ ^ a) • formPowR (jT ≫ sX) ω (a * (k * r))) := by
  haveI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨_, hU⟩⟩
  letI := functionFieldAlgebra sX
  have hY : topologicalKrullDim X = n + 1 := by rw [hdim]; norm_cast
  have hpow := isPoincareResidue_smul_formPowR_pow hj hY w _ ω c₁ hρ a ha
  have hres := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hpow
    (X.presheaf.germ (f ⁻¹ᵁ U) (jT (genericPoint T)) hU (f.appLE U (f ⁻¹ᵁ U) le_rfl h))
  have hg : functionFieldMap f (divisorialSectionValue φ) * u ^ (a * r) =
      algebraMap (X.presheaf.stalk (jT (genericPoint T))) X.functionField
        (X.presheaf.germ (f ⁻¹ᵁ U) (jT (genericPoint T)) hU (f.appLE U (f ⁻¹ᵁ U) le_rfl h)) *
      (((functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
        (e : RationalFunctions R)))⁻¹ * u) ^ r) ^ a := by
    rw [hφ, map_mul, MMP.Spreading.functionFieldMap_germToFunctionField f U (f ⁻¹ᵁ U) le_rfl,
      map_pow, map_inv₀, ← pow_mul, mul_comm r a, mul_pow, mul_assoc]
    congr 1
    exact (Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hU _).symm
  rw [hg, mul_smul, mul_smul]
  exact hres

/-- **Coordinates of a pulled-back section.** Let `a` freely generate the invertible module `E`
over `U`, and `φ = h a` on `U` a global section. If the pull-back of `φ` along `ι : Z ⟶ Y` is
`g · ι^*a` on `ι⁻¹U`, then `g = ι^♯ h`. -/
private theorem eq_app_of_unit_app_eq {Y Z : Scheme.{0}} (ι : Z ⟶ Y) (E : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y E] {U : Y.Opens} {a : Γ(E, U)}
    (ha : IsLocalGenerator E U a) (φ : Γ(E, ⊤)) (h : Γ(Y, U))
    (hh : h • E.presheaf.map (homOfLE le_rfl).op a = E.presheaf.map (homOfLE le_top).op φ)
    (g : Γ(Z, ι ⁻¹ᵁ U))
    (hg : ((Scheme.Modules.pullback ι ⋙ Scheme.Modules.pushforward ι).obj E).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app E).app ⊤ φ) =
      (show Γ((Scheme.Modules.pullback ι).obj E, ι ⁻¹ᵁ U) from
        g • (show Γ((Scheme.Modules.pullback ι).obj E, ι ⁻¹ᵁ U) from
          ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app E).app U a))) :
    g = ι.app U h := by
  set η := (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app E
  have hnat : ∀ {V W : Y.Opens} (i : V ⟶ W) (x : Γ(E, W)),
      η.app V (E.presheaf.map i.op x) =
        ((Scheme.Modules.pullback ι ⋙ Scheme.Modules.pushforward ι).obj E).presheaf.map i.op
          (η.app W x) := fun i x =>
    congrArg (fun F => F x) (η.mapPresheaf.naturality i.op)
  have h1 := hnat (homOfLE (le_top : U ≤ ⊤)) φ
  rw [← hh, Scheme.Modules.Hom.app_smul, hnat, hg] at h1
  have hgen := isLocalGenerator_pullback_unit ι E ha (ι ⁻¹ᵁ U) le_rfl
  have e0 : ∀ x : Γ((Scheme.Modules.pullback ι ⋙ Scheme.Modules.pushforward ι).obj E, U),
      ((Scheme.Modules.pullback ι ⋙ Scheme.Modules.pushforward ι).obj E).presheaf.map
        (homOfLE (le_refl U)).op x = x := by
    intro x
    rw [show homOfLE (le_refl U) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  have e1 : ∀ x : Γ((Scheme.Modules.pullback ι).obj E, ι ⁻¹ᵁ U),
      ((Scheme.Modules.pullback ι).obj E).presheaf.map (homOfLE (le_refl (ι ⁻¹ᵁ U))).op x = x := by
    intro x
    rw [show homOfLE (le_refl (ι ⁻¹ᵁ U)) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [e0] at h1
  apply hgen.1
  show g • _ = (ι.app U h) • _
  exact ((congrArg (fun y => g • y) (e1 (η.app U a))).trans h1.symm).trans
    (congrArg (fun y => (ι.app U h) • y) (e1 (η.app U a))).symm

/-! ### Small facts about the contraction -/

/-- A morphism inducing isomorphisms on all rings of sections is dominant: an open set missing
the image would have no sections upstairs. -/
private theorem isDominant_of_forall_isIso_app {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) : IsDominant f := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq]
  by_contra hne
  set U : Y.Opens := ⟨(closure (Set.range f.base))ᶜ, isClosed_closure.isOpen_compl⟩
  have hU : (U : Set Y).Nonempty := Set.nonempty_compl.mpr hne
  haveI : Nonempty U := hU.to_subtype
  have hpre : f ⁻¹ᵁ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact hx (subset_closure (Set.mem_range_self x))
  haveI : Subsingleton Γ(X, f ⁻¹ᵁ U) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hpre)
  haveI : Subsingleton Γ(Y, U) :=
    (asIso (f.app U)).commRingCatIsoToRingEquiv.injective.subsingleton
  exact not_subsingleton Γ(Y, U) inferInstance

/-- Two equal morphisms have the same stalk maps on germs. -/
private theorem stalkMap_germ_eq_of_eq {A C : Scheme.{0}} {g g' : A ⟶ C} (hgg : g = g')
    (U : C.Opens) (x : A) (hx : g x ∈ U) (hx' : g' x ∈ U) (h : Γ(C, U)) :
    (g.stalkMap x).hom (C.presheaf.germ U (g x) hx h) =
      (g'.stalkMap x).hom (C.presheaf.germ U (g' x) hx' h) := by
  subst hgg
  rfl

/-- **The value of a pulled-back function at a point does not depend on the factorization.** -/
private theorem stalkMap_germ_app_eq {A B B' C : Scheme.{0}} (α : A ⟶ B) (β : B ⟶ C)
    (α' : A ⟶ B') (β' : B' ⟶ C) (hαβ : α ≫ β = α' ≫ β') (U : C.Opens) (x : A)
    (hx : α x ∈ β ⁻¹ᵁ U) (hx' : α' x ∈ β' ⁻¹ᵁ U) (h : Γ(C, U)) :
    (α.stalkMap x).hom (B.presheaf.germ (β ⁻¹ᵁ U) (α x) hx (β.app U h)) =
      (α'.stalkMap x).hom (B'.presheaf.germ (β' ⁻¹ᵁ U) (α' x) hx' (β'.app U h)) := by
  have l1 := (Scheme.Hom.germ_stalkMap_apply α (β ⁻¹ᵁ U) x hx (β.app U h)).trans
    (Scheme.Hom.germ_stalkMap_apply (α ≫ β) U x hx h).symm
  have l2 := (Scheme.Hom.germ_stalkMap_apply α' (β' ⁻¹ᵁ U) x hx' (β'.app U h)).trans
    (Scheme.Hom.germ_stalkMap_apply (α' ≫ β') U x hx' h).symm
  exact l1.trans ((stalkMap_germ_eq_of_eq hαβ U x hx hx' h).trans l2.symm)

section Setup

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {B : QDivisor X}
  {C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0}}
  [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
  {j : ∀ P, C P ⟶ X} {BC : ∀ P, QDivisor (C P)} {m : ℕ}

variable (sX j BC) in
/-- `s`, a rational `am`-canonical form on `X`, lifts the `a`-th power of the floor system `t`
(in degree `m`): along every floor `j_P`, if `t_P = c · ω^{⊗m}` then the Poincaré residue of `s` is
`c^a · ω^{⊗am}`. -/
private def LiftsPow (t : ∀ P, logPluricanonicalSections (j P ≫ sX) n m (BC P)) (a : ℕ)
    (s : RationalPluriForms sX (n + 1) ((a * m : ℕ) : ℤ)) : Prop :=
  ∀ P, letI := functionFieldAlgebra (j P ≫ sX)
    ∀ (ω : ⋀[(C P).functionField]^n Ω[(C P).functionField⁄ℂ]) (c : (C P).functionField),
      (t P : RationalPluriForms (j P ≫ sX) n m) =
          c • (formPow ω m : RationalPluriForms (j P ≫ sX) n m) →
        IsPoincareResidue sX (j P) n (a * m) s
          (c ^ a • (formPow ω (a * m) : RationalPluriForms (j P ≫ sX) n ((a * m : ℕ) : ℤ)))

/-- **Lifts of an admissible floor system are preadmissible.** A section of `am(K_X + B)` whose
Poincaré residue along every floor component is the `a`-th power of one admissible floor system is
preadmissible. -/
private theorem mem_preadmissibleSections_of_liftsPow [CompactSpace X]
    (hX : Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    (hC : ∀ P, IsAdjunctionStep sX B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X))
    (RS : ResidueRestriction (fun P => j P ≫ sX) BC n m)
    {t : ∀ P, logPluricanonicalSections (j P ≫ sX) n m (BC P)} (ht : t ∈ admissibleSections RS)
    {a : ℕ} (RX : ResidueRestriction (fun _ : Unit => sX) (fun _ => B) (n + 1) (a * m))
    (s : ∀ _ : Unit, logPluricanonicalSections sX (n + 1) (a * m) B)
    (hs : LiftsPow sX j BC t a (s () : RationalPluriForms sX (n + 1) ((a * m : ℕ) : ℤ))) :
    s ∈ preadmissibleSections RX := by
  classical
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  have ha0 : 0 < a := Nat.pos_of_mul_pos_right RX.setting.pos
  have hcanX : ∀ {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
      (F : StratumAdjunctionData sX B ι BS),
      haveI := F.isIntegral_stratum
      haveI := F.isNormal_stratum
      haveI := F.isLocallyNoetherian_stratum
      ∃ (d : ℕ) (K : Divisor S), K.IsCanonicalDivisor (ι ≫ sX) d ∧
        (Divisor.toQDivisor K + BS).IsQCartier := by
    intro S ι BS F
    obtain ⟨d, K, hK, hKC⟩ := RX.setting.isCartierDivisor () F
    exact ⟨d, K, hK, ⟨((a * m : ℕ) : ℤ), by exact_mod_cast RX.setting.pos.ne', hKC⟩⟩
  intro i i' S S' ι ι' BS BS' F F' e h₁ h₂ hdS hdS' σ hσ
  cases i
  cases i'
  change StratumAdjunctionData sX B ι BS at F
  change StratumAdjunctionData sX B ι' BS' at F'
  haveI := F.isIntegral_stratum
  haveI := F.isNormal_stratum
  haveI := F.isLocallyNoetherian_stratum
  haveI := F'.isIntegral_stratum
  haveI := F'.isNormal_stratum
  haveI := F'.isLocallyNoetherian_stratum
  haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι' ≫ sX) := F'.isNormalVariety.1.toLocallyOfFiniteType
  obtain ⟨P, S₁, ι₁, BS₁, F₁, ψ, hl₁, -, -, hrest₁⟩ := exists_flagMatch hX hdim hC RS hcanX F h₁
  obtain ⟨P', S₂, ι₂, BS₂, F₂, ψ', hl₂, -, -, hrest₂⟩ :=
    exists_flagMatch hX hdim hC RS hcanX F' h₂
  haveI := F₁.isIntegral_stratum
  haveI := F₁.isNormal_stratum
  haveI := F₁.isLocallyNoetherian_stratum
  haveI := F₂.isIntegral_stratum
  haveI := F₂.isNormal_stratum
  haveI := F₂.isLocallyNoetherian_stratum
  haveI : LocallyOfFiniteType (ι₁ ≫ j P ≫ sX) := F₁.isNormalVariety.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι₂ ≫ j P' ≫ sX) := F₂.isNormalVariety.1.toLocallyOfFiniteType
  obtain ⟨σψ, -, hσψc, hres⟩ := hrest₁
  obtain ⟨σψ', -, hσψc', hres'⟩ := hrest₂
  -- the matched strata have dimension `e`
  have hdim₁ : ∀ (Q : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}) {T : Scheme.{0}}
      {ιT : T ⟶ C Q} {BT : QDivisor T} (G : StratumAdjunctionData (j Q ≫ sX) (BC Q) ιT BT)
      {T₀ : Scheme.{0}} {ι₀ : T₀ ⟶ X} {B₀ : QDivisor T₀} (G₀ : StratumAdjunctionData sX B ι₀ B₀),
      G.length + 1 = G₀.length → topologicalKrullDim T₀ = e →
      haveI := G.isIntegral_stratum
      topologicalKrullDim T = e := by
    intro Q T ιT BT G T₀ ι₀ B₀ G₀ hl hT₀
    haveI := G.isIntegral_stratum
    haveI : LocallyOfFiniteType (ιT ≫ j Q ≫ sX) := G.isNormalVariety.1.toLocallyOfFiniteType
    have e1 := StratumAdjunctionData.dim_add_length (sX := sX) hdim G₀ hT₀
    have e2 := StratumAdjunctionData.dim_add_length (sX := j Q ≫ sX)
      (RS.setting.topologicalKrullDim_eq Q) G (topologicalKrullDim_eq_toNat_trdeg (ιT ≫ j Q ≫ sX))
    rw [topologicalKrullDim_eq_toNat_trdeg (ιT ≫ j Q ≫ sX)]
    congr 1
    norm_cast
    omega
  have hdS₁ : topologicalKrullDim S₁ = e := hdim₁ P F₁ F hl₁ hdS
  have hdS₂ : topologicalKrullDim S₂ = e := hdim₁ P' F₂ F' hl₂ hdS'
  -- the residue of `s` along `F` is read off the residue of `t_P` along `F₁`
  have hread : ∀ (Q : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}) {T : Scheme.{0}}
      {ιT : T ⟶ C Q} {BT : QDivisor T} (G : StratumAdjunctionData (j Q ≫ sX) (BC Q) ιT BT)
      {T₀ : Scheme.{0}} {ι₀ : T₀ ⟶ X} {B₀ : QDivisor T₀} (G₀ : StratumAdjunctionData sX B ι₀ B₀),
      haveI := G.isIntegral_stratum
      haveI := G₀.isIntegral_stratum
      topologicalKrullDim T = e → topologicalKrullDim T₀ = e →
      ∀ (τ : FunctionFieldEquiv (ι₀ ≫ sX) (ιT ≫ j Q ≫ sX)),
      (∀ (N : ℕ) (ζ : RationalPluriForms sX (n + 1) N) (ρQ : RationalPluriForms (j Q ≫ sX) n N),
        IsPoincareResidue sX (j Q) n N ζ ρQ → ∀ (e' : ℕ), topologicalKrullDim T₀ = e' →
        ∀ ρ' : RationalPluriForms (ιT ≫ j Q ≫ sX) e' N, IsIteratedResidueRec ρQ G e' ρ' →
          IsIteratedResidueRec ζ G₀ e' (pluriformPullback (ι₀ ≫ sX) (ιT ≫ j Q ≫ sX) τ.toHom e' N ρ')) →
      letI := functionFieldAlgebra (ιT ≫ j Q ≫ sX)
      ∀ (b : Module.Basis Unit T.functionField (⋀[T.functionField]^e Ω[T.functionField⁄ℂ]))
        (c₁ : T.functionField),
        RS.toFun Q G e (t Q) = c₁ • (formPow (b ()) m : RationalPluriForms (ιT ≫ j Q ≫ sX) e m) →
        RX.toFun () G₀ e (s ()) = pluriformPullback (ι₀ ≫ sX) (ιT ≫ j Q ≫ sX) τ.toHom e
          ((a * m : ℕ) : ℤ) (c₁ ^ a • (formPow (b ()) (a * m) :
            RationalPluriForms (ιT ≫ j Q ≫ sX) e ((a * m : ℕ) : ℤ))) := by
    intro Q T ιT BT G T₀ ι₀ B₀ G₀ hT hT₀ τ hresG b c₁ hc₁
    haveI := G.isIntegral_stratum
    haveI := G₀.isIntegral_stratum
    letI := functionFieldAlgebra (j Q ≫ sX)
    letI := functionFieldAlgebra (ιT ≫ j Q ≫ sX)
    haveI : LocallyOfFiniteType (j Q ≫ sX) :=
      (RS.setting.isPair Q).isPair.isNormalVariety.1.toLocallyOfFiniteType
    obtain ⟨b₀⟩ := exists_basis_topForms (sX := j Q ≫ sX) (RS.setting.topologicalKrullDim_eq Q)
    set c := (ZTensorPower.basis b₀ m).repr (t Q : RationalPluriForms (j Q ≫ sX) n m) ()
    have htQ : (t Q : RationalPluriForms (j Q ≫ sX) n m) = c • formPow (b₀ ()) m :=
      eq_repr_smul_formPow b₀ _
    have hIt := (RS.isIteratedResidue Q G e (t Q) hT).rec'
    rw [hc₁, htQ] at hIt
    have hpow := isIteratedResidueRec_pow (b₀ ()) c G hT (b ()) c₁ hIt a ha0
    have hsQ := hs Q (b₀ ()) c htQ
    have h1 := hresG (a * m) (s ()) _ hsQ e hT₀ _ hpow
    exact IsIteratedResidueRec.unique G₀ (RX.isIteratedResidue () G₀ e (s ()) hT₀).rec' h1
  letI := functionFieldAlgebra (ι₁ ≫ j P ≫ sX)
  letI := functionFieldAlgebra (ι₂ ≫ j P' ≫ sX)
  obtain ⟨b₁⟩ := exists_basis_topForms (sX := ι₁ ≫ j P ≫ sX) hdS₁
  obtain ⟨b₂⟩ := exists_basis_topForms (sX := ι₂ ≫ j P' ≫ sX) hdS₂
  set c₁ := (ZTensorPower.basis b₁ m).repr (RS.toFun P F₁ e (t P)) ()
  set c₂ := (ZTensorPower.basis b₂ m).repr (RS.toFun P' F₂ e (t P')) ()
  have hc₁ : RS.toFun P F₁ e (t P) =
      c₁ • (formPow (b₁ ()) m : RationalPluriForms (ι₁ ≫ j P ≫ sX) e m) :=
    eq_repr_smul_formPow b₁ _
  have hc₂ : RS.toFun P' F₂ e (t P') =
      c₂ • (formPow (b₂ ()) m : RationalPluriForms (ι₂ ≫ j P' ≫ sX) e m) :=
    eq_repr_smul_formPow b₂ _
  beta_reduce
  rw [hread P F₁ F hdS₁ hdS σψ hres b₁ c₁ hc₁, hread P' F₂ F' hdS₂ hdS' σψ' hres' b₂ c₂ hc₂]
  -- the crepant map `σ̃ = σψ⁻¹ ∘ σ ∘ σψ'` between the matched strata
  letI := functionFieldAlgebra (ι ≫ sX)
  letI := functionFieldAlgebra (ι' ≫ sX)
  set σt : FunctionFieldEquiv (ι₁ ≫ j P ≫ sX) (ι₂ ≫ j P' ≫ sX) := σψ'.trans (σ.trans σψ.symm)
  have hσt : IsCrepantBirationalMap (ι₁ ≫ j P ≫ sX) (ι₂ ≫ j P' ≫ sX) BS₁ BS₂ σt :=
    (hσψc.symm.trans hσ).trans hσψc'
  have hadm := ht P P' F₁ F₂ e (Nat.zero_le _) (Nat.zero_le _) hdS₁ hdS₂ σt hσt
  beta_reduce at hadm
  rw [hc₁, hc₂, pluriformPullback_smul_formPow' hdS₁ hdS₂ σt.toHom (b₂ ()) m c₂] at hadm
  have hpw : (c₁ ^ a • (formPow (b₁ ()) (a * m) :
      RationalPluriForms (ι₁ ≫ j P ≫ sX) e ((a * m : ℕ) : ℤ))) =
      pluriformPullback (ι₁ ≫ j P ≫ sX) (ι₂ ≫ j P' ≫ sX) σt.toHom e ((a * m : ℕ) : ℤ)
        (c₂ ^ a • (formPow (b₂ ()) (a * m) :
          RationalPluriForms (ι₂ ≫ j P' ≫ sX) e ((a * m : ℕ) : ℤ))) := by
    rw [pluriformPullback_smul_formPow' hdS₁ hdS₂ σt.toHom (b₂ ()) (a * m) (c₂ ^ a),
      map_pow (σt.toHom) c₂ a]
    exact (smul_formPow_pow_eq b₁ hadm a).symm
  have key : ∀ y : RationalPluriForms (ι₂ ≫ j P' ≫ sX) e ((a * m : ℕ) : ℤ),
      pluriformPullback (ι ≫ sX) (ι' ≫ sX) σ.toHom e ((a * m : ℕ) : ℤ)
        (pluriformPullback (ι' ≫ sX) (ι₂ ≫ j P' ≫ sX) σψ'.toHom e ((a * m : ℕ) : ℤ) y) =
      pluriformPullback (ι ≫ sX) (ι₁ ≫ j P ≫ sX) σψ.toHom e ((a * m : ℕ) : ℤ)
        (pluriformPullback (ι₁ ≫ j P ≫ sX) (ι₂ ≫ j P' ≫ sX) σt.toHom e ((a * m : ℕ) : ℤ) y) := by
    intro y
    have hh : (σ.toHom).comp (σψ'.toHom) = (σψ.toHom).comp (σt.toHom) := by
      ext x
      change σ (σψ' x) = σψ (σψ.symm (σ (σψ' x)))
      rw [AlgEquiv.apply_symm_apply]
    rw [pluriformPullback_comp hdS hdS' hdS₂, pluriformPullback_comp hdS hdS₁ hdS₂, hh]
  rw [hpw]
  exact key _

end Setup

/-- Over the spectrum of a field, relative ampleness is ampleness. -/
private theorem isAmple_of_isRelativelyAmple_spec {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N]
    (h : MMP.Mori.IsRelativelyAmple s N) : Stacks.Ample.IsAmple X N := by
  obtain ⟨V, -, hyV, hA⟩ := h (IsLocalRing.closedPoint _)
  have hV : V = ⊤ := TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun z => by
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint _)])
  subst hV
  have : IsIso (s ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens)).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact Stacks.RelativeAmpleAffineBase.isAmple_of_isAmple_modulePullback _ N hA

/-- `𝒪(mA) ≅ 𝒪(A)^{⊗ m}` for a Cartier divisor `A`. -/
private noncomputable def divisorialSheafNsmulIso {V : Scheme.{u}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] {A : Divisor V} (hA : A.IsCartier) (m : ℕ) :
    haveI := hA.isInvertibleModule_divisorialSheaf
    (m • A).divisorialSheaf ≅ Stacks.Ample.tensorPowModule V A.divisorialSheaf (m : ℤ) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  induction m with
  | zero =>
    exact eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso ≪≫
      (Stacks.Ample.tensorPowModuleZeroIso V A.divisorialSheaf).symm
  | succ n ih =>
    exact eqToIso (by rw [succ_nsmul]) ≪≫
      ((hA.nsmul n).divisorialSheafTensorIso hA).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso ih).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso V A.divisorialSheaf).symm ≪≫
      Stacks.Ample.tensorPowModuleAddIso V A.divisorialSheaf (n : ℤ) 1 ≪≫
      eqToIso (by push_cast; rfl)

/-- An isomorphism of modules is surjective on sections. -/
private theorem surjective_app_of_isIso {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [IsIso f]
    (U : X.Opens) : Function.Surjective (f.app U) := fun y =>
  ⟨(inv f).app U y, by
    have := congrArg (fun φ : N ⟶ N => φ.app U y) (IsIso.inv_hom_id f)
    simpa using this⟩

/-- An isomorphism of modules is injective on sections. -/
private theorem injective_app_of_isIso {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [IsIso f]
    (U : X.Opens) : Function.Injective (f.app U) := fun a b hab => by
  have h := congrArg ((inv f).app U) hab
  have e : ∀ x, (inv f).app U (f.app U x) = x := fun x => by
    have := congrArg (fun φ : M ⟶ M => φ.app U x) (IsIso.hom_inv_id f)
    simpa using this
  rwa [e, e] at h

/-- `e.hom` undoes `e.inv` on sections. -/
private theorem inv_hom_id_app_apply {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (x : Γ(N, U)) : e.hom.app U (e.inv.app U x) = x := by
  have := congrArg (fun φ : N ⟶ N => φ.app U x) e.inv_hom_id
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] at this
  exact this

/-- `e.inv` undoes `e.hom` on sections. -/
private theorem hom_inv_id_app_apply {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (x : Γ(M, U)) : e.inv.app U (e.hom.app U x) = x := by
  have := congrArg (fun φ : M ⟶ M => φ.app U x) e.hom_inv_id
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] at this
  exact this

/-- Surjectivity on sections is stable under composition. -/
private theorem surjective_app_comp {X : Scheme.{u}} {M N P : X.Modules} {f : M ⟶ N} {g : N ⟶ P}
    (U : X.Opens) (hf : Function.Surjective (f.app U)) (hg : Function.Surjective (g.app U)) :
    Function.Surjective ((f ≫ g).app U) := by
  have : ⇑((f ≫ g).app U) = (g.app U) ∘ (f.app U) := by
    funext x; simp
  rw [this]; exact hg.comp hf

open CategoryTheory.Limits in
/-- The ideal sheaf `ker(𝒪_R → ι_*𝒪_Z)` of a closed subscheme of a locally Noetherian scheme is
coherent. -/
private theorem isCoherent_kernel_unitToPushforwardStructureSheaf {R Z : Scheme.{0}}
    [IsLocallyNoetherian R] (ιZ : Z ⟶ R) [IsClosedImmersion ιZ] :
    (kernel (Stacks.AffineClosedUnion.unitToPushforwardStructureSheaf ιZ)).IsCoherent := by
  haveI : (Stacks.AlgebraicGeometry.PicardBaseChange.unitModule R).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent R
  haveI : (Stacks.Morphisms.pushforwardStructureSheaf ιZ).IsCoherent :=
    ClosedImmersionCoherentImage.isCoherent_pushforward_unit ιZ
  exact _root_.SheafOfModules.kernel_isCoherent _

open CategoryTheory.Limits in
/-- **The twisted ideal sheaf sequence.** For a closed immersion `ι : Z ⟶ R` with ideal sheaf
`ℐ_Z` and an invertible module `T`, the sequence `0 → ℐ_Z ⊗ T → 𝒪_R ⊗ T → ι_*𝒪_Z ⊗ T → 0` is
exact. -/
private theorem shortExact_twist_idealSheafSequence {R Z : Scheme.{0}} (ιZ : Z ⟶ R)
    [IsClosedImmersion ιZ] (T : R.Modules) [Stacks.Ample.IsInvertibleModule R T] :
    ((ShortComplex.mk (kernel.ι (Stacks.AffineClosedUnion.unitToPushforwardStructureSheaf ιZ)) _
      (kernel.condition _)).map (Stacks.AffineClosedUnion.twistFunctor R T)).ShortExact := by
  set q := Stacks.AffineClosedUnion.unitToPushforwardStructureSheaf ιZ
  have hS : (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel q)
      mono_f := inferInstanceAs (Mono (kernel.ι q))
      epi_g := Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion
        ιZ }
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible R.toRingedSpace.presheaf
      (structureSheafRing R.toRingedSpace).property T :=
    Stacks.ProjectionFormula.isInvertible_of_isInvertibleModule R T
  haveI : (Stacks.AffineClosedUnion.twistFunctor R T).IsEquivalence :=
    Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence
      R.toRingedSpace.presheaf (structureSheafRing R.toRingedSpace).property T
  exact hS.map_of_exact _

open CategoryTheory.Limits in
/-- **Serre lifting through a closed immersion.** On a projective variety `R` over `ℂ` with an
ample Cartier divisor `H`, for every closed subscheme `ι : Z ⟶ R` the pull-back of global sections
`Γ(R, 𝒪_R(qH)) → Γ(Z, ι^*𝒪_R(qH))` is surjective for all large `q`. -/
private theorem exists_forall_surjective_unit_app_top {R Z : Scheme.{0}} [IsIntegral R]
    [IsLocallyNoetherian R] [IsNormal R] [CompactSpace R] {sR : R ⟶ Spec (.of ℂ)}
    (hRp : Mori.IsProjectiveVariety ℂ sR) {H : Divisor R} (hH : H.IsCartier)
    (hHamp : H.IsRelativelyAmple sR hH) (ιZ : Z ⟶ R) [IsClosedImmersion ιZ] :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app
        (q • H).divisorialSheaf).app ⊤) := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  have hO : Stacks.Ample.IsAmple R H.divisorialSheaf :=
    isAmple_of_isRelativelyAmple_spec sR _ hHamp
  haveI : IsProper sR := (IsProjectiveMorphism.isProjective
    (IsProjectiveVariety.isProjective (k := ℂ) (f := sR))).isProper
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (ιZ ≫ sR)
  let q := Stacks.AffineClosedUnion.unitToPushforwardStructureSheaf ιZ
  haveI : (kernel q).IsCoherent := isCoherent_kernel_unitToPushforwardStructureSheaf ιZ
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist sR
      (kernel q) H.divisorialSheaf hO
  refine ⟨d₀, fun d hd => ?_⟩
  set T := Stacks.Ample.tensorPowModule R H.divisorialSheaf (d : ℤ)
  have hS' := shortExact_twist_idealSheafSequence ιZ T
  have hz := hd₀ d 1 hd Nat.one_pos
  have hzero := (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    R.ringCatSheaf ⊤ 1 _).mpr hz
  have hsurj := Stacks.Cohomology.surjective_sections_of_isZero_firstCohomology R ⊤ hS' hzero
  have hT : Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app T).app ⊤) := by
    rw [← Stacks.AffineClosedUnion.twistedUnit_eq_unit, Stacks.AffineClosedUnion.twistedUnit]
    refine surjective_app_comp _ (surjective_app_of_isIso _ _)
      (surjective_app_comp _ hsurj (surjective_app_of_isIso _ _))
  let e := divisorialSheafNsmulIso hH d
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.naturality e.hom
  have heq : (Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app (d • H).divisorialSheaf =
      e.hom ≫ (Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app T ≫
        (Scheme.Modules.pullback ιZ ⋙ Scheme.Modules.pushforward ιZ).map e.inv := by
    have h2 := congrArg
      (· ≫ (Scheme.Modules.pullback ιZ ⋙ Scheme.Modules.pushforward ιZ).map e.inv) hnat
    simp only [Functor.id_map, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id] at h2
    exact h2.symm
  rw [heq]
  exact surjective_app_comp _ (surjective_app_of_isIso _ _)
    (surjective_app_comp _ hT (surjective_app_of_isIso _ _))

open Opposite in
/-- **Generating sections are local generators.** If finitely many global sections `σᵢ`
generate `M`, then near every point `y` every section of `M` is an `𝒪`-linear combination of
the `σᵢ`. -/
private theorem exists_eq_sum_smul_of_generatingSections {X : Scheme.{0}} {M : X.Modules}
    (σ : M.GeneratingSections) [Fintype σ.I] {W : X.Opens} {y : X} (hy : y ∈ W)
    (κ : M.val.obj (op W)) :
    ∃ (W₁ : X.Opens) (_ : y ∈ W₁) (hW₁ : W₁ ≤ W) (ρ : σ.I → X.ringCatSheaf.obj.obj (op W₁)),
      M.val.map (homOfLE hW₁).op κ =
        ∑ i, ρ i • M.val.map (homOfLE le_top).op ((σ.s i).eval (op ⊤)) := by
  classical
  have hspan := (AlgebraicGeometry.generates_iff_stalkwise_generates X.ringCatSheaf M σ.s).mp
    σ.epi y
  have hmem := Submodule.mem_top (R := TopCat.Presheaf.stalk (C := RingCat) X.ringCatSheaf.obj y)
    (x := TopCat.Presheaf.germ M.val.presheaf W y hy κ)
  rw [← hspan] at hmem
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨r, hr⟩ := hmem
  choose Wi hyWi ρ' hρ' using fun i => TopCat.Presheaf.germ_exist X.ringCatSheaf.obj (r i)
  set W' : X.Opens := W ⊓ ⨅ i, Wi i with hW'
  have hyW' : y ∈ W' := by
    refine ⟨hy, ?_⟩
    change y ∈ ((⨅ i, Wi i : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hyWi
  have hW'i : ∀ i, W' ≤ Wi i := fun i => inf_le_right.trans (iInf_le _ i)
  have hW'W : W' ≤ W := inf_le_left
  set κ' : M.val.obj (op W') := ∑ i, X.ringCatSheaf.obj.map (homOfLE (hW'i i)).op (ρ' i) •
    M.val.map (homOfLE le_top).op ((σ.s i).eval (op ⊤)) with hκ'
  have hgerm : TopCat.Presheaf.germ M.val.presheaf W' y hyW' κ' =
      TopCat.Presheaf.germ M.val.presheaf W y hy κ := by
    rw [← hr, hκ']
    erw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (PresheafOfModules.germ_ringCat_smul M.val y W' hyW' _ _).trans ?_
    congr 1
    · rw [← hρ' i]
      exact TopCat.Presheaf.germ_res_apply X.ringCatSheaf.obj (homOfLE (hW'i i)) y hyW' (ρ' i)
    · exact TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE le_top) y hyW' _
  obtain ⟨W₁, hyW₁, i₁, i₂, heq⟩ := TopCat.Presheaf.germ_eq M.val.presheaf y hyW' hy κ' κ hgerm
  have hW₁W' : W₁ ≤ W' := i₁.le
  refine ⟨W₁, hyW₁, hW₁W'.trans hW'W, fun i => X.ringCatSheaf.obj.map
    (homOfLE (hW₁W'.trans (hW'i i))).op (ρ' i), ?_⟩
  have e2 : M.val.map (homOfLE (hW₁W'.trans hW'W)).op κ = M.val.presheaf.map i₂.op κ := rfl
  rw [e2, ← heq, hκ']
  erw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (PresheafOfModules.map_smul M.val i₁.op _ _).trans ?_
  congr 1
  · change (X.ringCatSheaf.obj.map (homOfLE (hW'i i)).op ≫ X.ringCatSheaf.obj.map i₁.op) (ρ' i) = _
    rw [← Functor.map_comp]
    rfl
  · change (M.val.presheaf.map (homOfLE le_top).op ≫ M.val.presheaf.map i₁.op) _ = _
    rw [← Functor.map_comp]
    rfl

open CategoryTheory.Limits Opposite in
/-- **Sections of `𝒪_R(qH)` vanishing on a closed subscheme.** On a projective variety `R` with an
ample Cartier divisor `H` and a closed subscheme `ι : Z ⟶ R`, for all large `q` every point `y`
off `Z` has a global section `φ` of `𝒪_R(qH)` restricting to zero on `Z` and generating at `y`:
`φ = h e^{-q}` near `y` for a local equation `e` of `H` and a function `h` invertible at `y`. This
is Serre's global generation of `ℐ_Z(qH)`. -/
private theorem exists_forall_exists_mem_basicOpen_of_notMem_range {R Z : Scheme.{0}}
    [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R] [CompactSpace R] {sR : R ⟶ Spec (.of ℂ)}
    (hRp : Mori.IsProjectiveVariety ℂ sR) {H : Divisor R} (hH : H.IsCartier)
    (hHamp : H.IsRelativelyAmple sR hH) (ιZ : Z ⟶ R) [IsClosedImmersion ιZ] :
    ∃ q₁ : ℕ, ∀ q : ℕ, q₁ ≤ q → ∀ y : R, y ∉ Set.range ιZ.base →
      ∃ φ : Γ((q • H).divisorialSheaf, ⊤),
        ((Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app
          (q • H).divisorialSheaf).app ⊤ φ = 0 ∧
        ∃ (U : R.Opens) (_ : Nonempty U) (e : (RationalFunctions R)ˣ) (_ : H.IsLocalEquation U e)
          (h : Γ(R, U)), y ∈ R.basicOpen h ∧
          divisorialSectionValue φ = R.germToFunctionField U h *
            MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
              (((e ^ q)⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R) := by
  classical
  haveI := hH.isInvertibleModule_divisorialSheaf
  have hO : Stacks.Ample.IsAmple R H.divisorialSheaf :=
    isAmple_of_isRelativelyAmple_spec sR _ hHamp
  haveI : IsProper sR := (IsProjectiveMorphism.isProjective
    (IsProjectiveVariety.isProjective (k := ℂ) (f := sR))).isProper
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (ιZ ≫ sR)
  let q := Stacks.AffineClosedUnion.unitToPushforwardStructureSheaf ιZ
  haveI : (kernel q).IsCoherent := isCoherent_kernel_unitToPushforwardStructureSheaf ιZ
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent (kernel q)
  obtain ⟨n₀, hn₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple
    H.divisorialSheaf hO (kernel q) hqc hft
  refine ⟨n₀.toNat, fun d hd y hy => ?_⟩
  obtain ⟨σ, hσfin⟩ := hn₀ (d : ℤ) (by omega)
  let T := Stacks.Ample.tensorPowModule R H.divisorialSheaf (d : ℤ)
  let σ' := Stacks.AlgebraicGeometry.ProperAmpleCohomology.generatingSectionsOfIso σ
    ((MMP.SemiampleSections.tensorRightIsoSheafTensorRight T).app (kernel q))
  haveI : Finite σ'.I := hσfin
  haveI : Fintype σ'.I := Fintype.ofFinite _
  have hS' := shortExact_twist_idealSheafSequence ιZ T
  set F := Stacks.AffineClosedUnion.twistFunctor R T with hF
  set D := (d • H).divisorialSheaf with hD
  let e := divisorialSheafNsmulIso hH d
  let ψ : F.obj (kernel q) ⟶ D :=
    F.map (kernel.ι q) ≫ (Stacks.AffineClosedUnion.twistUnitIso T).hom ≫ e.inv
  let κs : σ'.I → Γ(F.obj (kernel q), ⊤) := fun i => (σ'.s i).eval (op ⊤)
  let φ : σ'.I → Γ(D, ⊤) := fun i => ψ.app ⊤ (κs i)
  -- the sections restrict to zero on `Z`
  have hψ0 : ψ ≫ (Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app D = 0 := by
    have hnat : e.inv ≫ (Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app D =
        (Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app T ≫
          (Scheme.Modules.pullback ιZ ⋙ Scheme.Modules.pushforward ιZ).map e.inv :=
      (Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.naturality e.inv
    have htu := Stacks.AffineClosedUnion.twistedUnit_eq_unit ιZ T
    rw [Stacks.AffineClosedUnion.twistedUnit] at htu
    simp only [ψ, Category.assoc]
    rw [hnat, ← htu]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, kernel.condition, Functor.map_zero, zero_comp]
  have hunit : ∀ i, ((Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app D).app ⊤ (φ i) = 0 := by
    intro i
    have := congrArg (fun g => (Scheme.Modules.Hom.app g ⊤) (κs i)) hψ0
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app,
      ConcreteCategory.comp_apply] at this
    exact this.trans rfl
  -- presentations near `y`
  obtain ⟨U₀, hyU₀, e₀, he₀⟩ := hH y
  haveI : Nonempty U₀ := ⟨⟨y, hyU₀⟩⟩
  choose h hhpres hhval using fun i => exists_divisorialSectionValue_eq he₀ d (φ i)
  suffices hex : ∃ i, y ∈ R.basicOpen (h i) by
    obtain ⟨i, hi⟩ := hex
    exact ⟨φ i, hunit i, U₀, inferInstance, e₀, he₀, h i, hi, hhval i⟩
  -- an open neighbourhood of `y` missing `Z`
  have hZc : IsOpen (Set.range ιZ.base)ᶜ := ιZ.isClosedEmbedding.isClosed_range.isOpen_compl
  let W₀ : R.Opens := U₀ ⊓ ⟨_, hZc⟩
  have hyW₀ : y ∈ W₀ := ⟨hyU₀, hy⟩
  have hW₀U₀ : W₀ ≤ U₀ := inf_le_left
  set gen := (isLocalEquation_pow he₀ d).invSection with hgen
  let u : Γ(F.obj (Stacks.AlgebraicGeometry.PicardBaseChange.unitModule R), W₀) :=
    (Stacks.AffineClosedUnion.twistUnitIso T).inv.app W₀
      (e.hom.app W₀ (D.presheaf.map (homOfLE hW₀U₀).op gen))
  have hpre : ιZ ⁻¹ᵁ W₀ = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    exact absurd ⟨z, rfl⟩ hz.2
  have hsub : Subsingleton Γ(F.obj (Stacks.Morphisms.pushforwardStructureSheaf ιZ), W₀) := by
    have h1 : Subsingleton Γ((Scheme.Modules.pullback ιZ).obj T, ιZ ⁻¹ᵁ W₀) := by
      rw [hpre]; exact Module.subsingleton Γ(Z, ⊥) _
    have h2 : Subsingleton Γ((Scheme.Modules.pushforward ιZ).obj
        ((Scheme.Modules.pullback ιZ).obj T), W₀) := h1
    exact ⟨fun a b => injective_app_of_isIso
      (Stacks.AffineClosedUnion.twistPushforwardIso ιZ T).hom W₀ (Subsingleton.elim _ _)⟩
  have hgu : (F.map q).app W₀ u = 0 := Subsingleton.elim _ _
  obtain ⟨κ, hκ⟩ : ∃ κ : Γ(F.obj (kernel q), W₀), (F.map (kernel.ι q)).app W₀ κ = u := by
    let Tsec : R.Modules ⥤ ModuleCat Γ(R, W₀) := SheafOfModules.evaluation R.ringCatSheaf (op W₀)
    have _ : Tsec.PreservesZeroMorphisms := ⟨by intros; rfl⟩
    have _ : PreservesFiniteLimits Tsec :=
      SheafOfModules.Finite.evaluationPreservesFiniteLimits R.ringCatSheaf (op W₀)
    have hex := hS'.exact.map_of_mono_of_preservesKernel Tsec hS'.mono_f inferInstance
    exact (ShortComplex.moduleCat_exact_iff _).mp hex u hgu
  obtain ⟨W₁, hyW₁, hW₁, ρ, hρ⟩ := exists_eq_sum_smul_of_generatingSections σ' hyW₀ κ
  have hW₁U₀ : W₁ ≤ U₀ := hW₁.trans hW₀U₀
  set g₁ := D.presheaf.map (homOfLE hW₁U₀).op gen with hg₁
  have hnatψ : ∀ {V W : R.Opens} (i : V ⟶ W) (x : Γ(F.obj (kernel q), W)),
      ψ.app V ((F.obj (kernel q)).presheaf.map i.op x) = D.presheaf.map i.op (ψ.app W x) :=
    fun i x => congrArg (fun G => G x) (ψ.mapPresheaf.naturality i.op)
  have hψκ : ψ.app W₀ κ = D.presheaf.map (homOfLE hW₀U₀).op gen := by
    have : ψ.app W₀ κ = e.inv.app W₀ ((Stacks.AffineClosedUnion.twistUnitIso T).hom.app W₀
        ((F.map (kernel.ι q)).app W₀ κ)) := rfl
    rw [this, hκ]
    exact (congrArg (e.inv.app W₀) (inv_hom_id_app_apply _ W₀ _)).trans (hom_inv_id_app_apply e W₀ _)
  have hres : ∀ {V W W' : R.Opens} (i : V ⟶ W) (j : W ⟶ W') (x : Γ(D, W')),
      D.presheaf.map i.op (D.presheaf.map j.op x) = D.presheaf.map (i ≫ j).op x := by
    intro V W W' i j x
    rw [op_comp, Functor.map_comp]
    rfl
  have hφW₁ : ∀ i, D.presheaf.map (homOfLE (le_top : W₁ ≤ ⊤)).op (φ i) =
      R.presheaf.map (homOfLE hW₁U₀).op (h i) • g₁ := by
    intro i
    have h2 := congrArg (D.presheaf.map (homOfLE hW₁U₀).op) (hhpres i)
    rw [Scheme.Modules.map_smul, hres, hres] at h2
    exact h2.symm
  have hsumeq : g₁ = (∑ i, (show Γ(R, W₁) from ρ i) *
      R.presheaf.map (homOfLE hW₁U₀).op (h i)) • g₁ := by
    have h1 : ψ.app W₁ ((F.obj (kernel q)).presheaf.map (homOfLE hW₁).op κ) =
        ψ.app W₁ (∑ i, (show Γ(R, W₁) from ρ i) •
          (F.obj (kernel q)).presheaf.map (homOfLE le_top).op (κs i)) := congrArg _ hρ
    rw [hnatψ, hψκ, hres, map_sum] at h1
    refine h1.trans ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Scheme.Modules.Hom.app_smul, hnatψ, mul_smul]
    exact congrArg _ (hφW₁ i)
  have hone : (1 : Γ(R, W₁)) = ∑ i, (show Γ(R, W₁) from ρ i) *
      R.presheaf.map (homOfLE hW₁U₀).op (h i) := by
    apply ((isLocalEquation_pow he₀ d).isLocalGenerator_invSection W₁ hW₁U₀).1
    change (1 : Γ(R, W₁)) • g₁ = _ • g₁
    rwa [one_smul]
  by_contra hne
  simp only [not_exists] at hne
  have hmem : ∀ i, R.presheaf.germ W₁ y hyW₁ (R.presheaf.map (homOfLE hW₁U₀).op (h i)) ∈
      IsLocalRing.maximalIdeal (R.presheaf.stalk y) := by
    intro i
    rw [TopCat.Presheaf.germ_res_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hne i ((R.mem_basicOpen (h i) y hyU₀).mpr hu)
  have h1mem : R.presheaf.germ W₁ y hyW₁ 1 ∈ IsLocalRing.maximalIdeal (R.presheaf.stalk y) := by
    rw [hone, map_sum]
    exact Ideal.sum_mem _ fun i _ => by
      rw [map_mul]; exact Ideal.mul_mem_left _ _ (hmem i)
  rw [map_one] at h1mem
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1mem)

/-- A prime divisor is determined by its support. -/
private theorem primeDivisor_eq_of_support_eq {X : Scheme.{0}} {P Q : Mori.PrimeDivisor X}
    (h : (P.support : Set X) = Q.support) : P = Q := by
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  exact (inseparable_iff_closure_eq.2 h).eq

/-- **The normalization components of the floor are the floor components.** If the components
`νᵢ : Tᵢ ⟶ S` of a normalization of the reduced floor `S = ⌊B⌋` are adjunction steps onto the
floor primes, each floor prime being the image of exactly one of them, then they are indexed by the
floor primes and each `Tᵢ` is isomorphic over `X` to the given normal model `C_P`. -/
private theorem exists_equiv_iso_floorComponents {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {B : QDivisor X}
    {S : Scheme.{0}} (ιS : S ⟶ X)
    {hfin : ∀ U : S.Opens, IsCompact (U : Set S) → (irreducibleComponents U).Finite}
    (N : MMP.Flips.NormalizationComponents (ιS ≫ sX) hfin) {Θ : ∀ i, QDivisor (N.X i)}
    (hadj : ∀ i, IsAdjunctionStep sX B (N.n i ≫ ιS) (Θ i))
    (hbij : ∀ P ∈ B.roundDown.support, ∃! i, Set.range (N.n i ≫ ιS).base = (P.support : Set X))
    (C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0})
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    (j : ∀ P, C P ⟶ X) (BC : ∀ P, QDivisor (C P))
    (hC : ∀ P, IsAdjunctionStep sX B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X)) :
    ∃ π : N.ι ≃ {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      ∀ i, Set.range (N.n i ≫ ιS).base = ((π i).1.support : Set X) ∧
        ∃ p : C (π i) ≅ N.X i, p.hom ≫ N.n i ≫ ιS = j (π i) := by
  classical
  have hP : ∀ i, ∃ P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0},
      Set.range (N.n i ≫ ιS).base = (P.1.support : Set X) := by
    intro i
    obtain ⟨-, P, hP1, hPr, -⟩ := hadj i
    refine ⟨⟨P, ?_⟩, hPr⟩
    have : (1 : ℤ) ≤ ⌊B.coeff P⌋ := Int.le_floor.mpr (by exact_mod_cast hP1)
    omega
  choose π₀ hπ₀ using hP
  have hmem : ∀ P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0}, P.1 ∈ B.roundDown.support := by
    intro P
    rw [Finsupp.mem_support_iff]
    have := P.2
    rwa [← DivisorWithCoeffs.coeff_roundDown] at this
  have hinj : Function.Injective π₀ := by
    intro i i' h
    obtain ⟨i₀, -, hu⟩ := hbij (π₀ i).1 (hmem _)
    have h1 := hu i (hπ₀ i)
    have h2 := hu i' (show Set.range (N.n i' ≫ ιS).base = ((π₀ i).1.support : Set X) by
      rw [hπ₀ i', h])
    rw [h1, h2]
  have hsurj : Function.Surjective π₀ := by
    intro P
    obtain ⟨i, hi, -⟩ := hbij P.1 (hmem P)
    refine ⟨i, Subtype.ext (primeDivisor_eq_of_support_eq ?_)⟩
    rw [← hπ₀ i, hi]
  refine ⟨Equiv.ofBijective π₀ ⟨hinj, hsurj⟩, fun i => ⟨hπ₀ i, ?_⟩⟩
  change ∃ p : C (π₀ i) ≅ N.X i, p.hom ≫ N.n i ≫ ιS = j (π₀ i)
  obtain ⟨-, -, -, -, hci, -⟩ := hadj i
  obtain ⟨-, -, -, -, hcj, -⟩ := (hC (π₀ i)).1
  haveI := hci
  haveI := hcj
  obtain ⟨ψ, hψ⟩ := exists_iso_comp_eq_of_range_eq (j (π₀ i)) (N.n i ≫ ιS)
    (by rw [(hC (π₀ i)).2, hπ₀ i])
  exact ⟨ψ, hψ⟩

/-- **Reindexing a residue-restriction system** along an equivalence of index types. -/
private def residueRestrictionReindex {k : Type u} [Field k] {I J : Type*} {X : I → Scheme.{u}}
    {sX : ∀ i, X i ⟶ Spec (.of k)} [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)]
    [∀ i, IsNormal (X i)] {B : ∀ i, QDivisor (X i)} {n m : ℕ} (R : ResidueRestriction sX B n m)
    (π : J ≃ I) : ResidueRestriction (fun j => sX (π j)) (fun j => B (π j)) n m where
  setting :=
    { finite := by haveI := R.setting.finite; exact Finite.of_equiv I π.symm
      isProjectiveVariety := fun j => R.setting.isProjectiveVariety (π j)
      isPair := fun j => R.setting.isPair (π j)
      isDltPair := fun j => R.setting.isDltPair (π j)
      topologicalKrullDim_eq := fun j => R.setting.topologicalKrullDim_eq (π j)
      even := R.setting.even
      pos := R.setting.pos
      isCartierDivisor := fun j => R.setting.isCartierDivisor (π j) }
  toFun j := R.toFun (π j)
  isIteratedResidue j := R.isIteratedResidue (π j)

/-- Reindexing preserves admissibility. -/
private theorem mem_admissibleSections_reindex {k : Type u} [Field k] {I J : Type*}
    {X : I → Scheme.{u}} {sX : ∀ i, X i ⟶ Spec (.of k)} [∀ i, IsIntegral (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)] {B : ∀ i, QDivisor (X i)} {n m : ℕ}
    (R : ResidueRestriction sX B n m) (π : J ≃ I)
    {s : ∀ i, logPluricanonicalSections (sX i) n m (B i)} (hs : s ∈ admissibleSections R) :
    (fun j => s (π j)) ∈ admissibleSections (residueRestrictionReindex R π) :=
  fun j j' _ _ _ _ _ _ F F' e h₁ h₂ h₃ h₄ σ hσ => hs (π j) (π j') F F' e h₁ h₂ h₃ h₄ σ hσ

/-- **Residue-restriction systems along equal structure morphisms.** -/
private theorem exists_residueRestriction_congr {k : Type u} [Field k] {I : Type*}
    {X : I → Scheme.{u}} [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)]
    [∀ i, IsNormal (X i)] {sX sX' : ∀ i, X i ⟶ Spec (.of k)} (h : sX = sX')
    {B : ∀ i, QDivisor (X i)} {n m : ℕ} (R : ResidueRestriction sX' B n m)
    (s : ∀ i, logPluricanonicalSections (sX' i) n m (B i)) (hs : s ∈ admissibleSections R) :
    ∃ (R' : ResidueRestriction sX B n m) (s' : ∀ i, logPluricanonicalSections (sX i) n m (B i)),
      s' ∈ admissibleSections R' ∧ ∀ i, HEq (s' i : RationalPluriForms (sX i) n m)
        (s i : RationalPluriForms (sX' i) n m) := by
  subst h
  exact ⟨R, s, hs, fun _ => HEq.rfl⟩

/-- An integral scheme is its own unique irreducible component. -/
private theorem univ_mem_irreducibleComponents (X : Scheme.{0}) [IsIntegral X] :
    (Set.univ : Set X) ∈ irreducibleComponents X := by
  rw [irreducibleComponents_eq_singleton]; rfl

/-- The logarithmic frame `dt/t ∧ dx₁ ∧ ⋯ ∧ dx_e` of top forms along a prime divisor. -/
private noncomputable def logFrame {Y T : Scheme.{0}} [IsIntegral Y] [IsIntegral T] (sY : Y ⟶ Spec (.of ℂ))
    (j : T ⟶ Y) {e : ℕ} (t : Y.presheaf.stalk (j (genericPoint T)))
    (x : Fin e → Y.presheaf.stalk (j (genericPoint T))) :
    letI := functionFieldAlgebra sY
    ⋀[Y.functionField]^(e + 1) Ω[Y.functionField⁄ℂ] :=
  letI := functionFieldAlgebra sY
  (algebraMap _ Y.functionField t)⁻¹ • exteriorPower.ιMulti Y.functionField (e + 1)
    (Fin.cons (KaehlerDifferential.D ℂ Y.functionField (algebraMap _ _ t))
      fun i => KaehlerDifferential.D ℂ Y.functionField (algebraMap _ _ (x i)))

/-- The restricted frame `dx̄₁ ∧ ⋯ ∧ dx̄_e` of top forms on the divisor. -/
private noncomputable def resFrame {Y T : Scheme.{0}} [IsIntegral T] (sY : Y ⟶ Spec (.of ℂ))
    (j : T ⟶ Y) {e : ℕ} (x : Fin e → Y.presheaf.stalk (j (genericPoint T))) :
    letI := functionFieldAlgebra (j ≫ sY)
    ⋀[T.functionField]^e Ω[T.functionField⁄ℂ] :=
  letI := functionFieldAlgebra (j ≫ sY)
  exteriorPower.ιMulti T.functionField e fun i =>
    KaehlerDifferential.D ℂ T.functionField ((j.stalkMap (genericPoint T)).hom (x i))

/-- The residue of a form written in the logarithmic frame. -/
private theorem isPoincareResidue_smul_formPow_logFrame {Y T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsIntegral T] (sY : Y ⟶ Spec (.of ℂ)) (j : T ⟶ Y) {e m : ℕ}
    {t : Y.presheaf.stalk (j (genericPoint T))} (ht : Y.ord (algebraMap _ Y.functionField t)
      (j (genericPoint T)) = 1) (x : Fin e → Y.presheaf.stalk (j (genericPoint T)))
    (h : Y.presheaf.stalk (j (genericPoint T))) :
    letI := functionFieldAlgebra sY
    letI := functionFieldAlgebra (j ≫ sY)
    IsPoincareResidue sY j e m
      (algebraMap _ Y.functionField h • formPow (logFrame sY j t x) m)
      ((j.stalkMap (genericPoint T)).hom h • formPow (resFrame sY j x) m) :=
  ⟨t, h, x, ht, rfl, rfl⟩

/-- A unit of the local ring at the generic point of a prime divisor has order zero along it,
for any spelling `x = η_P` of that point. -/
private theorem ord_algebraMap_stalk_eq_zero_of_isUnit {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y) {x : Y}
    (hx : x = P.genericPoint) {u : Y.presheaf.stalk x} (hu : IsUnit u) :
    Y.ord (algebraMap _ Y.functionField u) P.genericPoint = 0 := by
  subst hx
  exact P.ord_algebraMap_of_isUnit hu

/-- A germ at the image of the generic point of an integral closed subscheme `j : T ⟶ Y` whose
restriction to `T` is nonzero is a unit: the stalk of `T` at its generic point is a field. -/
private theorem isUnit_of_stalkMap_genericPoint_ne_zero {Y T : Scheme.{0}} [IsIntegral T]
    (j : T ⟶ Y) {g : Y.presheaf.stalk (j (genericPoint T))}
    (hg : (j.stalkMap (genericPoint T)).hom g ≠ 0) : IsUnit g := by
  have hfield : IsField (T.presheaf.stalk (genericPoint T)) := by
    have := RationalFunctions.isField_stalk T ⟨Set.univ, univ_mem_irreducibleComponents T⟩
    rwa [componentGenericPoint_eq_genericPoint] at this
  letI := hfield.toField
  exact isUnit_of_map_unit (j.stalkMap (genericPoint T)).hom g (isUnit_iff_ne_zero.mpr hg)

/-- **The logarithmic frame of a residue.** Let `σ` be a rational top form on `Y` with a simple
pole along the prime divisor `P = j(T)` and a nonzero Poincaré residue `ρσ`. Then `σ = g₀ ω₀` and
`ρσ = ḡ₀ ω̄₀` for a logarithmic frame `ω₀ = dt/t ∧ dx` and a unit `g₀`, and every rational
`m`-canonical form with `ord_P τ ≥ -m` is `h ω₀^{⊗m}` with `h` regular along `P`. -/
private theorem exists_logFrame {Y T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY]
    {e : ℕ} (hd : topologicalKrullDim Y = (e + 1 : ℕ)) [IsIntegral T] {j : T ⟶ Y}
    (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    {σ : RationalPluriForms sY (e + 1) 1} (hσ0 : σ ≠ 0) (hσP : P.ordForm σ = -1)
    {ρσ : RationalPluriForms (j ≫ sY) e 1} (hρσ : IsPoincareResidue sY j e 1 σ ρσ)
    (hρσ0 : ρσ ≠ 0) :
    letI := functionFieldAlgebra sY
    letI := functionFieldAlgebra (j ≫ sY)
    ∃ (t g₀ : Y.presheaf.stalk (j (genericPoint T)))
      (x : Fin e → Y.presheaf.stalk (j (genericPoint T))),
      Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1 ∧ IsUnit g₀ ∧
      σ = algebraMap _ Y.functionField g₀ • formPow (logFrame sY j t x) 1 ∧
      ρσ = (j.stalkMap (genericPoint T)).hom g₀ • formPow (resFrame sY j x) 1 ∧
      ∀ (m : ℕ) (τ : RationalPluriForms sY (e + 1) m), (τ ≠ 0 → -(m : ℤ) ≤ P.ordForm τ) →
        ∃ h : Y.presheaf.stalk (j (genericPoint T)),
          τ = algebraMap _ Y.functionField h • formPow (logFrame sY j t x) m := by
  classical
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  obtain ⟨t, g₀, x, ht, hσ, hρσ'⟩ := hρσ
  set ω₀ := logFrame sY j t x with hω₀
  have hg₀ : (j.stalkMap (genericPoint T)).hom g₀ ≠ 0 := by
    intro h0
    apply hρσ0
    rw [hρσ', h0, zero_smul]
    rfl
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hd
  obtain ⟨b⟩ := exists_basis_topForms (sX := sY) hd
  obtain ⟨N, hN⟩ := P.exists_ordForm_eq_ord_add_mul hd' b
  set c := b.repr ω₀ () with hc
  have hω₀b : ω₀ = c • b () := (basis_unit_repr_smul b ω₀).symm
  have hpow : ∀ a : ℕ, (formPow ω₀ a : RationalPluriForms sY (e + 1) a) = c ^ a • formPow (b ()) a :=
    fun a => by rw [hω₀b, formPow_smul]
  have hσω : σ = algebraMap _ Y.functionField g₀ • formPow ω₀ 1 := hσ
  have hσ' : σ = (algebraMap _ Y.functionField g₀ * c) • formPow (b ()) 1 := by
    rw [hσω, mul_smul, ← pow_one c, ← hpow]
  have hc0 : c ≠ 0 := by
    intro h0; apply hσ0
    rw [hσ', h0, mul_zero, zero_smul]
    rfl
  have hcoh : Order.coheight (j (genericPoint T)) = 1 := by
    rw [hP]; exact P.coheight_genericPoint
  have hg₀u : IsUnit g₀ := isUnit_of_stalkMap_genericPoint_ne_zero j hg₀
  have hg₀ord := ord_algebraMap_stalk_eq_zero_of_isUnit P hP hg₀u
  have hσN := hN 1 σ hσ0
  have hr1 : (ZTensorPower.basis b 1).repr
      ((algebraMap _ Y.functionField g₀ * c) • formPow (b ()) 1 : RationalPluriForms sY (e + 1) 1)
      () = algebraMap _ Y.functionField g₀ * c := repr_smul_formPow b 1 _
  rw [hσ', hr1, ← hσ', hσP, Scheme.ord_mul ((hg₀u.map _).ne_zero) hc0, hg₀ord] at hσN
  refine ⟨t, g₀, x, ht, hg₀u, hσω, hρσ', fun m τ hτ => ?_⟩
  by_cases hτ0 : τ = 0
  · exact ⟨0, by rw [hτ0, map_zero, zero_smul]; rfl⟩
  set fτ := (ZTensorPower.basis b m).repr τ () / c ^ m with hfτ
  have hτf : τ = fτ • formPow ω₀ m := by
    rw [hpow, smul_smul, hfτ, div_mul_cancel₀ _ (pow_ne_zero _ hc0)]
    exact eq_repr_smul_formPow b τ
  have hrepr0 : (ZTensorPower.basis b m).repr τ () ≠ 0 := repr_ne_zero_of_ne_zero b hτ0
  have hf0 : fτ ≠ 0 := div_ne_zero hrepr0 (pow_ne_zero _ hc0)
  have hford : 0 ≤ Y.ord fτ (j (genericPoint T)) := by
    have h1 := hτ hτ0
    rw [hN m τ hτ0] at h1
    rw [hP, hfτ, div_eq_mul_inv, Scheme.ord_mul hrepr0 (inv_ne_zero (pow_ne_zero _ hc0)),
      ← zpow_natCast, ← zpow_neg, ord_zpow _ hc0]
    push_cast
    nlinarith
  obtain ⟨h, hh⟩ := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hcoh hf0).mpr hford
  exact ⟨h, by rw [hτf, ← hh]⟩

/-- A nonzero multiple of a power of a nonzero top form is nonzero. -/
private theorem smul_formPow_ne_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d)
    {ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄ℂ]}
    (hω : ω ≠ 0) {f : X.functionField} (hf : f ≠ 0) (a : ℕ) :
    letI := functionFieldAlgebra sX
    (show RationalPluriForms sX d a from f • formPow ω a) ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  set c := b.repr ω () with hc
  have hωb : ω = c • b () := (basis_unit_repr_smul b ω).symm
  have hc0 : c ≠ 0 := fun h0 => hω (by rw [hωb, h0, zero_smul])
  have e1 : (f • formPow ω a : RationalPluriForms sX d a) = (f * c ^ a) • formPow (b ()) a := by
    rw [hωb, formPow_smul, smul_smul]
  change (f • formPow ω a : RationalPluriForms sX d a) ≠ 0
  rw [e1, ← ZTensorPower.basis_natCast]
  exact smul_ne_zero (mul_ne_zero hf (pow_ne_zero _ hc0)) ((ZTensorPower.basis b _).ne_zero ())

/-- The order of `f ω^{⊗a}` along a prime divisor is `ord f + a ord ω`. -/
private theorem ordForm_smul_formPow {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) (Γ : Mori.PrimeDivisor X)
    {ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄ℂ]}
    (hω : ω ≠ 0) {f : X.functionField} (hf : f ≠ 0) (a : ℕ) :
    letI := functionFieldAlgebra sX
    Γ.ordForm (show RationalPluriForms sX d a from f • formPow ω a) =
      X.ord f Γ.genericPoint + a * Γ.ordForm (show RationalPluriForms sX d 1 from formPow ω 1) := by
  let := functionFieldAlgebra sX
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd' b
  set c := b.repr ω () with hc
  have hωb : ω = c • b () := (basis_unit_repr_smul b ω).symm
  have hc0 : c ≠ 0 := fun h0 => hω (by rw [hωb, h0, zero_smul])
  have hpow : ∀ k : ℕ, (formPow ω k : RationalPluriForms sX d k) = c ^ k • formPow (b ()) k :=
    fun k => by rw [hωb, formPow_smul]
  have e1 : (f • formPow ω a : RationalPluriForms sX d a) = (f * c ^ a) • formPow (b ()) a := by
    rw [hpow, smul_smul]
  have e2 : (formPow ω 1 : RationalPluriForms sX d 1) = c • formPow (b ()) 1 := by
    rw [hpow, pow_one]
  have h1 : (f * c ^ a) • formPow (b ()) a ≠ (0 : RationalPluriForms sX d a) := by
    rw [← ZTensorPower.basis_natCast]
    exact smul_ne_zero (mul_ne_zero hf (pow_ne_zero _ hc0)) ((ZTensorPower.basis b _).ne_zero ())
  have h2 : c • formPow (b ()) 1 ≠ (0 : RationalPluriForms sX d 1) := by
    rw [← ZTensorPower.basis_natCast]
    exact smul_ne_zero hc0 ((ZTensorPower.basis b _).ne_zero ())
  have r1 : (ZTensorPower.basis b a).repr ((f * c ^ a) • formPow (b ()) a :
      RationalPluriForms sX d a) () = f * c ^ a := repr_smul_formPow b a _
  have r2 : (ZTensorPower.basis b 1).repr (c • formPow (b ()) 1 :
      RationalPluriForms sX d 1) () = c := repr_smul_formPow b 1 _
  rw [e1, e2, hN _ _ h1, hN _ _ h2, r1, r2, Scheme.ord_mul hf (pow_ne_zero _ hc0),
    ← zpow_natCast, ord_zpow _ hc0]
  push_cast
  ring

/-- **Residues of forms with a pole of full order are nonzero.** Let `j : T ⟶ Y` be a closed
immersion of integral schemes onto a prime divisor `P` of the normal variety `Y` of dimension
`e + 1`, and `σ` a top form with a simple pole along `P` and a nonzero residue. Every
rational `m`-canonical form `τ ≠ 0` with `ord_P τ = -m` has a Poincaré residue along `P`, and
that residue is nonzero. -/
private theorem exists_isPoincareResidue_ne_zero_of_ordForm_eq {Y T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY]
    {e : ℕ} (hd : topologicalKrullDim Y = (e + 1 : ℕ)) [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] {j : T ⟶ Y} [LocallyOfFiniteType (j ≫ sY)]
    (hdT : topologicalKrullDim T = e)
    (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    {σ : RationalPluriForms sY (e + 1) 1} (hσ0 : σ ≠ 0) (hσP : P.ordForm σ = -1)
    {ρσ : RationalPluriForms (j ≫ sY) e 1} (hρσ : IsPoincareResidue sY j e 1 σ ρσ)
    (hρσ0 : ρσ ≠ 0) {m : ℕ} (τ : RationalPluriForms sY (e + 1) m) (hτ0 : τ ≠ 0)
    (hτP : P.ordForm τ = -(m : ℤ)) :
    ∃ ρ : RationalPluriForms (j ≫ sY) e m, IsPoincareResidue sY j e m τ ρ ∧ ρ ≠ 0 := by
  classical
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  obtain ⟨t, g₀, x, ht, hg₀u, hσeq, hρσeq, hall⟩ := exists_logFrame hd P hP hσ0 hσP hρσ hρσ0
  obtain ⟨h, hh⟩ := hall m τ (fun _ => hτP.ge)
  set ω₀ := logFrame sY j t x with hω₀def
  have hpow0 : ∀ (ω : ⋀[Y.functionField]^(e + 1) Ω[Y.functionField⁄ℂ]) (a : ℕ), 0 < a →
      ω = 0 → (formPow ω a : RationalPluriForms sY (e + 1) a) = 0 := by
    intro ω a ha hω
    rw [show ω = (0 : Y.functionField) • ω by rw [hω, smul_zero], formPow_smul,
      zero_pow ha.ne', zero_smul]
  have hω₀ : ω₀ ≠ 0 := by
    intro h0
    apply hσ0
    rw [hσeq, hpow0 ω₀ 1 one_pos h0, smul_zero]
    rfl
  have hunit_ord : ∀ u : Y.presheaf.stalk (j (genericPoint T)), IsUnit u →
      Y.ord (algebraMap _ Y.functionField u) P.genericPoint = 0 :=
    fun _ hu => ord_algebraMap_stalk_eq_zero_of_isUnit P hP hu
  have hg₀ne : algebraMap _ Y.functionField g₀ ≠ 0 := (hg₀u.map _).ne_zero
  have hσord := ordForm_smul_formPow hd P hω₀ hg₀ne 1
  rw [← hσeq, hσP, hunit_ord g₀ hg₀u] at hσord
  have hω₀ord : P.ordForm (show RationalPluriForms sY (e + 1) 1 from formPow ω₀ 1) = -1 := by
    have h1 := hσord
    simp only [Nat.cast_one, one_mul, zero_add] at h1
    exact h1.symm
  have hh0 : algebraMap _ Y.functionField h ≠ 0 := by
    intro h0
    apply hτ0
    rw [hh, h0, zero_smul]
    rfl
  have hτord := ordForm_smul_formPow hd P hω₀ hh0 m
  rw [← hh, hτP, hω₀ord] at hτord
  have hhord : Y.ord (algebraMap _ Y.functionField h) P.genericPoint = 0 := by omega
  obtain ⟨v, hv, hvh⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
    (j (genericPoint T)) hh0 fun Γ hΓ => by
      rw [hP] at hΓ
      obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hΓ
      exact hhord
  have hvh' : v = h := IsFractionRing.injective _ Y.functionField hvh
  subst hvh'
  refine ⟨(j.stalkMap (genericPoint T)).hom v • formPow (resFrame sY j x) m,
    hh ▸ isPoincareResidue_smul_formPow_logFrame sY j ht x v, ?_⟩
  have hres0 : resFrame sY j x ≠ 0 := by
    intro h0
    apply hρσ0
    rw [hρσeq]
    have : (formPow (resFrame sY j x) 1 : RationalPluriForms (j ≫ sY) e 1) = 0 := by
      rw [show resFrame sY j x = (0 : T.functionField) • resFrame sY j x by rw [h0, smul_zero],
        formPow_smul, zero_pow one_ne_zero, zero_smul]
    rw [this, smul_zero]
    rfl
  exact smul_formPow_ne_zero hdT hres0 ((hv.map _).ne_zero) m

/-- An integral locally Noetherian normal scheme with a point other than its generic point has a
prime divisor: a minimal prime over a nonzero element of the maximal ideal of the local ring at
that point has height one by Krull's principal ideal theorem. -/
private theorem nonempty_primeDivisor_of_ne_genericPoint {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {x : X} (hx : x ≠ genericPoint X) :
    Nonempty (MMP.Mori.PrimeDivisor X) := by
  set R := X.presheaf.stalk x
  have hm : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    intro h0
    have hη : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    have hx' : x ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact specializes_rfl
    obtain ⟨p₁, hp₁⟩ := hη
    obtain ⟨p₂, hp₂⟩ := hx'
    have hall : ∀ p : PrimeSpectrum R, p.asIdeal = ⊥ := fun p =>
      le_bot_iff.mp (h0 ▸ IsLocalRing.le_maximalIdeal p.2.ne_top)
    have : p₁ = p₂ := PrimeSpectrum.ext ((hall p₁).trans (hall p₂).symm)
    exact hx (by rw [← hp₂, ← this, hp₁])
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hle : Ideal.span {a} ≤ IsLocalRing.maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).mpr ha
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hle
  haveI : q.IsPrime := hq.1.1
  have h1 : q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq
  have h0 : q.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro hq0
    exact ha0 (by
      have : a ∈ q := hq.1.2 (Ideal.mem_span_singleton_self a)
      rwa [hq0, Ideal.mem_bot] at this)
  have hq1 : q.height = 1 := le_antisymm h1 (ENat.one_le_iff_ne_zero.mpr h0)
  obtain ⟨E, -, -⟩ := MMP.Mori.exists_primeDivisor_isLocalization (x := x) ⟨q, inferInstance⟩ hq1
  exact ⟨E⟩

/-- A scheme of positive dimension has a point other than a given one. -/
private theorem exists_ne_of_topologicalKrullDim_pos {X : Scheme.{0}} {n : ℕ} (hn : 0 < n)
    (hdim : topologicalKrullDim X = n) (y : X) : ∃ x : X, x ≠ y := by
  by_contra h
  push Not at h
  haveI : Subsingleton X := ⟨fun a b => (h a).trans (h b).symm⟩
  haveI : DiscreteTopology X := Subsingleton.discreteTopology
  have h0 := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at h0
  norm_cast at h0
  omega

/-- **A top form with a simple pole along a prime divisor and nonzero residue**, on a normal
variety of dimension `n + 1 ≥ 2`. -/
private theorem exists_simplePole_isPoincareResidue_ne_zero {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ} (hn : 0 < n)
    (hdim : topologicalKrullDim X = n + 1) (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T]
    [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sX))
    (hdimT : topologicalKrullDim T = n) (P : Mori.PrimeDivisor X)
    (hP : Set.range j.base = (P.support : Set X)) :
    ∃ σ : RationalPluriForms sX (n + 1) 1, σ ≠ 0 ∧ P.ordForm σ = -1 ∧
      ∃ ρσ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 σ ρσ ∧ ρσ ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne_of_topologicalKrullDim_pos hn hdimT (genericPoint T)
  obtain ⟨Q⟩ := nonempty_primeDivisor_of_ne_genericPoint hx
  obtain ⟨σ, hσ0, hσP, -, ρσ, hρσ, hρσ0, -⟩ :=
    MMP.Fourfold.exists_form_of_residue_order sX hX hdim j hT P hP Q
  exact ⟨σ, hσ0, hσP, ρσ, hρσ, hρσ0⟩

/-- **The base forms generate.** If `e` is a local equation of `H` on `U`, then
`f^*e^{-r} · w^{⊗kr}` generates `𝒪_X(kr(K_X + B))` over `f⁻¹(U)`. -/
private theorem generatesOn_base
    {X R : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R]
    (f : X ⟶ R) [IsDominant f] {H : Divisor R}
    {hfH : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ H.supp}
    {M : Divisor X} (hM : H.IsPullback f hfH M) {K : Divisor X} {B : QDivisor X} {k r : ℕ}
    {u : X.functionField} (hu0 : u ≠ 0)
    (hMu : ∀ Γ : Mori.PrimeDivisor X,
      (X.ord u Γ.genericPoint : ℚ) = M.coeff Γ - k * (K.coeff Γ + B.coeff Γ))
    (w : letI := functionFieldAlgebra sX; ⋀[X.functionField]^(n + 1) Ω[X.functionField⁄ℂ])
    (hw : ∀ N : ℕ, 0 < N → formPowR sX w N ≠ 0 ∧
      ∀ Γ : Mori.PrimeDivisor X, Γ.ordForm (formPowR sX w N) = N * K.coeff Γ)
    (hm0 : 0 < k * r) {U : R.Opens} {e : (RationalFunctions R)ˣ} (he : H.IsLocalEquation U e) :
    letI := functionFieldAlgebra sX
    GeneratesOn B (k * r) (f ⁻¹ᵁ U)
      (((functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
        (e : RationalFunctions R)))⁻¹ * u) ^ r • formPowR sX w (k * r)) := by
  letI := functionFieldAlgebra sX
  set v := MMP.Threefold.Mori.Helpers.evalFF (univComponent R) (e : RationalFunctions R)
    with hv
  have hv0 : v ≠ 0 := (e.isUnit.map _).ne_zero
  have hfu0 : functionFieldMap f v ≠ 0 := (map_ne_zero _).mpr hv0
  have hc0 : ((functionFieldMap f v)⁻¹ * u) ^ r ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (inv_ne_zero hfu0) hu0)
  refine ⟨smul_ne_zero hc0 (hw _ hm0).1, fun Γ hΓ => ?_⟩
  have hΓU : Γ.genericPoint ∈ f ⁻¹ᵁ U := Mori.PrimeDivisor.genericPoint_mem_of_nonempty (E := Γ) hΓ
  have hMΓ := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hM he Γ hΓU (univComponent R)
  rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hdim hc0 (hw _ hm0).1, (hw _ hm0).2 Γ, mul_pow,
    Scheme.ord_mul (pow_ne_zero _ (inv_ne_zero hfu0)) (pow_ne_zero _ hu0),
    MMP.Flips.ord_inv_pow hfu0, Scheme.ord_pow hu0, ← hMΓ]
  have h1 := hMu Γ
  push_cast
  linear_combination (r : ℚ) * h1

/-- In degree `0`, the `m`-th tensor power of the generator `1 ∈ ⋀⁰ M` is nonzero. -/
private theorem tprod_ιMulti_zero_ne_zero {K : Type} [Field K] {M : Type} [AddCommGroup M]
    [Module K M] (m : ℕ) (v : Fin 0 → M) :
    (PiTensorProduct.tprod K (fun _ : Fin m => exteriorPower.ιMulti K 0 v) :
      TensorPower K m (⋀[K]^0 M)) ≠ 0 := by
  let b : Module.Basis Unit K (⋀[K]^0 M) :=
    (Module.Basis.singleton Unit K).map (exteriorPower.zeroEquiv K M).symm
  have hb : b () = exteriorPower.ιMulti K 0 v := by
    apply (exteriorPower.zeroEquiv K M).injective
    rw [exteriorPower.zeroEquiv_ιMulti]
    simp [b]
  have h := (Basis.piTensorProduct (fun _ : Fin m => b)).ne_zero (fun _ => ())
  rw [Basis.piTensorProduct_apply] at h
  simpa only [hb] using h

/-- **Forms at a point of a normal curve in the logarithmic frame.** Along an adjunction step
`j : Q ⟶ C` onto a point of a normal curve, a rational `m`-canonical form `ρ` with a pole of order
at most `m` there is `g (dϖ/ϖ)^{⊗m}` for a uniformizer `ϖ` and a regular function `g`, and `g` is a
unit when `ρ ≠ 0` has a pole of order exactly `m`. -/
private theorem exists_eq_smul_formPow_logFrame_of_curve {C Q : Scheme.{0}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] {s : C ⟶ Spec (.of ℂ)}
    (hC : IsNormalVariety ℂ s) (hdim : topologicalKrullDim C = 1) {BC : QDivisor C}
    {j : Q ⟶ C} {BQ : QDivisor Q} (hj : IsAdjunctionStep s BC j BQ) [IsIntegral Q] {m : ℕ}
    (ρ : RationalPluriForms s 1 m)
    (hρ : ∀ P : Mori.PrimeDivisor C, j (genericPoint Q) = P.genericPoint → ρ ≠ 0 →
      -(m : ℤ) ≤ P.ordForm ρ) :
    letI := functionFieldAlgebra s
    ∃ ϖ g : C.presheaf.stalk (j (genericPoint Q)),
      C.ord (algebraMap _ C.functionField ϖ) (j (genericPoint Q)) = 1 ∧
      ρ = algebraMap _ C.functionField g • formPow (logFrame s j ϖ Fin.elim0) m ∧
      ((∀ P : Mori.PrimeDivisor C, j (genericPoint Q) = P.genericPoint →
        P.ordForm ρ = -(m : ℤ)) → ρ ≠ 0 → IsUnit g) := by
  classical
  haveI : LocallyOfFiniteType s := hC.1.toLocallyOfFiniteType
  obtain ⟨P, hP, hci⟩ := hj.exists_primeDivisor
  let O := C.presheaf.stalk (j (genericPoint Q))
  let := stalkAlgebra s (j (genericPoint Q))
  let := functionFieldAlgebra s
  let := functionFieldAlgebra (j ≫ s)
  let : Algebra O Q.functionField := (j.stalkMap (genericPoint Q)).hom.toAlgebra
  have := isScalarTower_stalk_functionField s (j (genericPoint Q))
  obtain ⟨hdvr, hfree, hfin, -, hcoh, hrank⟩ := hj.stalk_facts
  obtain ⟨-, hsurj⟩ := hj.stalkMap_facts
  obtain ⟨ϖ, r, -, hr, hker, -, -⟩ := hj.exists_uniformizer
  have htr : (Algebra.trdeg ℂ C.functionField).toNat = 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (by exact_mod_cast hdim)
  -- `ϖ` is a uniformizer
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)).symm.trans hker
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
  have hϖ0 : algebraMap O C.functionField ϖ ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hϖirr.ne_zero
  have hord : C.ord (algebraMap O C.functionField ϖ) (j (genericPoint Q)) = 1 :=
    (Scheme.ord_eq_iff hcoh hϖ0).mpr (Ring.ordFrac_irreducible hϖirr)
  by_cases hρ0 : ρ = 0
  · refine ⟨ϖ, 0, hord, ?_, fun _ h => absurd hρ0 h⟩
    rw [hρ0, map_zero]
    exact (zero_smul _ _).symm
  -- `dϖ` generates `Ω_{𝒪/ℂ}`
  have hspan : Submodule.span O (Set.range ![KaehlerDifferential.D ℂ O ϖ]) = ⊤ := by
    haveI := hfree
    haveI := hfin
    have hrk : Module.finrank O Ω[O⁄ℂ] = 1 := hrank.trans htr
    let b₀ := Module.finBasisOfFinrankEq O Ω[O⁄ℂ] hrk
    set c := b₀.repr (KaehlerDifferential.D ℂ O ϖ) 0 with hc_def
    have hD : KaehlerDifferential.D ℂ O ϖ = c • b₀ 0 := by
      conv_lhs => rw [← b₀.sum_repr (KaehlerDifferential.D ℂ O ϖ)]
      simp [Fin.sum_univ_one, hc_def]
    have hc : IsUnit c := IsUnit.of_mul_eq_one (r (b₀ 0)) (by
      rw [← smul_eq_mul, ← map_smul, ← hD, hr])
    refine eq_top_iff.mpr ?_
    rw [← b₀.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have : b₀ 0 = ((hc.unit⁻¹ : Oˣ) : O) • KaehlerDifferential.D ℂ O ϖ := by
      conv_rhs => rw [hD]
      rw [smul_smul, hc.val_inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  -- the frame `dϖ` of `Ω_{k(C)/ℂ}`
  have := essFiniteType_functionField (sX := s)
  have hK1 : Module.finrank C.functionField Ω[C.functionField⁄ℂ] = 1 :=
    (finrank_kaehlerDifferential_eq_trdeg ℂ C.functionField).trans htr
  have : FiniteDimensional C.functionField Ω[C.functionField⁄ℂ] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent ℂ C.functionField).1
  haveI := nontrivial_exteriorPower_of_finrank_eq ℂ C.functionField hK1
  have hσ := MMP.Fourfold.span_singleton_ιMulti_eq_top _ hspan
  have h0 := topFormsMap_ne_zero_of_span_eq_top (k := ℂ) (K := C.functionField) hσ
  set F0 := topFormsMap ℂ O C.functionField 1 (exteriorPower.ιMulti O 1
    ![KaehlerDifferential.D ℂ O ϖ]) with hF0_def
  have hfr1 : Module.finrank C.functionField (⋀[C.functionField]^1 Ω[C.functionField⁄ℂ]) = 1 := by
    rw [exteriorPower.finrank_eq, hK1, Nat.choose_self]
  have hspanK : Submodule.span C.functionField {F0} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero F0 h0).mp hfr1
  let bK := basisOfSpanSingleton hspanK h0
  set c := (ZTensorPower.basis bK (m : ℤ)).repr ρ () with hc_def
  have hρeq : ρ = c • (PiTensorProduct.tprod C.functionField (fun _ : Fin m => F0) :
      TensorPower C.functionField m (⋀[C.functionField]^1 Ω[C.functionField⁄ℂ])) := by
    have h1 := basis_unit_repr_smul (ZTensorPower.basis bK (m : ℤ)) ρ
    have h2 := ZTensorPower.basis_ofNat bK m
    rw [basisOfSpanSingleton_apply] at h2
    rw [← hc_def] at h1
    rw [← h2]
    exact h1.symm
  have hc0 : c ≠ 0 := fun h => hρ0 (by rw [hρeq, h]; exact zero_smul _ _)
  have hordc : P.ordForm ρ = C.ord c P.genericPoint :=
    MMP.CyclicChartDifferent.ordForm_eq_of_frame (sX := s) P hP ![KaehlerDifferential.D ℂ O ϖ]
      hspan h0 c ρ hρeq
  -- the coefficient along the frame `(dϖ/ϖ)^m` has order `ord_P ρ + m` along `P`
  have hgK : c * algebraMap O C.functionField ϖ ^ m ≠ 0 := mul_ne_zero hc0 (pow_ne_zero _ hϖ0)
  have hordg : ∀ Γ : Mori.PrimeDivisor C, j (genericPoint Q) ∈ Γ.support →
      C.ord (c * algebraMap O C.functionField ϖ ^ m) Γ.genericPoint = P.ordForm ρ + m := by
    intro Γ hΓ
    have hΓP : Γ.genericPoint = P.genericPoint := by
      have hsp : Γ.genericPoint ⤳ j (genericPoint Q) := by
        rwa [specializes_iff_mem_closure, ← PrimeDivisor.support_eq_closure]
      rw [hP] at hsp
      exact MMP.ProgramBaseChange.eq_of_specializes_of_coheight_eq_one hsp
        Γ.coheight_genericPoint P.coheight_genericPoint
    rw [hΓP, Scheme.ord_mul hc0 (pow_ne_zero _ hϖ0), Scheme.ord_pow hϖ0, ← hP, hord, hP, hordc]
    omega
  obtain ⟨g, hg⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    (j (genericPoint Q)) hgK fun Γ hΓ => by
      have := hρ P hP hρ0
      rw [hordg Γ hΓ]
      omega
  refine ⟨ϖ, g, hord, ?_, fun hexact _ => ?_⟩
  · have hF0' : exteriorPower.ιMulti C.functionField (0 + 1)
        (Fin.cons (KaehlerDifferential.D ℂ C.functionField (algebraMap O C.functionField ϖ))
          fun i : Fin 0 => KaehlerDifferential.D ℂ C.functionField
            (algebraMap O C.functionField (Fin.elim0 i))) = F0 := by
      rw [hF0_def, topFormsMap_ιMulti]
      congr 1
      funext i
      fin_cases i
      simp [KaehlerDifferential.map_D]
    unfold logFrame
    rw [formPow_smul, ← mul_smul, hg, mul_assoc, ← mul_pow]
    erw [mul_inv_cancel₀ hϖ0]
    rw [one_pow, mul_one, hF0', hρeq]
    rfl
  · obtain ⟨v, hv, hvg⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
      (j (genericPoint Q)) hgK fun Γ hΓ => by
        rw [hordg Γ hΓ, hexact P hP]
        omega
    rwa [← IsFractionRing.injective O C.functionField (hvg.trans hg.symm)]

/-- **Residues at a point of a normal curve.** Along an adjunction step `j : Q ⟶ C` onto a
point of a normal curve, a rational `m`-canonical form with a pole of order exactly `m` there
has a nonzero Poincaré residue. -/
private theorem exists_isPoincareResidue_ne_zero_of_curve {C Q : Scheme.{0}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] {s : C ⟶ Spec (.of ℂ)}
    (hC : IsNormalVariety ℂ s) (hdim : topologicalKrullDim C = 1) {BC : QDivisor C}
    {j : Q ⟶ C} {BQ : QDivisor Q} (hj : IsAdjunctionStep s BC j BQ) [IsIntegral Q] {m : ℕ}
    (ρ : RationalPluriForms s 1 m) (hρ0 : ρ ≠ 0)
    (hρ : ∀ P : Mori.PrimeDivisor C, j (genericPoint Q) = P.genericPoint →
      P.ordForm ρ = -(m : ℤ)) :
    ∃ ρ' : RationalPluriForms (j ≫ s) 0 m, IsPoincareResidue s j 0 m ρ ρ' ∧ ρ' ≠ 0 := by
  obtain ⟨ϖ, g, hord, hρeq, hunit⟩ :=
    exists_eq_smul_formPow_logFrame_of_curve hC hdim hj ρ fun P hP _ => (hρ P hP).ge
  rw [hρeq]
  exact ⟨_, isPoincareResidue_smul_formPow_logFrame s j hord Fin.elim0 g,
    smul_ne_zero (((hunit hρ hρ0).map (j.stalkMap (genericPoint Q)).hom).ne_zero)
      (tprod_ιMulti_zero_ne_zero m _)⟩

/-- **Residues at a point of a normal curve exist.** Along an adjunction step `j : Q ⟶ C` onto a
point of a normal curve, every rational `m`-canonical form with a pole of order at most `m`
there has a Poincaré residue. -/
private theorem exists_isPoincareResidue_of_curve {C Q : Scheme.{0}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] {s : C ⟶ Spec (.of ℂ)}
    (hC : IsNormalVariety ℂ s) (hdim : topologicalKrullDim C = 1) {BC : QDivisor C}
    {j : Q ⟶ C} {BQ : QDivisor Q} (hj : IsAdjunctionStep s BC j BQ) [IsIntegral Q] {m : ℕ}
    (ρ : RationalPluriForms s 1 m)
    (hρ : ∀ P : Mori.PrimeDivisor C, j (genericPoint Q) = P.genericPoint → ρ ≠ 0 →
      -(m : ℤ) ≤ P.ordForm ρ) :
    ∃ ρ' : RationalPluriForms (j ≫ s) 0 m, IsPoincareResidue s j 0 m ρ ρ' := by
  obtain ⟨ϖ, g, hord, hρeq, -⟩ := exists_eq_smul_formPow_logFrame_of_curve hC hdim hj ρ hρ
  rw [hρeq]
  exact ⟨_, isPoincareResidue_smul_formPow_logFrame s j hord Fin.elim0 g⟩

/-- **Residues of local generators along a floor component exist and are nonzero.** Let
`jT : T ⟶ X` be an adjunction step of the dlt-type pair `(X, B)` (`B ≤ 1`), `T` of dimension
`n`, and `τ` a local generator of `𝒪_X(m(K_X + B))` on an open meeting `jT(T)`. Then `τ` has a
nonzero Poincaré residue along `T`. -/
private theorem exists_isPoincareResidue_ne_zero_of_generatesOn {X T : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X]
    [LocallyOfFiniteType sX] (hXn : IsNormalVariety ℂ sX) {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ)) {B : QDivisor X} (hle : ∀ P, B.coeff P ≤ 1)
    [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T] {jT : T ⟶ X}
    {BT : QDivisor T} (hj : IsAdjunctionStep sX B jT BT) (hdimT : topologicalKrullDim T = n)
    {m : ℕ} {W : X.Opens} {τ : RationalPluriForms sX (n + 1) m} (hτ : GeneratesOn B m W τ)
    (hW : jT (genericPoint T) ∈ W) :
    ∃ ρ : RationalPluriForms (jT ≫ sX) n m, IsPoincareResidue sX jT n m τ ρ ∧ ρ ≠ 0 := by
  obtain ⟨hTn, P, hP1, hPr, hci, -⟩ := id hj
  haveI := hci
  haveI : LocallyOfFiniteType (jT ≫ sX) := hTn.1.toLocallyOfFiniteType
  have hBP : B.coeff P = 1 := le_antisymm (hle P) hP1
  have hjgen : jT (genericPoint T) = P.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq jT P hPr
  have hPW : (P.support ∩ (W : Set X)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hjgen ▸ hW⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hτP : P.ordForm τ = -(m : ℤ) := by
    have := hτ.2 P hPW
    rw [hBP, mul_one] at this
    have h2 : (P.ordForm τ : ℚ) = -(m : ℚ) := by linarith
    exact_mod_cast h2
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    refine exists_isPoincareResidue_ne_zero_of_curve hXn (by rw [hdim]; rfl) hj τ hτ.1
      fun P' hP' => ?_
    obtain rfl : P' = P := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support
      (by
        rw [← hP', hjgen, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl)
    exact hτP
  · obtain ⟨σ, hσ0, hσP, ρσ, hρσ, hρσ0⟩ := exists_simplePole_isPoincareResidue_ne_zero sX hXn
      hnpos (by rw [hdim]; norm_cast) jT hTn hdimT P hPr
    exact exists_isPoincareResidue_ne_zero_of_ordForm_eq hdim hdimT P hjgen hσ0 hσP hρσ
      hρσ0 τ hτ.1 hτP

/-- The stalk map of a closed immersion into a reduced scheme is injective at a point whose image
has a neighbourhood contained in the image. -/
private theorem stalkMap_injective_of_subset_range {A Y : Scheme.{0}} [IsReduced Y] (f : A ⟶ Y)
    [IsClosedImmersion f] (t : A) (V : Y.Opens) (htV : f.base t ∈ V)
    (hV : (V : Set Y) ⊆ Set.range f.base) : Function.Injective (f.stalkMap t).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨W, hxW, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf a
  rw [Scheme.Hom.germ_stalkMap_apply,
    ← map_zero (ConcreteCategory.hom (A.presheaf.germ (f ⁻¹ᵁ W) t hxW))] at ha
  obtain ⟨V', htV', iV, iV', hV'⟩ := TopCat.Presheaf.germ_eq A.presheaf t hxW hxW _ 0 ha
  rw [map_zero] at hV'
  obtain ⟨W₁, hW₁, hW₁V⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.mp V'.isOpen
  let W₂ : Y.Opens := W ⊓ ⟨W₁, hW₁⟩ ⊓ V
  have hxW₂ : f.base t ∈ W₂ := ⟨⟨hxW, show t ∈ f.base ⁻¹' W₁ by rwa [hW₁V]⟩, htV⟩
  let r₂ := (ConcreteCategory.hom (Y.presheaf.map
    (homOfLE (inf_le_left.trans inf_le_left) : W₂ ⟶ W).op)) r
  have hle : f ⁻¹ᵁ W₂ ≤ V' := fun z hz => by
    have : z ∈ f.base ⁻¹' W₁ := hz.1.2
    rwa [hW₁V] at this
  have hz : (ConcreteCategory.hom (f.app W₂)) r₂ = 0 := by
    change (ConcreteCategory.hom (Y.presheaf.map
      (homOfLE (inf_le_left.trans inf_le_left) : W₂ ⟶ W).op ≫ f.app W₂)) r = 0
    rw [Scheme.Hom.naturality, ConcreteCategory.comp_apply]
    have : ((TopologicalSpace.Opens.map f.base).map
        (homOfLE (inf_le_left.trans inf_le_left) : W₂ ⟶ W).op.unop).op =
        iV.op ≫ (homOfLE hle).op :=
      congrArg Quiver.Hom.op (Subsingleton.elim _ _)
    rw [this, Functor.map_comp, ConcreteCategory.comp_apply, hV', map_zero]
  have hr₂ : r₂ = 0 := by
    apply eq_zero_of_basicOpen_eq_bot
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨a', rfl⟩ := hV (Y.basicOpen_le r₂ hy).2
    have : a' ∈ f ⁻¹ᵁ Y.basicOpen r₂ := hy
    rw [Scheme.Hom.preimage_basicOpen, hz, Scheme.basicOpen_zero] at this
    exact this
  rw [← TopCat.Presheaf.germ_res_apply Y.presheaf
    (homOfLE (inf_le_left.trans inf_le_left) : W₂ ⟶ W) (f.base t) hxW₂ r]
  change (ConcreteCategory.hom (Y.presheaf.germ W₂ (f.base t) hxW₂)) r₂ = 0
  rw [hr₂, map_zero]

/-- A strict generization in the specialization order of a scheme. -/
private theorem lt_of_specializes_of_ne {Y : Scheme.{0}} {a b : Y} (h : b ⤳ a) (hne : a ≠ b) :
    a < b :=
  lt_of_le_not_ge h fun h' => hne (Specializes.antisymm (h' : a ⤳ b) h).eq

/-- `d + 1 = n + 1` in `WithBot ℕ∞` forces `d = n`. -/
private theorem eq_natCast_of_add_one_eq_natCast_succ {d : WithBot ℕ∞} {n : ℕ}
    (h : d + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) : d = (n : ℕ) := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add]; exact WithBot.bot_ne_coe)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
      exact ENat.top_ne_coe (n + 1) (by simpa using WithBot.coe_injective this)
    | coe e =>
      have : ((e + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [← h]; norm_cast
      have : e + 1 = n + 1 := by exact_mod_cast this
      norm_cast; omega

/-- On an integral scheme locally of finite type over a field, a prime divisor has codimension
one: its dimension plus one is the dimension of the scheme. -/
private theorem topologicalKrullDim_support_add_one {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    (P : MMP.Mori.PrimeDivisor X) :
    topologicalKrullDim (P.support : Set X) + 1 = topologicalKrullDim X := by
  let _ : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sX)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint P.genericPoint)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint, P.coheight_genericPoint] at h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact_mod_cast h

/-- The images of the floor components are the irreducible components of the floor. -/
private theorem range_mem_irreducibleComponents_of_floor {X T : Scheme.{0}} (ι : T ⟶ X)
    [IsClosedImmersion ι] {B : QDivisor X}
    (hT : Set.range ι.base = ⋃ P ∈ B.roundDown.support, (P.support : Set X))
    {I : Type} (S : I → Scheme.{0}) (n : ∀ i, S i ⟶ T) (P : I → MMP.Mori.PrimeDivisor X)
    (hP : ∀ i, P i ∈ B.roundDown.support) (hPinj : Function.Injective P)
    (hPsurj : ∀ Q ∈ B.roundDown.support, ∃ i, P i = Q)
    (hn : ∀ i, Set.range (n i ≫ ι) = ((P i).support : Set X)) :
    (∀ i, Set.range (n i) ∈ irreducibleComponents T) ∧
      ∀ Z ∈ irreducibleComponents T, ∃! i, Set.range (n i) = Z := by
  have hinj : Function.Injective ι.base := ι.isClosedEmbedding.injective
  have himg : ∀ i, ι.base '' Set.range (n i) = ((P i).support : Set X) := fun i => by
    rw [← hn i, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  -- an irreducible subset of `T` maps into one component of the floor
  have hsub : ∀ Z : Set T, IsIrreducible Z → ∃ i, ι.base '' Z ⊆ ((P i).support : Set X) := by
    intro Z hZ
    have hZ' : IsIrreducible (ι.base '' Z) := hZ.image _ ι.base.hom.continuous.continuousOn
    have hcl := isIrreducible_iff_sUnion_isClosed.mp hZ'
    obtain ⟨W, hW, hZW⟩ := hcl (B.roundDown.support.image fun Q => (Q.support : Set X))
      (by
        intro W hW
        obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hW
        exact Q.idealSheaf.support.isClosed)
      (by
        rintro _ ⟨z, -, rfl⟩
        have : ι.base z ∈ Set.range ι.base := ⟨z, rfl⟩
        rw [hT] at this
        obtain ⟨_, ⟨Q, rfl⟩, hz⟩ := this
        obtain ⟨hQ, hz⟩ := Set.mem_iUnion.mp hz
        exact ⟨_, Finset.mem_image.mpr ⟨Q, hQ, rfl⟩, hz⟩)
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨i, rfl⟩ := hPsurj Q hQ
    exact ⟨i, hZW⟩
  have hirr : ∀ i, IsIrreducible (Set.range (n i)) := fun i => by
    have hgen : (P i).genericPoint ∈ ι.base '' Set.range (n i) := by
      rw [himg i, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    obtain ⟨η, -, hη⟩ := hgen
    have : Set.range (n i) = closure {η} := by
      apply (Set.image_injective.mpr hinj)
      rw [himg i, ← ι.isClosedEmbedding.closure_image_eq, Set.image_singleton, hη,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rw [this]
    exact isIrreducible_singleton.closure
  have hmax : ∀ i, Set.range (n i) ∈ irreducibleComponents T := fun i => by
    refine ⟨hirr i, fun Z hZ hiZ => ?_⟩
    obtain ⟨j, hj⟩ := hsub Z hZ
    have hij : ((P i).support : Set X) ⊆ (P j).support := by
      rw [← himg i]; exact (Set.image_mono hiZ).trans hj
    have hgen : (P i).genericPoint ∈ ((P j).support : Set X) := by
      apply hij
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hji := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hgen
    rw [hji, ← himg i] at hj
    exact (Set.image_subset_image_iff hinj).mp hj
  refine ⟨hmax, fun Z hZ => ?_⟩
  obtain ⟨i, hi⟩ := hsub Z hZ.1
  rw [← himg i] at hi
  have hZi : Z = Set.range (n i) :=
    ((Set.image_subset_image_iff hinj).mp hi).antisymm
      (hZ.2 (hirr i) ((Set.image_subset_image_iff hinj).mp hi))
  refine ⟨i, hZi.symm, fun i' hi' => hPinj ?_⟩
  apply primeDivisor_eq_of_support_eq
  rw [← himg i, ← himg i', hi', hZi]

section FloorBranches

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {B : QDivisor X}
  {T : Scheme.{0}} (ι : T ⟶ X) [IsClosedImmersion ι] [IsReduced T]
variable (hdim : topologicalKrullDim X = (n + 1 : ℕ)) (hK : K.IsCanonicalDivisor sX (n + 1))
  (hproj : MMP.Mori.IsProjectiveVariety k sX) (hQ : IsQFactorial sX)
  (hB : MMP.Fourfold.IsPair sX B) (hdlt : MMP.Intersection.IsDltPair sX B)
  (hB0 : B.roundDown ≠ 0)
  (hT : Set.range ι.base = ⋃ P ∈ B.roundDown.support, (P.support : Set X))

include hdim hK hproj hQ hB hdlt hB0 hT

variable {hfin : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
  (N : MMP.Flips.NormalizationComponents (ι ≫ sX) hfin) (Θ : ∀ i, QDivisor (N.X i))
  (hΘ : ∀ i, IsAdjunctionStep sX B (N.n i ≫ ι) (Θ i))
  (huniq : ∀ P ∈ B.roundDown.support,
    ∃! i, Set.range (N.n i ≫ ι).base = (P.support : Set X))

include hΘ huniq

/-- The floor components are indexed by the prime components of `⌊B⌋`. -/
private theorem exists_primeDivisor_floorComponent :
    ∃ P : N.ι → MMP.Mori.PrimeDivisor X,
      (∀ i, Set.range (N.n i ≫ ι).base = ((P i).support : Set X)) ∧
      (∀ i, P i ∈ B.roundDown.support) ∧ Function.Injective P ∧
      ∀ Q ∈ B.roundDown.support, ∃ i, P i = Q := by
  choose P hP using fun i => (hΘ i).2
  have hPrange : ∀ i, Set.range (N.n i ≫ ι) = ((P i).support : Set X) := fun i => (hP i).2.1
  have hPmem : ∀ i, P i ∈ B.roundDown.support := fun i => by
    rw [Finsupp.mem_support_iff]
    change B.roundDown.coeff (P i) ≠ 0
    rw [DivisorWithCoeffs.coeff_roundDown]
    have h1 : (1 : ℤ) ≤ ⌊B.coeff (P i)⌋ := Int.le_floor.mpr (by exact_mod_cast (hP i).1)
    omega
  have hPinj : Function.Injective P := fun i j hij => by
    obtain ⟨l, -, hl⟩ := huniq (P i) (hPmem i)
    rw [hl i (hPrange i), hl j (show _ = _ by rw [hPrange j, hij])]
  have hPsurj : ∀ Q ∈ B.roundDown.support, ∃ i, P i = Q := fun Q hQ => by
    obtain ⟨i, hi, -⟩ := huniq Q hQ
    exact ⟨i, primeDivisor_eq_of_support_eq (by rwa [← hPrange i])⟩
  exact ⟨P, hPrange, hPmem, hPinj, hPsurj⟩

/-- Every point of the floor lies on a floor component. -/
private theorem exists_mem_range_floorComponent (t : T) : ∃ i, t ∈ Set.range (N.n i).base := by
  obtain ⟨P, hPr, -, -, hPs⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  have ht : ι.base t ∈ Set.range ι.base := ⟨t, rfl⟩
  rw [hT] at ht
  obtain ⟨_, ⟨Q, rfl⟩, ht⟩ := ht
  obtain ⟨hQ, htQ⟩ := Set.mem_iUnion.mp ht
  obtain ⟨i, rfl⟩ := hPs Q hQ
  rw [← hPr i] at htQ
  obtain ⟨y, hy⟩ := htQ
  exact ⟨i, y, ι.isClosedEmbedding.injective (by rw [← hy]; rfl)⟩

/-- Each floor component has dimension `n`. -/
private theorem topologicalKrullDim_floorComponent (i : N.ι) :
    topologicalKrullDim (N.X i) = (n : ℕ) := by
  obtain ⟨P, hPr, -, -, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : IsClosedImmersion (N.n i ≫ ι) := (hΘ i).2.choose_spec.2.2.1
  have e2 : topologicalKrullDim (N.X i) = topologicalKrullDim (Set.range (N.n i ≫ ι)) :=
    (N.n i ≫ ι).isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq
  rw [e2, hPr i]
  have hlft : LocallyOfFiniteType sX := hB.isPair.1.1.toLocallyOfFiniteType
  have h1 := topologicalKrullDim_support_add_one sX (P i)
  rw [hdim] at h1
  exact eq_natCast_of_add_one_eq_natCast_succ h1

/-- **A prime divisor of a floor component has codimension one in the floor.** -/
private theorem coheight_floorComponent_primeDivisor (i : N.ι)
    (Q : MMP.Mori.PrimeDivisor (N.X i)) :
    Order.coheight ((N.n i).base Q.genericPoint) = 1 := by
  haveI : IsClosedImmersion (N.n i ≫ ι) := (hΘ i).2.choose_spec.2.2.1
  haveI : ∀ j, IsClosedImmersion (N.n j) := fun j =>
    haveI : IsClosedImmersion (N.n j ≫ ι) := (hΘ j).2.choose_spec.2.2.1
    IsClosedImmersion.of_comp (N.n j) ι
  have hlft : ∀ j, LocallyOfFiniteType (N.n j ≫ ι ≫ sX) := fun j =>
    (N.isNormalVariety j).1.toLocallyOfFiniteType
  have hdimj := topologicalKrullDim_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  set y := (N.n i).base Q.genericPoint with hy
  -- the dimension of the closure of `y`
  have hdy : topologicalKrullDim (closure {y} : Set T) + 1 = (n : WithBot ℕ∞) := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (N.n i ≫ ι ≫ sX)
      Q.genericPoint
    rw [Q.coheight_genericPoint, hdimj i] at h
    have himg : (N.n i).base '' closure {Q.genericPoint} = closure {y} := by
      rw [← (N.n i).isClosedEmbedding.closure_image_eq, Set.image_singleton]
    rw [← himg, ← ((N.n i).isClosedEmbedding.isEmbedding.homeomorphImage
      (closure {Q.genericPoint})).isHomeomorph.topologicalKrullDim_eq]
    exact_mod_cast h
  refine le_antisymm ?_ ?_
  · by_contra hlt
    have h2 : ((2 : ℕ) : ℕ∞) ≤ Order.coheight y := by
      rw [not_le] at hlt
      exact Order.add_one_le_of_lt hlt
    obtain ⟨p, hp0, hplen⟩ := Order.exists_series_of_le_coheight y h2
    have h01 : p ⟨0, by omega⟩ < p ⟨1, by omega⟩ := p.strictMono (by simp [Fin.lt_def])
    have h12 : p ⟨1, by omega⟩ < p ⟨2, by omega⟩ := p.strictMono (by simp [Fin.lt_def])
    obtain ⟨j, q2, hq2⟩ := exists_mem_range_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
      hΘ huniq (p ⟨2, by omega⟩)
    have hcl : ∀ z : T, p ⟨2, by omega⟩ ⤳ z → z ∈ Set.range (N.n j).base := fun z hz =>
      (N.n j).isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr ⟨q2, hq2⟩) (specializes_iff_mem_closure.mp hz)
    obtain ⟨q1, hq1⟩ := hcl _ h12.le
    obtain ⟨q0, hq0⟩ := hcl _ (h01.le.trans h12.le)
    have hsp : ∀ {a b : N.X j}, (N.n j).base a ⤳ (N.n j).base b → a ⤳ b := fun h =>
      ((N.n j).isClosedEmbedding.isInducing.specializes_iff).mp h
    have hl01 : q0 < q1 := lt_of_specializes_of_ne (hsp (by rw [hq0, hq1]; exact h01.le))
      (fun h => h01.ne (by rw [← hq0, ← hq1, h]))
    have hl12 : q1 < q2 := lt_of_specializes_of_ne (hsp (by rw [hq1, hq2]; exact h12.le))
      (fun h => h12.ne (by rw [← hq1, ← hq2, h]))
    have hc0 : (2 : ℕ∞) ≤ Order.coheight q0 := by
      calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ Order.coheight q2 + 1 + 1 := by gcongr; exact bot_le
        _ ≤ Order.coheight q1 + 1 := by gcongr; exact Order.coheight_add_one_le hl12
        _ ≤ Order.coheight q0 := Order.coheight_add_one_le hl01
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (N.n j ≫ ι ≫ sX) q0
    rw [hdimj j] at h
    have himg : (N.n j).base '' closure {q0} = closure {y} := by
      rw [← (N.n j).isClosedEmbedding.closure_image_eq, Set.image_singleton, hq0, ← hp0]
      rfl
    rw [((N.n j).isClosedEmbedding.isEmbedding.homeomorphImage
      (closure {q0})).isHomeomorph.topologicalKrullDim_eq, himg] at h
    -- `dim closure {y} = n - 1` and `coheight q0 ≥ 2` contradict `dim + coheight = n`
    induction hd : topologicalKrullDim (closure {y} : Set T) using WithBot.recBotCoe with
    | bot => rw [hd, WithBot.bot_add] at hdy; exact WithBot.bot_ne_coe hdy
    | coe d =>
      rw [hd] at hdy h
      have h' : d + Order.coheight q0 = n := by exact_mod_cast h
      have hdy' : d + 1 = n := by exact_mod_cast hdy
      have : d + 2 ≤ d + 1 := by
        calc d + 2 ≤ d + Order.coheight q0 := by gcongr
          _ = d + 1 := by rw [h', hdy']
      induction d using ENat.recTopCoe with
      | top => simp at hdy'
      | coe d => norm_cast at this; omega
  · -- the generic point of the component strictly generizes `y`
    have hne : Q.genericPoint ≠ genericPoint (N.X i) := by
      intro h
      apply MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support Q
      rw [← h, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hlt : y < (N.n i).base (genericPoint (N.X i)) :=
      lt_of_specializes_of_ne
        ((genericPoint_specializes Q.genericPoint).map (N.n i).base.hom.continuous)
        (fun h => hne ((N.n i).isClosedEmbedding.injective h))
    have := Order.coheight_add_one_le hlt
    calc (1 : ℕ∞) = 0 + 1 := by simp
      _ ≤ _ := by gcongr; exact bot_le
      _ ≤ _ := this

/-- At a point lying on a single floor component, the stalk of the floor is the stalk of the
component. -/
private theorem bijective_stalkMap_floorComponent (i : N.ι) (t : N.X i)
    (ht : ∀ j, j ≠ i → (N.n i).base t ∉ Set.range (N.n j).base) :
    Function.Bijective ((N.n i).stalkMap t).hom := by
  classical
  obtain ⟨P, -, hPmem, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : Finite N.ι := Finite.of_injective
    (fun i => (⟨P i, hPmem i⟩ : {Q // Q ∈ B.roundDown.support}))
    fun a b h => hPinj (congrArg Subtype.val h)
  haveI : ∀ j, IsClosedImmersion (N.n j) := fun j =>
    haveI : IsClosedImmersion (N.n j ≫ ι) := (hΘ j).2.choose_spec.2.2.1
    IsClosedImmersion.of_comp (N.n j) ι
  let V : T.Opens := ⟨(⋃ j ∈ ({i}ᶜ : Set N.ι), Set.range (N.n j).base)ᶜ, by
    refine (Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ =>
      (N.n j).isClosedEmbedding.isClosed_range).isOpen_compl⟩
  have htV : (N.n i).base t ∈ V := by
    simp only [V, TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun j hj => ht j hj
  have hV : (V : Set T) ⊆ Set.range (N.n i).base := by
    intro z hz
    obtain ⟨j, hj⟩ := exists_mem_range_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
      hΘ huniq z
    by_cases hji : j = i
    · exact hji ▸ hj
    · exact absurd (Set.mem_iUnion₂.mpr ⟨j, hji, hj⟩) hz
  exact ⟨stalkMap_injective_of_subset_range (N.n i) t V htV hV, (N.n i).stalkMap_surjective t⟩

/-- The image of the generic point of a floor component is the generic point of an irreducible
component of the floor. -/
private theorem closure_mem_irreducibleComponents_floorComponent (i : N.ι) :
    closure {(N.n i).base (genericPoint (N.X i))} ∈ irreducibleComponents T := by
  obtain ⟨P, hPr, hPmem, hPinj, hPs⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : ∀ j, IsClosedImmersion (N.n j) := fun j =>
    haveI : IsClosedImmersion (N.n j ≫ ι) := (hΘ j).2.choose_spec.2.2.1
    IsClosedImmersion.of_comp (N.n j) ι
  have h := (range_mem_irreducibleComponents_of_floor ι hT N.X N.n P hPmem hPinj hPs hPr).1 i
  rwa [← Set.image_singleton, (N.n i).isClosedEmbedding.closure_image_eq,
    (genericPoint_spec (N.X i)).def, Set.image_univ]

/-- The generic point of a floor component has codimension zero in the floor. -/
private theorem coheight_genericPoint_floorComponent (i : N.ι) :
    Order.coheight ((N.n i).base (genericPoint (N.X i))) = 0 := by
  rw [Order.coheight_eq_zero]
  intro z hz
  have hc := closure_mem_irreducibleComponents_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT
    N Θ hΘ huniq i
  have hsub : closure {(N.n i).base (genericPoint (N.X i))} ⊆ closure {z} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hz))
      isClosed_closure
  have := hc.2 isIrreducible_singleton.closure hsub
  exact specializes_iff_mem_closure.mpr (this (subset_closure rfl))

/-- A codimension-one point on a single floor component is a regular point of the floor. -/
private theorem isRegularLocalRing_stalk_of_single (i : N.ι) (t : N.X i)
    (ht1 : Order.coheight t = 1)
    (ht : ∀ j, j ≠ i → (N.n i).base t ∉ Set.range (N.n j).base) :
    IsRegularLocalRing (T.presheaf.stalk ((N.n i).base t)) := by
  set E := AlgebraicGeometry.PrimeDivisor.ofCoheightOne t ht1
  have hE : E.genericPoint = t := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hdvr := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing (X := N.X i) E
  have hreg : IsRegularLocalRing ((N.X i).presheaf.stalk t) := by
    rw [← hE]
    infer_instance
  have hbij := bijective_stalkMap_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
    i t ht
  exact IsRegularLocalRing.of_ringEquiv (RingEquiv.ofBijective _ hbij).symm

/-- A point on a single floor component is not in the double locus. -/
private theorem notMem_doubleIntersectionLocus_of_single (i : N.ι) (t : N.X i)
    (ht : ∀ j, j ≠ i → (N.n i).base t ∉ Set.range (N.n j).base) :
    (N.n i).base t ∉ (MMP.Flips.doubleIntersectionLocus T : Set T) := by
  classical
  obtain ⟨P, -, hPmem, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : Finite N.ι := Finite.of_injective
    (fun i => (⟨P i, hPmem i⟩ : {Q // Q ∈ B.roundDown.support}))
    fun a b h => hPinj (congrArg Subtype.val h)
  haveI : ∀ j, IsClosedImmersion (N.n j) := fun j =>
    haveI : IsClosedImmersion (N.n j ≫ ι) := (hΘ j).2.choose_spec.2.2.1
    IsClosedImmersion.of_comp (N.n j) ι
  let V : Set T := (⋃ j ∈ ({i}ᶜ : Set N.ι), Set.range (N.n j).base)ᶜ
  have hVo : IsOpen V := (Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ =>
      (N.n j).isClosedEmbedding.isClosed_range).isOpen_compl
  have htV : (N.n i).base t ∈ V := by
    simp only [V, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun j hj => ht j hj
  intro hmem
  obtain ⟨s, hsV, hsS⟩ := mem_closure_iff.mp hmem V hVo htV
  obtain ⟨hs1, hsreg⟩ := hsS
  obtain ⟨j, s', rfl⟩ := exists_mem_range_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
    hΘ huniq s
  have hji : j = i := by
    by_contra h
    exact hsV (Set.mem_iUnion₂.mpr ⟨j, h, s', rfl⟩)
  subst hji
  have hsingle : ∀ l, l ≠ j → (N.n j).base s' ∉ Set.range (N.n l).base := fun l hl h =>
    hsV (Set.mem_iUnion₂.mpr ⟨l, hl, h⟩)
  -- the codimension of `s'` in its component is one
  have hmono : StrictMono (N.n j).base := fun a b hab =>
    lt_of_specializes_of_ne (hab.le.map (N.n j).base.hom.continuous)
      (fun h => hab.ne ((N.n j).isClosedEmbedding.injective h))
  have hle := Order.coheight_le_coheight_apply_of_strictMono _ hmono s'
  rw [hs1] at hle
  have hne : s' ≠ genericPoint (N.X j) := by
    rintro rfl
    rw [coheight_genericPoint_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq j]
      at hs1
    exact zero_ne_one hs1
  have hge : 1 ≤ Order.coheight s' := by
    have hlt : s' < genericPoint (N.X j) :=
      lt_of_specializes_of_ne (genericPoint_specializes s') hne
    have := Order.coheight_add_one_le hlt
    calc (1 : ℕ∞) = 0 + 1 := by simp
      _ ≤ _ := by gcongr; exact bot_le
      _ ≤ _ := this
  exact hsreg (isRegularLocalRing_stalk_of_single ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
    j s' (le_antisymm hle hge) hsingle)

/-- **A conductor component of the dlt floor has a second branch.** If a prime divisor `P` of a
floor component `Tᵢ` lies over the double locus of the floor, then the point `νᵢ(P)` is also the
image of the generic point of a prime divisor `P'` of a different floor component `Tⱼ`. -/
private theorem exists_other_branch (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i))
    (hD : (N.n i).base P.genericPoint ∈ (MMP.Flips.doubleIntersectionLocus T : Set T)) :
    ∃ (j : N.ι) (P' : MMP.Mori.PrimeDivisor (N.X j)),
      (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint ∧
      (⟨i, P.genericPoint⟩ : Σ i, N.X i) ≠ ⟨j, P'.genericPoint⟩ := by
  classical
  by_contra hno
  refine notMem_doubleIntersectionLocus_of_single ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
    i P.genericPoint (fun j hji hmem => hno ?_) hD
  obtain ⟨y, hy⟩ := hmem
  haveI : ∀ j, IsClosedImmersion (N.n j) := fun j =>
    haveI : IsClosedImmersion (N.n j ≫ ι) := (hΘ j).2.choose_spec.2.2.1
    IsClosedImmersion.of_comp (N.n j) ι
  have hcoh := coheight_floorComponent_primeDivisor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ
    huniq i P
  have hmono : StrictMono (N.n j).base := fun a b hab =>
    lt_of_specializes_of_ne (hab.le.map (N.n j).base.hom.continuous)
      (fun h => hab.ne ((N.n j).isClosedEmbedding.injective h))
  have hle := Order.coheight_le_coheight_apply_of_strictMono _ hmono y
  rw [hy, hcoh] at hle
  have hne : y ≠ genericPoint (N.X j) := by
    rintro rfl
    have h0 := coheight_genericPoint_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ
      huniq j
    rw [hy, hcoh] at h0
    exact one_ne_zero h0
  have hge : 1 ≤ Order.coheight y := by
    have hlt : y < genericPoint (N.X j) :=
      lt_of_specializes_of_ne ((genericPoint_spec (N.X j)).specializes trivial) hne
    have := Order.coheight_add_one_le hlt
    calc (1 : ℕ∞) = 0 + 1 := by simp
      _ ≤ _ := by gcongr; exact bot_le
      _ ≤ _ := this
  have hE : (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y (le_antisymm hle hge)).genericPoint =
      y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨j, AlgebraicGeometry.PrimeDivisor.ofCoheightOne y (le_antisymm hle hge), ?_, ?_⟩
  · exact hy.symm.trans (congrArg _ hE.symm)
  · intro h
    exact hji (congrArg Sigma.fst h).symm

end FloorBranches

/-- A discrepancy `a(E, X, Δ)` of a divisor `(Y, f, E)` over `X` whose centre is the generic point
of a prime divisor `P` of `X` is `-coeff_P(Δ)`. -/
private theorem isDiscrepancy_eq_neg_coeff_of_map_genericPoint_eq {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : MMP.Mori.IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : MMP.Mori.DivisorOver k sX}
    {P : MMP.Mori.PrimeDivisor X} (hP : D.f D.E.genericPoint = P.genericPoint) {a : ℚ}
    (h : MMP.Mori.IsDiscrepancy sX n K Δ D a) : a = -Δ.coeff P := by
  obtain ⟨hX', hK, m, hm, hC, U, hU, τ, hτ, hτa⟩ := h
  refine MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX (P := P)
    ⟨hX', hK, m, hm, hC, U, ?_, τ, hτ, ?_⟩
  · convert hU using 2
    exact hP.symm
  · rw [hτa, MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX
      hK.topologicalKrullDim_eq
      (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX D P hP)]

/-- The image of a section in the function field does not change under restriction. -/
private theorem germToFunctionField_app_res {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : MMP.Flips.NormalizationComponents sT hT) (i : N.ι) {U U' : T.Opens} (hU : U' ≤ U) (f : Γ(T, U))
    [Nonempty (N.n i ⁻¹ᵁ U')] [Nonempty (N.n i ⁻¹ᵁ U)] :
    ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom ((N.n i).app U' (f |_ U')) =
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) := by
  have h := congrArg (fun φ => ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom (φ.hom f))
    ((N.n i).naturality (homOfLE hU).op)
  simp only [CommRingCat.comp_apply] at h
  change ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom
    ((N.n i).app U' (T.presheaf.map (homOfLE hU).op f)) = _
  rw [h]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- A family `φ` of rational functions on the normalization components *descends on* `V` if it
is the pull-back of a function on `V`. -/
private def DescendsOn {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : MMP.Flips.NormalizationComponents sT hT) (φ : ∀ i, (N.X i).functionField) (V : T.Opens) : Prop :=
  ∃ b : Γ(T, V), ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ V)),
    φ i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V)).hom ((N.n i).app V b)

/-- Descent is inherited by smaller opens. -/
private theorem DescendsOn.mono {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : MMP.Flips.NormalizationComponents sT hT} {φ : ∀ i, (N.X i).functionField} {V V' : T.Opens}
    (h : DescendsOn N φ V) (hV : V' ≤ V) : DescendsOn N φ V' := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b |_ V', fun i hi => ?_⟩
  have : Nonempty (N.n i ⁻¹ᵁ V) := ⟨⟨hi.some.1, hV hi.some.2⟩⟩
  rw [germToFunctionField_app_res N i hV b]
  exact hb i this

/-- On a reduced scheme a nonzero section has a nonzero germ at a generic point of an
irreducible component. -/
private theorem exists_mem_genericPoints_germ_ne_zero' {Y : Scheme.{0}} [IsReduced Y]
    {V : Y.Opens} (t : Γ(Y, V)) (ht : t ≠ 0) :
    ∃ (y : Y) (hy : y ∈ V), y ∈ genericPoints Y ∧ Y.presheaf.germ V y hy t ≠ 0 := by
  have hb : Y.basicOpen t ≠ ⊥ := fun h => ht ((basicOpen_eq_bot_iff t).mp h)
  obtain ⟨z, hz⟩ : ∃ z, z ∈ Y.basicOpen t := by
    by_contra! h
    exact hb (eq_bot_iff.2 fun x hx => (h x hx).elim)
  let C : irreducibleComponents Y :=
    ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
  have hηz : (genericPoints.ofComponent C).1 ⤳ z := specializes_iff_mem_closure.mpr <|
    (genericPoints.isGenericPoint_ofComponent C).symm ▸ mem_irreducibleComponent
  have hηb : (genericPoints.ofComponent C).1 ∈ Y.basicOpen t :=
    hηz.mem_open (Y.basicOpen t).isOpen hz
  have hηV : (genericPoints.ofComponent C).1 ∈ V := Y.basicOpen_le t hηb
  refine ⟨_, hηV, (genericPoints.ofComponent C).2, ?_⟩
  exact ((Y.mem_basicOpen t _ hηV).mp hηb).ne_zero

/-- **Generic points of `T` come from the normalization components.** Every generic point `η` of
an irreducible component of the reduced scheme `T` is the image `νᵢ(ηᵢ)` of the generic point of a
normalization component, and `νᵢ` is an isomorphism of local rings there. -/
private theorem exists_base_genericPoint_eq {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    [IsReduced T] (N : MMP.Flips.NormalizationComponents sT hT) {η : T} (hη : η ∈ genericPoints T) :
    ∃ i, (N.n i).base (genericPoint (N.X i)) = η ∧
      IsIso ((N.n i).stalkMap (genericPoint (N.X i))) := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  have hbir : IsBirational (MMP.Flips.slcCurveNormalization T hT) := Scheme.isBirational_normalization T hT
  obtain ⟨w, hw, hwη⟩ := hbir.1.surjOn hη
  obtain ⟨⟨i, u⟩, hu⟩ := (sigmaMk N.X).surjective (φ.inv.base w)
  set e := Limits.Sigma.ι N.X i ≫ φ.hom with he
  have heu : e.base u = w := by
    have h2 : φ.hom.base (φ.inv.base w) = w := by
      rw [← Scheme.Hom.comp_apply φ.inv φ.hom, Iso.inv_hom_id]
      rfl
    rw [he, Scheme.Hom.comp_apply, ← sigmaMk_mk, hu, h2]
  have hne : e ≫ MMP.Flips.slcCurveNormalization T hT = N.n i := by
    rw [he, Category.assoc, hφ, Limits.Sigma.ι_desc]
  have hu0 : u = genericPoint (N.X i) := by
    have hmax : IsMax w := Stacks.Chow.isMax_of_mem_genericPoints ⟨w, hw⟩
    have h1 : genericPoint (N.X i) ⤳ u :=
      (genericPoint_spec (N.X i)).specializes (Set.mem_univ u)
    have h2 : e.base u ≤ e.base (genericPoint (N.X i)) :=
      Scheme.le_iff_specializes.mpr (h1.map e.continuous)
    rw [heu] at h2
    have h3 := hmax h2
    rw [← heu, Scheme.le_iff_specializes] at h3
    have h4 : u ⤳ genericPoint (N.X i) := e.isOpenEmbedding.toIsInducing.specializes_iff.mp h3
    exact (h4.antisymm h1).eq
  subst hu0
  refine ⟨i, ?_, ?_⟩
  · rw [← hne]
    change (MMP.Flips.slcCurveNormalization T hT).base (e.base _) = η
    rw [heu, hwη]
  · have key : ∀ g : N.X i ⟶ T, g = e ≫ MMP.Flips.slcCurveNormalization T hT →
        IsIso (g.stalkMap (genericPoint (N.X i))) := by
      intro g hg
      subst hg
      rw [Scheme.Hom.stalkMap_comp]
      haveI h1 : IsIso ((MMP.Flips.slcCurveNormalization T hT).stalkMap
          (e.base (genericPoint (N.X i)))) := by
        rw [heu]; exact hbir.2 w hw
      have h2 : IsIso (e.stalkMap (genericPoint (N.X i))) :=
        IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
    exact key _ hne.symm

/-- **A function on `T` is detected on the normalization.** A nonzero function on an open `V` of
the reduced scheme `T` has a nonzero pull-back to the function field of some normalization
component meeting `V`: it has a nonzero germ at a generic point of `T`, where the normalization
is an isomorphism of local rings. -/
private theorem exists_germToFunctionField_ne_zero {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    [IsReduced T] (N : MMP.Flips.NormalizationComponents sT hT) {V : T.Opens} (c : Γ(T, V))
    (hc : c ≠ 0) : ∃ i, ∃ _ : Nonempty (N.n i ⁻¹ᵁ V),
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V)).hom ((N.n i).app V c) ≠ 0 := by
  obtain ⟨η, hηV, hη, hgerm⟩ := exists_mem_genericPoints_germ_ne_zero' c hc
  obtain ⟨i, hηeq, hiso⟩ := exists_base_genericPoint_eq N hη
  subst hηeq
  haveI : Nonempty (N.n i ⁻¹ᵁ V) := ⟨⟨_, hηV⟩⟩
  refine ⟨i, inferInstance, ?_⟩
  intro h0
  apply hgerm
  have h1 := Scheme.Hom.germ_stalkMap_apply (N.n i) V (genericPoint (N.X i)) hηV c
  apply (ConcreteCategory.bijective_of_isIso ((N.n i).stalkMap (genericPoint (N.X i)))).1
  rwa [h1, map_zero]

/-- **Descents glue.** On the reduced scheme `T`, a function is determined by its pull-backs to
the normalization components, so descents over the members of a family of opens glue to a descent
over their union. -/
private theorem descendsOn_iSup {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : MMP.Flips.NormalizationComponents sT hT} [IsReduced T] {φ : ∀ i, (N.X i).functionField}
    {ι : Type} (V : ι → T.Opens) (hV : ∀ j, DescendsOn N φ (V j)) :
    DescendsOn N φ (⨆ j, V j) := by
  choose b hb using hV
  have hcompat : TopCat.Presheaf.IsCompatible T.presheaf V b := by
    intro j j'
    by_contra hne
    obtain ⟨i, hi, hi0⟩ := exists_germToFunctionField_ne_zero N _ (sub_ne_zero.mpr hne)
    apply hi0
    have hj : Nonempty (N.n i ⁻¹ᵁ V j) := ⟨⟨hi.some.1, hi.some.2.1⟩⟩
    have hj' : Nonempty (N.n i ⁻¹ᵁ V j') := ⟨⟨hi.some.1, hi.some.2.2⟩⟩
    rw [map_sub, map_sub, sub_eq_zero]
    have e1 := germToFunctionField_app_res N i (inf_le_left : V j ⊓ V j' ≤ V j) (b j)
    have e2 := germToFunctionField_app_res N i (inf_le_right : V j ⊓ V j' ≤ V j') (b j')
    exact e1.trans ((hb j i hj).symm.trans ((hb j' i hj').trans e2.symm))
  obtain ⟨t, ht, -⟩ := T.sheaf.existsUnique_gluing V b hcompat
  refine ⟨t, fun i hi => ?_⟩
  obtain ⟨x, hx⟩ := hi.some
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hne : Nonempty (N.n i ⁻¹ᵁ V j) := ⟨⟨x, hj⟩⟩
  have hle : V j ≤ iSup V := le_iSup V j
  have e1 := germToFunctionField_app_res N i hle t
  have e2 : t |_ V j = b j := ht j
  exact (hb j i hne).trans ((congrArg (fun s => ((N.X i).germToFunctionField
    (N.n i ⁻¹ᵁ V j)).hom ((N.n i).app (V j) s)) e2).symm.trans e1)

/-- In the one-dimensional space of rational `m`-canonical top forms, every form is a multiple
of a given nonzero one. -/
private theorem exists_eq_smul_of_ne_zero {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] {d : ℕ}
    (hd : topologicalKrullDim Y = d) {m : ℤ} {ρ : RationalPluriForms sY d m} (hρ : ρ ≠ 0)
    (τ : RationalPluriForms sY d m) : ∃ c : Y.functionField, τ = c • ρ := by
  letI := functionFieldAlgebra sY
  obtain ⟨b⟩ := exists_basis_topForms (sX := sY) hd
  let bb : Module.Basis Unit Y.functionField (RationalPluriForms sY d m) := ZTensorPower.basis b m
  have hrank : Module.finrank Y.functionField (RationalPluriForms sY d m) = 1 := by
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ρ hρ).mp hrank τ
  exact ⟨c, hc.symm⟩

/-- The `k`-homomorphism of function fields `k(X) → k(T)` of a dominant morphism `h : T ⟶ X`
over `k`. -/
private noncomputable def ffHom {k : Type u} [Field k] {X T : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sT : T ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral T] (h : T ⟶ X) [IsDominant h]
    (hT : h ≫ sX = sT) : FunctionFieldHom sT sX :=
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sT
  { toRingHom := functionFieldMap h
    commutes' := fun c => by
      subst hT
      letI := functionFieldMapAlgebra h
      have := isScalarTower_functionFieldMap sX h
      exact (IsScalarTower.algebraMap_apply k X.functionField T.functionField c).symm }

/-- The pull-back of forms along a dominant morphism is the pluriform pull-back along any
function field equivalence inducing `functionFieldMap`. -/
private theorem pullbackRationalPluriForms_eq_pluriformPullback {k : Type u} [Field k]
    {X T : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral T] (h : T ⟶ X)
    [IsDominant h] (σ : FunctionFieldEquiv (h ≫ sX) sX) (hσ : ∀ a, σ a = functionFieldMap h a)
    {d : ℕ} {m : ℤ} (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms sX h τ = pluriformPullback (h ≫ sX) sX σ.toHom d m τ := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (h ≫ sX)
  have e : σ.toHom = ffHom h rfl := AlgHom.ext fun a => hσ a
  rw [e]
  rfl

/-- The pull-back of rational forms is `k(W)`-semilinear along `g^* : k(W) → k(V)`. -/
private theorem pullbackRationalPluriForms_smul' {k : Type u} [Field k] {V W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] [IsIntegral V] (g : V ⟶ W) [IsDominant g] {d : ℕ}
    {m : ℤ} (a : W.functionField) (τ : RationalPluriForms sW d m) :
    pullbackRationalPluriForms sW g (a • τ) =
      functionFieldMap g a • pullbackRationalPluriForms sW g τ := by
  let := functionFieldAlgebra sW
  let := functionFieldAlgebra (g ≫ sW)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sW g
  exact pullbackForms_smul (K := W.functionField) (K' := V.functionField) (m := m) a τ

/-- Transport of an equation `a = c • b` along equal structure morphisms. -/
private theorem eq_smul_of_heq {Y : Scheme.{0}} [IsIntegral Y] {s s' : Y ⟶ Spec (.of ℂ)}
    (h : s = s') {d : ℕ} {m : ℤ} {a b : RationalPluriForms s d m}
    {a' b' : RationalPluriForms s' d m} (ha : HEq a a') (hb : HEq b b') (c : Y.functionField)
    (h' : a' = c • b') : a = c • b := by
  subst h
  cases ha
  cases hb
  exact h'

/-- The order of a form along a prime divisor does not depend on the spelling of the structure
morphism. -/
private theorem ordForm_congr_heq {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {s s' : Y ⟶ Spec (.of ℂ)} (h : s = s') {d : ℕ} {m : ℤ}
    {a : RationalPluriForms s d m} {a' : RationalPluriForms s' d m} (ha : HEq a a')
    (Γ : Mori.PrimeDivisor Y) : Γ.ordForm a = Γ.ordForm a' := by
  subst h
  cases ha
  rfl

/-- The image of a prime divisor under an isomorphism. -/
private theorem exists_primeDivisor_genericPoint_eq_of_iso {C T : Scheme.{0}} (p : C ≅ T)
    (Γ : Mori.PrimeDivisor C) :
    ∃ Γ' : Mori.PrimeDivisor T, Γ'.genericPoint = p.hom Γ.genericPoint := by
  have hmono : ∀ {A A' : Scheme.{0}} (g : A ⟶ A') [IsIso g], StrictMono g.base := by
    intro A A' g _
    exact fun a b hab => lt_of_specializes_of_ne (hab.le.map g.base.hom.continuous)
      (fun h => hab.ne (g.isClosedEmbedding.injective h))
  have hcoh : Order.coheight (p.hom Γ.genericPoint) = 1 := by
    refine le_antisymm ?_ ?_
    · have h1 := Order.coheight_le_coheight_apply_of_strictMono _ (hmono p.inv)
        (p.hom Γ.genericPoint)
      have hinv : p.inv (p.hom Γ.genericPoint) = Γ.genericPoint := by
        rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
      rw [hinv, Γ.coheight_genericPoint] at h1
      exact h1
    · have h1 := Order.coheight_le_coheight_apply_of_strictMono _ (hmono p.hom) Γ.genericPoint
      rw [Γ.coheight_genericPoint] at h1
      exact h1
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _⟩

/-- **Orders along an isomorphism.** The order of the pull-back of a form along an isomorphism
`p : C ≅ T` along a prime divisor `Γ` is the order of the form along `p(Γ)`. -/
private theorem ordForm_pullback_eq_of_iso {C T : Scheme.{0}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {sT : T ⟶ Spec (.of ℂ)} (hT : IsNormalVariety ℂ sT) {d : ℕ} (hdT : topologicalKrullDim T = d)
    (p : C ≅ T) (hCn : IsNormalVariety ℂ (p.hom ≫ sT)) (Γ : Mori.PrimeDivisor C)
    (Γ' : Mori.PrimeDivisor T) (hΓ : Γ'.genericPoint = p.hom Γ.genericPoint) {m : ℤ}
    (τ : RationalPluriForms sT d m) :
    Γ.ordForm (pullbackRationalPluriForms sT p.hom τ) = Γ'.ordForm τ := by
  set D : DivisorOver ℂ sT := ⟨C, p.hom, hCn, isBirationalMorphism_of_isIso _, Γ⟩
  have hv := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hT D Γ' hΓ.symm
  have h1 := MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hT hdT hv τ
  rw [DivisorOver.ordPullback_ofPrimeDivisor hT hdT Γ' τ] at h1
  exact h1

/-- Every point of a scheme lies on a normalization component. -/
private theorem exists_base_eq' {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : MMP.Flips.NormalizationComponents sT hT) (x : T) : ∃ i z, (N.n i).base z = x := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  have hsurj : Surjective (MMP.Flips.slcCurveNormalization T hT) := Scheme.surjective_normalization T hT
  obtain ⟨w, rfl⟩ := hsurj.surj x
  obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk N.X).surjective (φ.inv.base w)
  refine ⟨i, z, ?_⟩
  have h1 : (Limits.Sigma.ι N.X i ≫ φ.hom ≫ MMP.Flips.slcCurveNormalization T hT).base z =
      (N.n i).base z := by
    rw [hφ, Limits.Sigma.ι_desc]
  have h2 : φ.hom.base (φ.inv.base w) = w := by
    rw [← Scheme.Hom.comp_apply φ.inv φ.hom, Iso.inv_hom_id]
    rfl
  rw [← h1, Scheme.Hom.comp_apply, ← sigmaMk_mk, hz, Scheme.Hom.comp_apply, h2]

/-- **Functions on a reduced scheme are detected on its normalization.** A function on an open
`U` of the reduced scheme `T` whose pull-back to every normalization component meeting `U`
vanishes in the function field is zero. -/
private theorem eq_zero_of_forall_germToFunctionField_eq_zero {k : Type} [Field k]
    {T : Scheme.{0}} [IsReduced T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : MMP.Flips.NormalizationComponents sT hT) {U : T.Opens} (b : Γ(T, U))
    (h : ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U b) = 0) : b = 0 := by
  rw [← basicOpen_eq_bot_iff]
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨i, z, rfl⟩ := exists_base_eq' N x
  have hzU : z ∈ N.n i ⁻¹ᵁ U := T.basicOpen_le b hx
  haveI : Nonempty (N.n i ⁻¹ᵁ U) := ⟨⟨z, hzU⟩⟩
  have hz : z ∈ (N.X i).basicOpen ((N.n i).app U b) := by
    rw [← Scheme.preimage_basicOpen]
    exact hx
  have h0 : (N.n i).app U b = 0 :=
    (N.X i).germToFunctionField_injective (N.n i ⁻¹ᵁ U) ((h i inferInstance).trans (map_zero _).symm)
  rw [h0, Scheme.basicOpen_zero] at hz
  exact hz

/-- **Residues of unit multiples.** If `τ = r τ'` for a function `r` on an open `V` containing
the generic point of the floor component `S`, then `Res_S τ = (r|_S) Res_S τ'`. -/
private theorem isPoincareResidue_eq_germ_smul {Y S : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY]
    [IsIntegral S] {j : S ⟶ Y} {BY : QDivisor Y} {BS : QDivisor S}
    (hS : IsAdjunctionStep sY BY j BS) {n m : ℕ} {V : Y.Opens} [Nonempty V]
    [Nonempty (j ⁻¹ᵁ V)] (hV : j (genericPoint S) ∈ V) (r : Γ(Y, V))
    {τ τ' : RationalPluriForms sY (n + 1) m} (hτ : τ = (Y.germToFunctionField V).hom r • τ')
    {ρ ρ' : RationalPluriForms (j ≫ sY) n m} (hρ : IsPoincareResidue sY j n m τ ρ)
    (hρ' : IsPoincareResidue sY j n m τ' ρ') :
    ρ = (S.germToFunctionField (j ⁻¹ᵁ V)).hom (j.app V r) • ρ' := by
  have h1 := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ'
    (Y.presheaf.germ V _ hV r)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, ← hτ, Scheme.Hom.germ_stalkMap_apply] at h1
  exact IsPoincareResidue.unique hS hρ h1

/-- **Gluing the local sections of `ι_V^* 𝒪_R(arH)`.** Functions `G_U` on `V ∩ U`, one for
each local equation `e` of the Cartier divisor `H` on `U`, which transform as `G_{U₁} d^r = G_{U₂}`
under the transition function `d` with `e₁^{-1} = d e₂^{-1}`, glue to a global section of
`ι_V^* 𝒪_R(arH)` equal to `G_U^a e^{-ar}` on every `U`. -/
private theorem exists_glued_section {R V : Scheme.{0}} [IsIntegral R] [IsLocallyNoetherian R]
    [IsNormal R] (ιV : V ⟶ R) {H : Divisor R} (hH : H.IsCartier) (a r : ℕ)
    (G : ∀ (U : R.Opens) (e : (RationalFunctions R)ˣ), H.IsLocalEquation U e → Γ(V, ιV ⁻¹ᵁ U))
    (hG : ∀ (U₁ U₂ : R.Opens) (e₁ e₂ : (RationalFunctions R)ˣ) (he₁ : H.IsLocalEquation U₁ e₁)
      (he₂ : H.IsLocalEquation U₂ e₂) (d : Γ(R, U₁ ⊓ U₂)),
      d • H.divisorialSheaf.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op
          he₂.invSection =
        H.divisorialSheaf.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op he₁.invSection →
      V.presheaf.map (homOfLE (ιV.preimage_mono (inf_le_left : U₁ ⊓ U₂ ≤ U₁))).op
          (G U₁ e₁ he₁) * ιV.app (U₁ ⊓ U₂) (d ^ r) =
        V.presheaf.map (homOfLE (ιV.preimage_mono (inf_le_right : U₁ ⊓ U₂ ≤ U₂))).op
          (G U₂ e₂ he₂)) :
    ∃ σ : Γ((Scheme.Modules.pullback ιV ⋙ Scheme.Modules.pushforward ιV).obj
        ((a * r) • H).divisorialSheaf, ⊤), ∀ (U : R.Opens) (e : (RationalFunctions R)ˣ)
        (he : H.IsLocalEquation U e),
      ((Scheme.Modules.pullback ιV ⋙ Scheme.Modules.pushforward ιV).obj
          ((a * r) • H).divisorialSheaf).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op σ =
        (show Γ((Scheme.Modules.pullback ιV).obj ((a * r) • H).divisorialSheaf, ιV ⁻¹ᵁ U) from
          (G U e he ^ a) • (show Γ((Scheme.Modules.pullback ιV).obj ((a * r) • H).divisorialSheaf,
              ιV ⁻¹ᵁ U) from
            ((Scheme.Modules.pullbackPushforwardAdjunction ιV).unit.app
              ((a * r) • H).divisorialSheaf).app U (isLocalEquation_pow he (a * r)).invSection)) := by
  set D := ((a * r) • H).divisorialSheaf with hD
  set E := (Scheme.Modules.pullback ιV ⋙ Scheme.Modules.pushforward ιV).obj D with hE
  set η := (Scheme.Modules.pullbackPushforwardAdjunction ιV).unit.app D with hη
  let ι := Σ U : R.Opens, {e : (RationalFunctions R)ˣ // H.IsLocalEquation U e}
  let Uc : ι → R.Opens := fun c => c.1
  let sc : ∀ c : ι, Γ(E, Uc c) := fun c =>
    (show Γ((Scheme.Modules.pullback ιV).obj D, ιV ⁻¹ᵁ c.1) from
      (G c.1 c.2.1 c.2.2 ^ a) • (show Γ((Scheme.Modules.pullback ιV).obj D, ιV ⁻¹ᵁ c.1) from
        η.app c.1 (isLocalEquation_pow c.2.2 (a * r)).invSection))
  have hnatη : ∀ {V₁ V₂ : R.Opens} (i : V₁ ⟶ V₂) (x : Γ(D, V₂)),
      η.app V₁ (D.presheaf.map i.op x) = E.presheaf.map i.op (η.app V₂ x) := fun i x =>
    congrArg (fun F => F x) (η.mapPresheaf.naturality i.op)
  have hcompat : TopCat.Presheaf.IsCompatible E.presheaf Uc sc := by
    rintro ⟨U₁, e₁, he₁⟩ ⟨U₂, e₂, he₂⟩
    -- the transition function between the two local equations
    obtain ⟨d, hd⟩ := (he₂.isLocalGenerator_invSection (U₁ ⊓ U₂) inf_le_right).2
      (H.divisorialSheaf.presheaf.map (homOfLE inf_le_left).op he₁.invSection)
    have hdpow : D.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op
        (isLocalEquation_pow he₁ (a * r)).invSection = d ^ (a * r) •
        D.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op
          (isLocalEquation_pow he₂ (a * r)).invSection := by
      refine Subtype.ext (funext fun Z => ?_)
      have hZ := congrFun (congrArg Subtype.val hd) Z
      change R.presheaf.germ (U₁ ⊓ U₂) (componentGenericPoint R Z.1) Z.2 d *
          (((e₂⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R) Z.1) =
        (((e₁⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R) Z.1) at hZ
      change (((e₁ ^ (a * r))⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R) Z.1 =
        R.presheaf.germ (U₁ ⊓ U₂) (componentGenericPoint R Z.1) Z.2 (d ^ (a * r)) *
          (((e₂ ^ (a * r))⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R) Z.1
      rw [← inv_pow, ← inv_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        Pi.pow_apply, Pi.pow_apply, map_pow, ← hZ, mul_pow]
    have hG12 : (V.presheaf.map (homOfLE (ιV.preimage_mono (inf_le_left : U₁ ⊓ U₂ ≤ U₁))).op
        (G U₁ e₁ he₁)) ^ a * ιV.app (U₁ ⊓ U₂) (d ^ (a * r)) =
        (V.presheaf.map (homOfLE (ιV.preimage_mono (inf_le_right : U₁ ⊓ U₂ ≤ U₂))).op
          (G U₂ e₂ he₂)) ^ a := by
      have hG12' := hG U₁ U₂ e₁ e₂ he₁ he₂ d hd
      rw [← hG12', mul_pow]
      congr 1
      rw [← map_pow, ← pow_mul, mul_comm r a]
    change ((Scheme.Modules.pullback ιV).obj D).presheaf.map
        (homOfLE (ιV.preimage_mono (inf_le_left : U₁ ⊓ U₂ ≤ U₁))).op
          ((G U₁ e₁ he₁ ^ a) • (show Γ((Scheme.Modules.pullback ιV).obj D, ιV ⁻¹ᵁ U₁) from
            η.app U₁ (isLocalEquation_pow he₁ (a * r)).invSection)) =
      ((Scheme.Modules.pullback ιV).obj D).presheaf.map
        (homOfLE (ιV.preimage_mono (inf_le_right : U₁ ⊓ U₂ ≤ U₂))).op
          ((G U₂ e₂ he₂ ^ a) • (show Γ((Scheme.Modules.pullback ιV).obj D, ιV ⁻¹ᵁ U₂) from
            η.app U₂ (isLocalEquation_pow he₂ (a * r)).invSection))
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, map_pow, map_pow]
    have h1 : ((Scheme.Modules.pullback ιV).obj D).presheaf.map
        (homOfLE (ιV.preimage_mono (inf_le_left : U₁ ⊓ U₂ ≤ U₁))).op
          (η.app U₁ (isLocalEquation_pow he₁ (a * r)).invSection) =
        η.app (U₁ ⊓ U₂) (D.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op
          (isLocalEquation_pow he₁ (a * r)).invSection) :=
      (hnatη (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) _).symm
    have h2 : ((Scheme.Modules.pullback ιV).obj D).presheaf.map
        (homOfLE (ιV.preimage_mono (inf_le_right : U₁ ⊓ U₂ ≤ U₂))).op
          (η.app U₂ (isLocalEquation_pow he₂ (a * r)).invSection) =
        η.app (U₁ ⊓ U₂) (D.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op
          (isLocalEquation_pow he₂ (a * r)).invSection) :=
      (hnatη (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) _).symm
    erw [h1, h2, hdpow, Scheme.Modules.Hom.app_smul]
    have h3 : ∀ y : Γ(E, U₁ ⊓ U₂), d ^ (a * r) • y =
        (show Γ((Scheme.Modules.pullback ιV).obj D, ιV ⁻¹ᵁ (U₁ ⊓ U₂)) from
          ιV.app (U₁ ⊓ U₂) (d ^ (a * r)) •
            (show Γ((Scheme.Modules.pullback ιV).obj D, ιV ⁻¹ᵁ (U₁ ⊓ U₂)) from y)) :=
      fun _ => rfl
    rw [h3]
    exact (smul_smul _ _ _).trans (congrArg (· • _) hG12)
  obtain ⟨σ', hσ', -⟩ := TopCat.Sheaf.existsUnique_gluing
    (⟨E.presheaf, Scheme.Modules.isSheaf E⟩ : TopCat.Sheaf Ab R) Uc sc hcompat
  have hcover : (⊤ : R.Opens) ≤ ⨆ c, Uc c := fun x _ => by
    obtain ⟨U, hx, e, he⟩ := hH x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, e, he⟩, hx⟩
  refine ⟨E.presheaf.map (homOfLE hcover).op σ', fun U e he => ?_⟩
  have h1 := hσ' ⟨U, e, he⟩
  have h2 : E.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (E.presheaf.map (homOfLE hcover).op σ') =
      E.presheaf.map (TopologicalSpace.Opens.leSupr Uc ⟨U, e, he⟩).op σ' := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  exact h2.trans h1

/-- **An admissible floor system is a section of `M|_V`.** An admissible system `t` of sections of
`m(K_{C_P} + B_{C_P})`, `m = kr`, descends to the floor `S` and, through `f_* 𝒪_S = 𝒪_V`, to
`V = f(S)`: for every `a > 0` there is a global section `σ` of `ι_V^* 𝒪_R(arH)` such that, near
the image of the generic point of every floor component `C_P`, `σ = g · e^{-ar}` for a local
equation `e` of `H` and a function `g` on `V` whose value along `C_P` is `γ^a`, where
`t_P = γ · Res_{C_P}(f^*e^{-r} w^{⊗kr})`. -/
private theorem exists_section_of_mem_admissibleSections
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : Mori.IsProjectiveVariety ℂ sX) {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ)) (hQ : IsQFactorial sX)
    {B : QDivisor X} (hB : IsPair sX B) (hdlt : MMP.Intersection.IsDltPair sX B)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    {R : Scheme.{0}} [IsIntegral R] [CompactSpace R] [IsLocallyNoetherian R] [IsNormal R]
    {sR : R ⟶ Spec (.of ℂ)} (hRn : IsNormalVariety ℂ sR) (hRp : Mori.IsProjectiveVariety ℂ sR)
    (f : X ⟶ R) [IsDominant f] (hf : f ≫ sR = sX) (hfp : IsProjectiveMorphism f)
    (hfO : ∀ U : R.Opens, IsIso (f.app U))
    {k : ℕ} (hk : 0 < k) {H : Divisor R} (hH : H.IsCartier)
    {M : Divisor X} {u : X.functionField} (hu0 : u ≠ 0)
    (hMu : ∀ Γ : Mori.PrimeDivisor X,
      (X.ord u Γ.genericPoint : ℚ) = M.coeff Γ - k * (K.coeff Γ + B.coeff Γ))
    (hM : ∃ hfH, H.IsPullback f hfH M)
    (hS0 : B.roundDown ≠ 0)
    {S : Scheme.{0}} (ιS : S ⟶ X) [IsClosedImmersion ιS] [IsReduced S]
    (hS : Set.range ιS.base = ⋃ E ∈ B.roundDown.support, (E.support : Set X))
    {V : Scheme.{0}} (ιV : V ⟶ R) [IsClosedImmersion ιV] [IsReduced V]
    (hV : Set.range ιV.base = f.base '' Set.range ιS.base)
    (fS : S ⟶ V) (hfS : fS ≫ ιV = ιS ≫ f) (hfSO : ∀ U : V.Opens, IsIso (fS.app U))
    (C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0})
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    (j : ∀ P, C P ⟶ X) (BC : ∀ P, QDivisor (C P))
    (hC : ∀ P, IsAdjunctionStep sX B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X))
    {r : ℕ} (hm : Even (k * r))
    (hCartKB : (((k * r : ℕ) : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    (RS : ResidueRestriction (fun P => j P ≫ sX) BC n (k * r))
    (w : letI := functionFieldAlgebra sX; ⋀[X.functionField]^(n + 1) Ω[X.functionField⁄ℂ])
    (hw : ∀ N : ℕ, 0 < N → formPowR sX w N ≠ 0 ∧
      ∀ Γ : Mori.PrimeDivisor X, Γ.ordForm (formPowR sX w N) = N * K.coeff Γ)
    (gV : ∀ P, C P ⟶ V) (hgV : ∀ P, gV P ≫ ιV = j P ≫ f)
    {t : ∀ P, logPluricanonicalSections (j P ≫ sX) n (k * r) (BC P)}
    (ht : t ∈ admissibleSections RS) {a : ℕ} (ha : 0 < a) :
    ∃ σ : Γ((Scheme.Modules.pullback ιV ⋙ Scheme.Modules.pushforward ιV).obj
        ((a * r) • H).divisorialSheaf, ⊤),
      ∀ (U : R.Opens) (e : (RationalFunctions R)ˣ) (he : H.IsLocalEquation U e) (P)
        (hP : f (j P (genericPoint (C P))) ∈ U),
        ∃ (ω₁ : letI := functionFieldAlgebra (j P ≫ sX);
            ⋀[(C P).functionField]^n Ω[(C P).functionField⁄ℂ])
          (c₁ γ : (C P).functionField) (g : Γ(V, ιV ⁻¹ᵁ U))
          (hPV : gV P (genericPoint (C P)) ∈ ιV ⁻¹ᵁ U),
          IsPoincareResidue sX (j P) n (k * r)
            (((functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
              (e : RationalFunctions R)))⁻¹ * u) ^ r • formPowR sX w (k * r))
            (c₁ • formPowR (j P ≫ sX) ω₁ (k * r)) ∧
          ((t P : logPluricanonicalSections (j P ≫ sX) n (k * r) (BC P)) :
              RationalPluriForms (j P ≫ sX) n ((k * r : ℕ) : ℤ)) =
            γ • (c₁ • formPowR (j P ≫ sX) ω₁ (k * r)) ∧
          ((Scheme.Modules.pullback ιV ⋙ Scheme.Modules.pushforward ιV).obj
              ((a * r) • H).divisorialSheaf).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op σ =
            (show Γ((Scheme.Modules.pullback ιV).obj ((a * r) • H).divisorialSheaf, ιV ⁻¹ᵁ U) from
              g • (show Γ((Scheme.Modules.pullback ιV).obj ((a * r) • H).divisorialSheaf,
                  ιV ⁻¹ᵁ U) from
                ((Scheme.Modules.pullbackPushforwardAdjunction ιV).unit.app
                  ((a * r) • H).divisorialSheaf).app U
                  (isLocalEquation_pow he (a * r)).invSection)) ∧
          ((gV P).stalkMap (genericPoint (C P))).hom (V.presheaf.germ (ιV ⁻¹ᵁ U) _ hPV g) =
            γ ^ a ∧
          ∀ y : C P, (∃ W : (C P).Opens, y ∈ W ∧ GeneratesOn (BC P) (k * r) W
              ((t P : logPluricanonicalSections (j P ≫ sX) n (k * r) (BC P)) :
                RationalPluriForms (j P ≫ sX) n ((k * r : ℕ) : ℤ))) →
            ∀ hy : gV P y ∈ ιV ⁻¹ᵁ U, IsUnit (V.presheaf.germ (ιV ⁻¹ᵁ U) (gV P y) hy g) := by
  classical
  -- the base forms `f^*e^{-r} w^{⊗kr}` near the floor
  let τ : R.Opens → (RationalFunctions R)ˣ → RationalPluriForms sX (n + 1) ((k * r : ℕ) : ℤ) :=
    fun _ e => ((functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
      (e : RationalFunctions R)))⁻¹ * u) ^ r • formPowR sX w (k * r)
  -- their residues along the floor components
  have hρex : ∀ (U : R.Opens) (e : (RationalFunctions R)ˣ), H.IsLocalEquation U e →
      ∀ P, f (j P (genericPoint (C P))) ∈ U →
        ∃ ρ : RationalPluriForms (j P ≫ sX) n ((k * r : ℕ) : ℤ),
          IsPoincareResidue sX (j P) n (k * r) (τ U e) ρ ∧ ρ ≠ 0 := by
    intro U e he P hP
    haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
    have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
    haveI : CompactSpace (C P) := by
      haveI := (RS.setting.isProjectiveVariety P).toIsVariety
      exact QuasiCompact.compactSpace_of_compactSpace (j P ≫ sX)
    obtain ⟨hfH, hpb⟩ := hM
    exact exists_isPoincareResidue_ne_zero_of_generatesOn hXn hdim hdlt.2.1 (hC P).1
      (RS.setting.topologicalKrullDim_eq P)
      (generatesOn_base hdim f hpb hu0 hMu w hw RS.setting.pos he) hP
  -- the floor as an sdlt adjoint pair, its components indexed by the floor primes
  obtain ⟨-, hfin, N, Δ, Θ, hsdlt, hadj, hbij, hres⟩ :=
    isCMScheme_and_exists_isSdltAdjointPair_of_isDltPair (k := ℂ) hdim hK hX hQ hB hdlt hS0 ιS hS
  obtain ⟨π, hπ⟩ := exists_equiv_iso_floorComponents ιS N hadj hbij C j BC hC
  choose hπr pp hpp using hπ
  haveI : ∀ i, IsDominant (pp i).hom := fun i => inferInstance
  have hproj : ∀ i, IsProjectiveMorphism (pp i).hom := by
    intro i
    obtain ⟨d, j0, hj0, h0⟩ := AlgebraicGeometry.isProjectiveMorphism_id (N.X i)
    haveI := hj0
    exact ⟨d, (pp i).hom ≫ j0, inferInstance, by rw [Category.assoc, h0, Category.comp_id]⟩
  have hfam : (fun i => (pp i).hom ≫ N.n i ≫ ιS ≫ sX) = (fun i => j (π i) ≫ sX) :=
    funext fun i => by rw [← hpp i]; simp only [Category.assoc]
  obtain ⟨R', s', hs', hss'⟩ := exists_residueRestriction_congr hfam
    (residueRestrictionReindex RS π) (fun i => t (π i)) (mem_admissibleSections_reindex RS π ht)
  have hcoefAll : ∀ i (F : Mori.PrimeDivisor (C (π i))) (F' : Mori.PrimeDivisor (N.X i)),
      F'.genericPoint = (pp i).hom F.genericPoint → (BC (π i)).coeff F = (Θ i).coeff F' := by
    intro i F F' hF'
    haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
    have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
    obtain ⟨K', hdltK⟩ := hsdlt.exists_isDltPair i
    have hPW := hdltK.1
    haveI : IsProper sX := (IsProjectiveMorphism.isProjective
      (IsProjectiveVariety.isProjective (k := ℂ) (f := sX))).isProper
    obtain ⟨-, d, K₀, hK₀, hKB⟩ := hB.isPair
    have hd : d = n + 1 := by
      have := hK₀.topologicalKrullDim_eq
      rw [hdim] at this
      exact_mod_cast this.symm
    subst hd
    have hσ0 : ∀ a, (1 : FunctionFieldEquiv sX sX) a = functionFieldMap (Iso.refl X).hom a :=
      fun a => (functionFieldMap_id_apply a).symm
    have hσc0 : IsCrepantBirationalMap sX sX B B 1 :=
      (crepantBirationalAutomorphisms sX B).one_mem
    have hψX : (pp i).hom ≫ (N.n i ≫ ιS) = j (π i) ≫ (Iso.refl X).hom := by
      rw [hpp i]; rfl
    have hsT : (pp i).hom ≫ (N.n i ≫ ιS) ≫ sX = j (π i) ≫ sX := by
      rw [← Category.assoc, hpp i]
    obtain ⟨σT, hσT⟩ := exists_functionFieldEquiv_of_comp_eq (k := ℂ) (pp i).hom
      (functionFieldMap_bijective_of_isIso (pp i)) hsT
    haveI : CompactSpace (C (π i)) := by
      haveI := (RS.setting.isProjectiveVariety (π i)).toIsVariety
      exact QuasiCompact.compactSpace_of_compactSpace (j (π i) ≫ sX)
    haveI : CompactSpace (N.X i) := (Scheme.homeoOfIso (pp i)).compactSpace
    haveI : IsNoetherian (C (π i)) := {}
    have hcr := isCrepantBirationalMap_of_isAdjunctionStep_of_iso hXn hXn hdim hdim hK₀ hK₀ hKB
      hKB (Iso.refl X) (Category.id_comp sX) 1 hσ0 hσc0 (hC (π i)).1 (hadj i) (pp i) hψX σT hσT
    have hPC : MMP.Mori.IsPair (j (π i) ≫ sX) (BC (π i)) := (RS.setting.isPair (π i)).isPair
    obtain ⟨-, dC, KC, hKC, -⟩ := id hPC
    have hPN : MMP.Mori.IsPair ((N.n i ≫ ιS) ≫ sX) (Θ i) := by
      rw [Category.assoc]; exact hPW.isPair
    have hK'N : K'.IsCanonicalDivisor ((N.n i ≫ ιS) ≫ sX) n := by
      rw [Category.assoc]; exact hPW.2.1
    have hinvj : (pp i).inv ≫ j (π i) = N.n i ≫ ιS := by
      rw [← hpp i, Iso.inv_hom_id_assoc]
    have hZn : IsNormalVariety ℂ ((pp i).inv ≫ j (π i) ≫ sX) := by
      rw [← Category.assoc, hinvj, Category.assoc]; exact N.isNormalVariety i
    have hval : ∀ g, F'.divisorialValuation g = F.divisorialValuation ((σT.toHom) g) := by
      intro g
      change F'.divisorialValuation g = F.divisorialValuation (σT g)
      rw [hσT]
      exact divisorialValuation_eq_of_iso (hC (π i)).1.1 (pp i) hZn F F' hF'.symm g
    exact (coeff_eq_of_isCrepantBirationalMap hPC hPN hKC hK'N σT hcr F F' hval).symm
  have hcrep : ∀ i, ∃ (K' : Divisor (N.X i))
      (hY : IsNormalVariety ℂ ((pp i).hom ≫ N.n i ≫ ιS ≫ sX))
      (hp : IsBirationalMorphism (pp i).hom),
      IsCrepantBoundary (N.n i ≫ ιS ≫ sX) n K' (Θ i) (pp i).hom hY hp (BC (π i)) := by
    intro i
    haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
    have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
    obtain ⟨K', hdltK⟩ := hsdlt.exists_isDltPair i
    have hPW := hdltK.1
    have hYeq : (pp i).hom ≫ N.n i ≫ ιS ≫ sX = j (π i) ≫ sX := by
      rw [← hpp i]; simp only [Category.assoc]
    have hY : IsNormalVariety ℂ ((pp i).hom ≫ N.n i ≫ ιS ≫ sX) := hYeq ▸ (hC (π i)).1.1
    have hp : IsBirationalMorphism (pp i).hom := isBirationalMorphism_of_isIso _
    refine ⟨K', hY, hp, fun F => ?_⟩
    -- the image of `F` on `Tᵢ`
    obtain ⟨F', hF'⟩ := exists_primeDivisor_genericPoint_eq_of_iso (pp i) F
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPW.isPair hPW.2.1
      (⟨C (π i), (pp i).hom, hY, hp, F⟩ : DivisorOver ℂ (N.n i ≫ ιS ≫ sX))
    have hc' := isDiscrepancy_eq_neg_coeff_of_map_genericPoint_eq hPW.1 (P := F') hF'.symm hc
    -- the crepancy of `(C_P, B_{C_P}) ≅ (Tᵢ, Θᵢ)`
    have hcoef : (BC (π i)).coeff F = (Θ i).coeff F' := hcoefAll i F F' hF'
    rw [hc', ← hcoef] at hc
    exact hc
  -- the residues of the base forms are local generators on the floor
  have hdimN : ∀ i, topologicalKrullDim (N.X i) = n := fun i =>
    topologicalKrullDim_floorComponent ιS hdim hK hX hQ hB hdlt hS0 hS N Θ hadj hbij i
  have hgenU : ∀ (U : R.Opens) (e : (RationalFunctions R)ˣ), H.IsLocalEquation U e →
      ∃ ρ : ∀ i, RationalPluriForms (N.n i ≫ ιS ≫ sX) n ((k * r : ℕ) : ℤ),
        ((∀ i, ((N.n i ≫ ιS) ⁻¹ᵁ (f ⁻¹ᵁ U) : Set (N.X i)).Nonempty →
          IsPoincareResidue sX (N.n i ≫ ιS) n (k * r) (τ U e) (ρ i)) ∧ ∀ i, ρ i ≠ 0) ∧
        IsAdjointGeneratorOn N n (k * r) Θ (ιS ⁻¹ᵁ (f ⁻¹ᵁ U)) ρ ∧
        ∀ U' : S.Opens, U' ≤ ιS ⁻¹ᵁ (f ⁻¹ᵁ U) →
          ∀ g : ∀ i, RationalPluriForms (N.n i ≫ ιS ≫ sX) n ((k * r : ℕ) : ℤ),
            IsAdjointGeneratorOn N n (k * r) Θ U' g →
            ∃ ε : Γ(S, U')ˣ, ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U')),
              g i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom
                ((N.n i).app U' (ε : Γ(S, U'))) • ρ i := by
    intro U e he
    haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
    have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
    obtain ⟨hfH, hpb⟩ := id hM
    have hgenτ := generatesOn_base hdim f hpb hu0 hMu w hw RS.setting.pos he
    have hCart := hCartKB
    obtain ⟨⟨ρ₀, hρ₀⟩, hρall⟩ := hres (k * r) RS.setting.pos hCart (f ⁻¹ᵁ U) (τ U e) hgenτ
    have hcpt : ∀ i, CompactSpace (N.X i) := fun i => by
      haveI : CompactSpace (C (π i)) := by
        haveI := (RS.setting.isProjectiveVariety (π i)).toIsVariety
        exact QuasiCompact.compactSpace_of_compactSpace (j (π i) ≫ sX)
      exact (Scheme.homeoOfIso (pp i)).compactSpace
    have hρ₁ : ∀ i, ∃ ρ₁ : RationalPluriForms (N.n i ≫ ιS ≫ sX) n ((k * r : ℕ) : ℤ),
        (((N.n i ≫ ιS) ⁻¹ᵁ (f ⁻¹ᵁ U) : Set (N.X i)).Nonempty →
          IsPoincareResidue sX (N.n i ≫ ιS) n (k * r) (τ U e) ρ₁) ∧ ρ₁ ≠ 0 := by
      intro i
      haveI := hcpt i
      by_cases hi : ((N.n i ≫ ιS) ⁻¹ᵁ (f ⁻¹ᵁ U) : Set (N.X i)).Nonempty
      · have hgi : (N.n i ≫ ιS) (genericPoint (N.X i)) ∈ f ⁻¹ᵁ U := by
          obtain ⟨z, hz⟩ := hi
          exact ((genericPoint_spec (N.X i)).specializes trivial |>.map
            (N.n i ≫ ιS).continuous).mem_open (f ⁻¹ᵁ U).isOpen hz
        obtain ⟨ρ', hρ', hρ'0⟩ := exists_isPoincareResidue_ne_zero_of_generatesOn hXn hdim
          hdlt.2.1 (hadj i) (hdimN i) hgenτ hgi
        exact ⟨ρ', fun _ => hρ', hρ'0⟩
      · haveI : LocallyOfFiniteType (N.n i ≫ ιS ≫ sX) := (N.isNormalVariety i).1.toLocallyOfFiniteType
        letI := functionFieldAlgebra (N.n i ≫ ιS ≫ sX)
        obtain ⟨b⟩ := exists_basis_topForms (sX := N.n i ≫ ιS ≫ sX) (d := n) (by rw [hdimN i])
        refine ⟨(ZTensorPower.basis b ((k * r : ℕ) : ℤ)) (), fun h => absurd h hi, ?_⟩
        exact (ZTensorPower.basis b _).ne_zero ()
    choose ρ hρres hρne using hρ₁
    obtain ⟨hgen, huniq⟩ := hρall ρ hρres hρne
    exact ⟨ρ, ⟨hρres, hρne⟩, hgen, huniq⟩
  have hm' : ∀ x : S, ∃ (U : S.Opens) (_ : x ∈ U)
      (g : ∀ i, RationalPluriForms (N.n i ≫ ιS ≫ sX) n ((k * r : ℕ) : ℤ)),
      IsAdjointGeneratorOn N n (k * r) Θ U g ∧
        ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
          (N.n i).base P.genericPoint ∈ (MMP.Flips.doubleIntersectionLocus S : Set S) →
          ∃ (V : S.Opens) (hP : (N.n i).base P.genericPoint ∈ V) (a : Fin (n - 1) → Γ(S, V))
            (g' : Γ(S, V)), IsLogResiduePresentation N n (k * r) i P V hP a g' 1 (g i) := by
    intro x
    obtain ⟨U, hU, e, he⟩ := hH (f (ιS x))
    obtain ⟨ρ, ⟨hρres, hρne⟩, hgen, -⟩ := hgenU U e he
    refine ⟨ιS ⁻¹ᵁ (f ⁻¹ᵁ U), hU, ρ, hgen, fun i P hPU hPD => ?_⟩
    obtain ⟨j', P', heq, hne⟩ := exists_other_branch ιS hdim hK hX hQ hB hdlt hS0 hS N Θ hadj
      hbij i P hPD
    obtain ⟨V', hP, -, a', g', h1, -⟩ := hgen.2 i j' P P' heq hPU hPD hne
    exact ⟨V', hP, a', g', h1⟩
  obtain ⟨t', ⟨htloc, htpull⟩, -⟩ :=
    ((IsSdltAdjointPair.existsUnique_pullback_eq_of_mem_preadmissibleSections hsdlt
      (fun i => (pp i).hom) hproj hcrep R' hm').1 s'
      (admissibleSections_le_preadmissibleSections R' hs')).1
  -- the descended functions on `V`
  have hdescG : ∀ (U : R.Opens) (e : (RationalFunctions R)ˣ), H.IsLocalEquation U e →
      ∃ G : Γ(V, ιV ⁻¹ᵁ U), ∀ P, ∀ hPV : gV P (genericPoint (C P)) ∈ ιV ⁻¹ᵁ U,
        ∀ ρ : RationalPluriForms (j P ≫ sX) n ((k * r : ℕ) : ℤ),
          IsPoincareResidue sX (j P) n (k * r) (τ U e) ρ →
          ((t P : logPluricanonicalSections (j P ≫ sX) n (k * r) (BC P)) :
              RationalPluriForms (j P ≫ sX) n ((k * r : ℕ) : ℤ)) =
            ((gV P).stalkMap (genericPoint (C P))).hom
              (V.presheaf.germ (ιV ⁻¹ᵁ U) _ hPV G) • ρ ∧
          ∀ y : C P, (∃ W : (C P).Opens, y ∈ W ∧ GeneratesOn (BC P) (k * r) W
              ((t P : logPluricanonicalSections (j P ≫ sX) n (k * r) (BC P)) :
                RationalPluriForms (j P ≫ sX) n ((k * r : ℕ) : ℤ))) →
            ∀ hy : gV P y ∈ ιV ⁻¹ᵁ U, IsUnit (V.presheaf.germ (ιV ⁻¹ᵁ U) (gV P y) hy G) := by
    intro U e he
    obtain ⟨ρN, ⟨hρNres, hρN0⟩, hgenρ, huniqρ⟩ := hgenU U e he
    set W : S.Opens := fS ⁻¹ᵁ (ιV ⁻¹ᵁ U) with hWdef
    have hWfS : ιS ⁻¹ᵁ (f ⁻¹ᵁ U) = W := by
      rw [hWdef, ← Scheme.Hom.comp_preimage, ← hfS, Scheme.Hom.comp_preimage]
    have hlftN : ∀ i, LocallyOfFiniteType (N.n i ≫ ιS ≫ sX) := fun i =>
      (N.isNormalVariety i).1.toLocallyOfFiniteType
    -- the coefficients of `t'` against the residue generators
    have hcoef : ∀ i, ∃ c : (N.X i).functionField, t' i = c • ρN i := fun i => by
      haveI := hlftN i
      exact exists_eq_smul_of_ne_zero (hdimN i) (hρN0 i) (t' i)
    choose φ hφ using hcoef
    -- they descend locally
    have hloc : ∀ x : W, ∃ V' : S.Opens, x.1 ∈ V' ∧ V' ≤ W ∧ DescendsOn N φ V' := by
      intro x
      obtain ⟨U', hxU', g, f', ⟨hg, -⟩, htf⟩ := htloc x.1
      have hgV : IsAdjointGeneratorOn N n (k * r) Θ (U' ⊓ W) g :=
        ⟨fun i => (hg.1 i).mono ((N.n i).preimage_mono inf_le_left),
          fun i j P P' h1 h2 h3 h4 => hg.2 i j P P' h1 h2.1 h3 h4⟩
      obtain ⟨ε, hε⟩ := huniqρ (U' ⊓ W) (inf_le_right.trans hWfS.ge) g hgV
      refine ⟨U' ⊓ W, ⟨hxU', x.2⟩, inf_le_right, (f' |_ (U' ⊓ W)) * (ε : Γ(S, U' ⊓ W)),
        fun i hi => ?_⟩
      haveI : Nonempty (N.n i ⁻¹ᵁ U') := ⟨⟨hi.some.1, hi.some.2.1⟩⟩
      have e1 := htf i inferInstance
      rw [hε i hi, ← germToFunctionField_app_res N i (inf_le_left : U' ⊓ W ≤ U') f', hφ i,
        smul_smul] at e1
      rw [smul_left_injective _ (hρN0 i) e1, map_mul, map_mul]
    choose Vx hxVx hVxW hVxD using hloc
    have hWeq : W = ⨆ x : W, Vx x := le_antisymm
      (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxVx ⟨x, hx⟩⟩)
      (iSup_le hVxW)
    obtain ⟨Fs, hFs⟩ : DescendsOn N φ W := by
      rw [hWeq]; exact descendsOn_iSup Vx hVxD
    -- push down to `V` through `fS_* 𝒪_S = 𝒪_V`
    haveI := hfSO (ιV ⁻¹ᵁ U)
    set G : Γ(V, ιV ⁻¹ᵁ U) := (inv (fS.app (ιV ⁻¹ᵁ U))).hom Fs with hGdef
    have hGFs : fS.app (ιV ⁻¹ᵁ U) G = Fs := by
      rw [hGdef, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id]
      rfl
    refine ⟨G, fun P hPV ρ hρ => ?_⟩
    obtain ⟨i, rfl⟩ := π.surjective P
    haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
    have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
    haveI := hlftN i
    have hpt : ∀ x, ιS (N.n i ((pp i).hom x)) = j (π i) x := fun x => by
      rw [← hpp i]; rfl
    -- the map `C_P ⟶ V` factors through `Tᵢ` and `S`
    have hgVeq : gV (π i) = (pp i).hom ≫ N.n i ≫ fS := by
      rw [← cancel_mono ιV, hgV, Category.assoc, Category.assoc, hfS, ← hpp i]
      simp only [Category.assoc]
    have hgen0 : N.n i ((pp i).hom (genericPoint (C (π i)))) ∈ W := by
      have h1 : ιV (gV (π i) (genericPoint (C (π i)))) ∈ U := hPV
      rw [hgVeq] at h1
      exact h1
    haveI hiW : Nonempty (N.n i ⁻¹ᵁ W) := ⟨⟨_, hgen0⟩⟩
    have hiWne : ((N.n i ≫ ιS) ⁻¹ᵁ (f ⁻¹ᵁ U) : Set (N.X i)).Nonempty := by
      refine ⟨(pp i).hom (genericPoint (C (π i))), ?_⟩
      have : N.n i ((pp i).hom (genericPoint (C (π i)))) ∈ ιS ⁻¹ᵁ (f ⁻¹ᵁ U) := hWfS ▸ hgen0
      exact this
    -- the residue `ρ` is the pull-back of `ρN i`
    have hsT : (pp i).hom ≫ (N.n i ≫ ιS) ≫ sX = j (π i) ≫ sX := by
      rw [← Category.assoc, hpp i]
    obtain ⟨σT, hσT⟩ := exists_functionFieldEquiv_of_comp_eq (k := ℂ) (pp i).hom
      (functionFieldMap_bijective_of_isIso (pp i)) hsT
    have hσ0 : ∀ a, (1 : FunctionFieldEquiv sX sX) a = functionFieldMap (Iso.refl X).hom a :=
      fun a => (functionFieldMap_id_apply a).symm
    have hψX : (pp i).hom ≫ (N.n i ≫ ιS) = j (π i) ≫ (Iso.refl X).hom := by
      rw [hpp i]; rfl
    obtain ⟨-, Q, -, hQr, hciQ, -⟩ := (hC (π i)).1
    obtain ⟨-, Q', -, hQ'r, hciQ', -⟩ := hadj i
    haveI := hciQ
    haveI := hciQ'
    haveI : LocallyOfFiniteType (j (π i) ≫ sX) := (hC (π i)).1.1.1.toLocallyOfFiniteType
    have hclean := isPoincareResidue_pluriformPullback_of_iso hXn hXn hdim hdim (Iso.refl X)
      (Category.id_comp sX) 1 hσ0 Q Q' hQr hQ'r (pp i) hψX σT hσT (hρNres i hiWne)
    rw [pluriformPullback_one (by exact_mod_cast hdim)] at hclean
    have hρeq := IsPoincareResidue.unique (hC (π i)).1 hρ hclean
    obtain ⟨σ₀, hσ₀⟩ := exists_functionFieldEquiv_of_comp_eq (k := ℂ) (pp i).hom
      (functionFieldMap_bijective_of_isIso (pp i))
      (rfl : (pp i).hom ≫ (N.n i ≫ ιS ≫ sX) = (pp i).hom ≫ N.n i ≫ ιS ≫ sX)
    have hheq : HEq (pullbackRationalPluriForms (N.n i ≫ ιS ≫ sX) (pp i).hom (ρN i)) ρ := by
      rw [pullbackRationalPluriForms_eq_pluriformPullback (pp i).hom σ₀ hσ₀ (ρN i), hρeq]
      exact pluriformPullback_heq (congrFun hfam i) (Category.assoc _ _ _).symm σ₀ σT
        (fun a => by
          change σT a = σ₀ a
          rw [hσT, hσ₀]) HEq.rfl
    have hs'eq : ((s' i : logPluricanonicalSections _ n (k * r) _) :
        RationalPluriForms ((pp i).hom ≫ N.n i ≫ ιS ≫ sX) n ((k * r : ℕ) : ℤ)) =
        functionFieldMap (pp i).hom (φ i) •
          pullbackRationalPluriForms (N.n i ≫ ιS ≫ sX) (pp i).hom (ρN i) := by
      rw [← htpull i, hφ i, pullbackRationalPluriForms_smul']
    haveI : Nonempty ((pp i).hom ⁻¹ᵁ (N.n i ⁻¹ᵁ W)) := ⟨⟨genericPoint (C (π i)), hgen0⟩⟩
    -- the value of `G` at the generic point of `C_P`
    have hval : ((gV (π i)).stalkMap (genericPoint (C (π i)))).hom
        (V.presheaf.germ (ιV ⁻¹ᵁ U) _ hPV G) = functionFieldMap (pp i).hom (φ i) := by
      have hx' : ((pp i).hom ≫ N.n i ≫ fS) (genericPoint (C (π i))) ∈ ιV ⁻¹ᵁ U := by
        rwa [← hgVeq]
      rw [stalkMap_germ_eq_of_eq hgVeq (ιV ⁻¹ᵁ U) _ hPV hx', Scheme.Hom.germ_stalkMap_apply,
        hFs i hiW, MMP.Spreading.functionFieldMap_germToFunctionField (pp i).hom (N.n i ⁻¹ᵁ W)
          _ le_rfl, Scheme.Hom.appLE_eq_app]
      change _ = (C (π i)).presheaf.germ _ _ _ _
      rw [← hGFs]
      rfl
    have ht1 : ((t (π i) : logPluricanonicalSections (j (π i) ≫ sX) n (k * r) (BC (π i))) :
        RationalPluriForms (j (π i) ≫ sX) n ((k * r : ℕ) : ℤ)) =
        functionFieldMap (pp i).hom (φ i) • ρ :=
      eq_smul_of_heq (congrFun hfam i).symm (hss' i).symm hheq.symm _ hs'eq
    refine ⟨by rwa [hval], ?_⟩
    rintro y ⟨Wy, hyW, hgenW⟩ hy
    haveI : CompactSpace (C (π i)) := by
      haveI := (RS.setting.isProjectiveVariety (π i)).toIsVariety
      exact QuasiCompact.compactSpace_of_compactSpace (j (π i) ≫ sX)
    have hdimC : topologicalKrullDim (C (π i)) = n := RS.setting.topologicalKrullDim_eq (π i)
    have hY : IsNormalVariety ℂ ((pp i).hom ≫ N.n i ≫ ιS ≫ sX) := by
      rw [congrFun hfam i]; exact (hC (π i)).1.1
    have ht0 : ((t (π i) : logPluricanonicalSections (j (π i) ≫ sX) n (k * r) (BC (π i))) :
        RationalPluriForms (j (π i) ≫ sX) n ((k * r : ℕ) : ℤ)) ≠ 0 := hgenW.1
    have hρ0 : ρ ≠ 0 := by
      rintro rfl; rw [smul_zero] at ht1; exact ht0 ht1
    have hc0 : functionFieldMap (pp i).hom (φ i) ≠ 0 := by
      rintro h0; rw [h0, zero_smul] at ht1; exact ht0 ht1
    -- the coefficient has no zero or pole along the prime divisors through `y`
    have hord : ∀ Γ : Mori.PrimeDivisor (C (π i)), y ∈ Γ.support →
        (C (π i)).ord (functionFieldMap (pp i).hom (φ i)) Γ.genericPoint = 0 := by
      intro Γ hΓ
      obtain ⟨Γ', hΓ'⟩ := exists_primeDivisor_genericPoint_eq_of_iso (pp i) Γ
      have hgΓ : Γ.genericPoint ∈ (gV (π i)) ⁻¹ᵁ (ιV ⁻¹ᵁ U) :=
        Mori.PrimeDivisor.genericPoint_mem_of_nonempty (E := Γ) ⟨y, hΓ, hy⟩
      have hΓ'W : (Γ'.support ∩ ((N.n i) ⁻¹ᵁ (ιS ⁻¹ᵁ (f ⁻¹ᵁ U)) : Set (N.X i))).Nonempty := by
        refine ⟨Γ'.genericPoint, ?_, ?_⟩
        · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
        · rw [hΓ', hWfS]
          have h1 : ιV (gV (π i) Γ.genericPoint) ∈ U := hgΓ
          rw [hgVeq] at h1
          exact h1
      have e1 := (hgenρ.1 i).2 Γ' hΓ'W
      have e2 := hgenW.2 Γ ⟨y, hΓ, hyW⟩
      have e3 : Γ.ordForm ρ = Γ'.ordForm (ρN i) := by
        rw [← ordForm_pullback_eq_of_iso (N.isNormalVariety i) (hdimN i) (pp i) hY Γ Γ' hΓ' (ρN i)]
        exact ordForm_congr_heq (congrFun hfam i).symm hheq.symm Γ
      have e4 := hcoefAll i Γ Γ' hΓ'
      rw [ht1, Γ.ordForm_smul_of_topologicalKrullDim_eq hdimC hc0 hρ0, e3, e4] at e2
      push_cast at e1 e2
      have : ((C (π i)).ord (functionFieldMap (pp i).hom (φ i)) Γ.genericPoint : ℚ) = 0 := by
        linarith
      exact_mod_cast this
    obtain ⟨u, hu, hue⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero y hc0
      hord
    have hst := Scheme.Hom.germ_stalkMap_apply (gV (π i)) (ιV ⁻¹ᵁ U) y hy G
    have hgen1 := Scheme.Hom.germ_stalkMap_apply (gV (π i)) (ιV ⁻¹ᵁ U) _ hPV G
    haveI : Nonempty ((gV (π i)) ⁻¹ᵁ (ιV ⁻¹ᵁ U)) := ⟨⟨y, hy⟩⟩
    have e5 := Scheme.algebraMap_germ_eq_germToFunctionField (X := C (π i))
      (U := (gV (π i)) ⁻¹ᵁ (ιV ⁻¹ᵁ U)) hy ((gV (π i)).app (ιV ⁻¹ᵁ U) G)
    have e6 : ((C (π i)).germToFunctionField ((gV (π i)) ⁻¹ᵁ (ιV ⁻¹ᵁ U))).hom
        ((gV (π i)).app (ιV ⁻¹ᵁ U) G) = functionFieldMap (pp i).hom (φ i) := by
      rw [← hval, hgen1]
    have hgerm : (C (π i)).presheaf.germ ((gV (π i)) ⁻¹ᵁ (ιV ⁻¹ᵁ U)) y hy
        ((gV (π i)).app (ιV ⁻¹ᵁ U) G) = u := by
      apply IsFractionRing.injective ((C (π i)).presheaf.stalk y) (C (π i)).functionField
      rw [e5, e6, hue]
    rw [hgerm] at hst
    exact isUnit_of_map_unit _ _ (hst ▸ hu)
  choose G hG using hdescG
  -- functions on `V` are detected by their values along the floor components
  have hgVeq : ∀ i, gV (π i) = (pp i).hom ≫ N.n i ≫ fS := fun i => by
    rw [← cancel_mono ιV, hgV, Category.assoc, Category.assoc, hfS, ← hpp i]
    simp only [Category.assoc]
  have hinj : ∀ (U' : R.Opens) (b : Γ(V, ιV ⁻¹ᵁ U')),
      (∀ P (hPV : gV P (genericPoint (C P)) ∈ ιV ⁻¹ᵁ U'),
        ((gV P).stalkMap (genericPoint (C P))).hom (V.presheaf.germ (ιV ⁻¹ᵁ U') _ hPV b) = 0) →
      b = 0 := by
    intro U' b hb
    haveI := hfSO (ιV ⁻¹ᵁ U')
    apply (ConcreteCategory.bijective_of_isIso (fS.app (ιV ⁻¹ᵁ U'))).1
    rw [map_zero]
    refine eq_zero_of_forall_germToFunctionField_eq_zero N _ fun i hi => ?_
    obtain ⟨z, hz⟩ := hi
    have hzz : (pp i).hom ((pp i).inv z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    have hgen0 : N.n i ((pp i).hom (genericPoint (C (π i)))) ∈ fS ⁻¹ᵁ (ιV ⁻¹ᵁ U') := by
      have hsp := ((genericPoint_spec (C (π i))).specializes (trivial : (pp i).inv z ∈ _)).map
        ((pp i).hom ≫ N.n i).continuous
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hzz] at hsp
      exact hsp.mem_open (fS ⁻¹ᵁ (ιV ⁻¹ᵁ U')).isOpen hz
    have hPV : gV (π i) (genericPoint (C (π i))) ∈ ιV ⁻¹ᵁ U' := by
      rwa [hgVeq]
    have h := hb (π i) hPV
    have hx' : ((pp i).hom ≫ N.n i ≫ fS) (genericPoint (C (π i))) ∈ ιV ⁻¹ᵁ U' := hgen0
    rw [stalkMap_germ_eq_of_eq (hgVeq i) (ιV ⁻¹ᵁ U') _ hPV hx',
      Scheme.Hom.germ_stalkMap_apply] at h
    haveI : Nonempty ((pp i).hom ⁻¹ᵁ (N.n i ⁻¹ᵁ (fS ⁻¹ᵁ (ιV ⁻¹ᵁ U')))) := ⟨⟨_, hgen0⟩⟩
    haveI : Nonempty (N.n i ⁻¹ᵁ (fS ⁻¹ᵁ (ιV ⁻¹ᵁ U'))) := ⟨⟨_, hgen0⟩⟩
    apply RingHom.injective (functionFieldMap (pp i).hom)
    rwa [map_zero, MMP.Spreading.functionFieldMap_germToFunctionField (pp i).hom
      (N.n i ⁻¹ᵁ (fS ⁻¹ᵁ (ιV ⁻¹ᵁ U'))) _ le_rfl, Scheme.Hom.appLE_eq_app]
  -- the glued section of `ι_V^* 𝒪_R(arH)`
  have hglue := exists_glued_section ιV hH a r G
    fun U₁ U₂ e₁ e₂ he₁ he₂ d hd => by
          rw [← sub_eq_zero]
          apply hinj (U₁ ⊓ U₂)
          intro P hPV
          rw [map_sub, map_sub, map_mul, map_mul, TopCat.Presheaf.germ_res_apply,
            TopCat.Presheaf.germ_res_apply, sub_eq_zero]
          have hP12 : f (j P (genericPoint (C P))) ∈ U₁ ⊓ U₂ := by
            have h := hPV
            change ιV (gV P (genericPoint (C P))) ∈ U₁ ⊓ U₂ at h
            rwa [← Scheme.Hom.comp_apply, hgV P, Scheme.Hom.comp_apply] at h
          have hPV₁ : gV P (genericPoint (C P)) ∈ ιV ⁻¹ᵁ U₁ := hPV.1
          have hPV₂ : gV P (genericPoint (C P)) ∈ ιV ⁻¹ᵁ U₂ := hPV.2
          obtain ⟨ρ₁, hρ₁, -⟩ := hρex U₁ e₁ he₁ P hP12.1
          obtain ⟨ρ₂, hρ₂, hρ₂0⟩ := hρex U₂ e₂ he₂ P hP12.2
          have ht₁ := (hG U₁ e₁ he₁ P hPV₁ ρ₁ hρ₁).1
          have ht₂ := (hG U₂ e₂ he₂ P hPV₂ ρ₂ hρ₂).1
          haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
          haveI : Nonempty (U₁ ⊓ U₂ : R.Opens) := ⟨⟨_, hP12⟩⟩
          haveI : Nonempty (f ⁻¹ᵁ (U₁ ⊓ U₂)) := ⟨⟨_, hP12⟩⟩
          haveI : Nonempty (j P ⁻¹ᵁ (f ⁻¹ᵁ (U₁ ⊓ U₂))) := ⟨⟨_, hP12⟩⟩
          -- the transition function at the generic point of `R`
          have hZ : componentGenericPoint R (univComponent R) ∈ U₁ ⊓ U₂ :=
            LocalFrame.componentGenericPoint_mem_of_isIntegral (univComponent R) ⟨_, hP12⟩
          have hZ0 := congrFun (congrArg Subtype.val hd) ⟨univComponent R, hZ⟩
          change R.presheaf.germ (U₁ ⊓ U₂) (componentGenericPoint R (univComponent R)) hZ d *
              (((e₂⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R) (univComponent R)) =
            (((e₁⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R) (univComponent R)) at hZ0
          have hkey0 : (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
                (e₁ : RationalFunctions R))⁻¹ =
              R.germToFunctionField (U₁ ⊓ U₂) d *
                (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
                  (e₂ : RationalFunctions R))⁻¹ := by
            have i1 := evalFF_inv_pow e₁ 1
            have i2 := evalFF_inv_pow e₂ 1
            rw [pow_one, pow_one] at i1 i2
            rw [← i1, ← i2]
            change (R.presheaf.stalkSpecializes _).hom
                (((e₁⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R) (univComponent R)) =
              _ * (R.presheaf.stalkSpecializes _).hom
                (((e₂⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R) (univComponent R))
            rw [← hZ0, map_mul]
            congr 1
            exact TopCat.Presheaf.germ_stalkSpecializes_apply R.presheaf hZ _ d
          have hkey : (functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
                (e₁ : RationalFunctions R)))⁻¹ =
              X.germToFunctionField (f ⁻¹ᵁ (U₁ ⊓ U₂)) (f.app (U₁ ⊓ U₂) d) *
                (functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
                  (e₂ : RationalFunctions R)))⁻¹ := by
            rw [← map_inv₀, hkey0, map_mul, map_inv₀,
              MMP.Spreading.functionFieldMap_germToFunctionField f (U₁ ⊓ U₂) (f ⁻¹ᵁ (U₁ ⊓ U₂))
                le_rfl, Scheme.Hom.appLE_eq_app]
          have hτ : τ U₁ e₁ = (X.germToFunctionField (f ⁻¹ᵁ (U₁ ⊓ U₂))).hom
              (f.app (U₁ ⊓ U₂) (d ^ r)) • τ U₂ e₂ := by
            change ((functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
                (e₁ : RationalFunctions R)))⁻¹ * u) ^ r • formPowR sX w (k * r) =
              _ • (((functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
                (e₂ : RationalFunctions R)))⁻¹ * u) ^ r • formPowR sX w (k * r))
            rw [hkey, mul_assoc, mul_pow, mul_smul, map_pow, map_pow]
          have hρ₁₂ := isPoincareResidue_eq_germ_smul (hC P).1 hP12 _ hτ hρ₁ hρ₂
          have hc := stalkMap_germ_app_eq (gV P) ιV (j P) f (hgV P) (U₁ ⊓ U₂)
            (genericPoint (C P)) hPV hP12 (d ^ r)
          rw [hρ₁₂, smul_smul] at ht₁
          have hcc : ((j P).stalkMap (genericPoint (C P))).hom
              (X.presheaf.germ (f ⁻¹ᵁ (U₁ ⊓ U₂)) _ hP12 (f.app (U₁ ⊓ U₂) (d ^ r))) =
              ((C P).germToFunctionField (j P ⁻¹ᵁ (f ⁻¹ᵁ (U₁ ⊓ U₂)))).hom
                ((j P).app _ (f.app (U₁ ⊓ U₂) (d ^ r))) :=
            Scheme.Hom.germ_stalkMap_apply (j P) _ _ _ _
          rw [hc, hcc]
          exact smul_left_injective _ hρ₂0 (ht₁.symm.trans ht₂)
  obtain ⟨σ, hσ⟩ := hglue
  refine ⟨σ, fun U e he P hP => ?_⟩
  have hPV : gV P (genericPoint (C P)) ∈ ιV ⁻¹ᵁ U := by
    show ιV (gV P (genericPoint (C P))) ∈ U
    rw [← Scheme.Hom.comp_apply, hgV P, Scheme.Hom.comp_apply]
    exact hP
  obtain ⟨ρ, hρ, -⟩ := hρex U e he P hP
  obtain ⟨htG, hunit⟩ := hG U e he P hPV ρ hρ
  letI := functionFieldAlgebra (j P ≫ sX)
  haveI : LocallyOfFiniteType (j P ≫ sX) :=
    (RS.setting.isPair P).isPair.isNormalVariety.1.toLocallyOfFiniteType
  obtain ⟨b⟩ := exists_basis_topForms (sX := j P ≫ sX) (d := n)
    (RS.setting.topologicalKrullDim_eq P)
  set c₁ := (ZTensorPower.basis b (k * r)).repr ρ () with hc₁
  have hρeq : ρ = c₁ • formPowR (j P ≫ sX) (b ()) (k * r) :=
    eq_repr_smul_formPow b ρ
  refine ⟨b (), c₁, ((gV P).stalkMap (genericPoint (C P))).hom
    (V.presheaf.germ (ιV ⁻¹ᵁ U) _ hPV (G U e he)), G U e he ^ a, hPV, hρeq ▸ hρ, ?_, hσ U e he,
    by rw [map_pow, map_pow], fun y hy hyV => by rw [map_pow]; exact (hunit y hy hyV).pow a⟩
  rw [htG, hρeq]

/-- **Residues of a pulled-back section, through the floor image.** Let `φ` be a section of
`𝒪_R(arH)` whose restriction to `V` is `g e^{-ar}` near the image of the generic point of an
adjunction step `T ⟶ X` mapping to `V`, and let `c₁ ω^{⊗kr}` be the residue of
`f^*e^{-r} w^{⊗kr}` along `T`. Then the residue of `f^*φ · w^{⊗akr}` along `T` is
`ḡ c₁^a ω^{⊗akr}`, `ḡ` the value of `g` at the generic point of `T`. -/
private theorem isPoincareResidue_pullback_of_unit_app_eq
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    {R : Scheme.{0}} [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R] [CompactSpace R]
    (f : X ⟶ R) [IsDominant f] {H : Divisor R} (hH : H.IsCartier) {B : QDivisor X}
    {T : Scheme.{0}} [IsIntegral T] {jT : T ⟶ X} {BT : QDivisor T}
    (hj : IsAdjunctionStep sX B jT BT)
    {V : Scheme.{0}} (ιV : V ⟶ R) (gT : T ⟶ V) (hgT : gT ≫ ιV = jT ≫ f)
    {U : R.Opens} [Nonempty U] (hU : f (jT (genericPoint T)) ∈ U)
    {e : (RationalFunctions R)ˣ} (he : H.IsLocalEquation U e) {r a k : ℕ} (ha : 0 < a)
    (u : X.functionField)
    (w : letI := functionFieldAlgebra sX; ⋀[X.functionField]^(n + 1) Ω[X.functionField⁄ℂ])
    (φ : Γ(((a * r) • H).divisorialSheaf, ⊤))
    (g : Γ(V, ιV ⁻¹ᵁ U)) (hPV : gT (genericPoint T) ∈ ιV ⁻¹ᵁ U)
    (hσU : ((Scheme.Modules.pullback ιV ⋙ Scheme.Modules.pushforward ιV).obj
        ((a * r) • H).divisorialSheaf).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction ιV).unit.app
          ((a * r) • H).divisorialSheaf).app ⊤ φ) =
      (show Γ((Scheme.Modules.pullback ιV).obj ((a * r) • H).divisorialSheaf, ιV ⁻¹ᵁ U) from
        g • (show Γ((Scheme.Modules.pullback ιV).obj ((a * r) • H).divisorialSheaf,
            ιV ⁻¹ᵁ U) from
          ((Scheme.Modules.pullbackPushforwardAdjunction ιV).unit.app
            ((a * r) • H).divisorialSheaf).app U (isLocalEquation_pow he (a * r)).invSection)))
    (ω : letI := functionFieldAlgebra (jT ≫ sX); ⋀[T.functionField]^n Ω[T.functionField⁄ℂ])
    (c₁ : T.functionField)
    (hρ : IsPoincareResidue sX jT n (k * r)
      (((functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
        (e : RationalFunctions R)))⁻¹ * u) ^ r • formPowR sX w (k * r))
      (c₁ • formPowR (jT ≫ sX) ω (k * r))) :
    IsPoincareResidue sX jT n (a * (k * r))
      ((functionFieldMap f (divisorialSectionValue φ) * u ^ (a * r)) • formPowR sX w (a * (k * r)))
      ((((gT.stalkMap (genericPoint T)).hom (V.presheaf.germ (ιV ⁻¹ᵁ U) _ hPV g)) * c₁ ^ a) •
        formPowR (jT ≫ sX) ω (a * (k * r))) := by
  obtain ⟨h, hhmod, hhval⟩ := exists_divisorialSectionValue_eq he (a * r) φ
  haveI := (hH.nsmul (a * r)).isInvertibleModule_divisorialSheaf
  have hg : g = ιV.app U h := eq_app_of_unit_app_eq ιV _
    (isLocalEquation_pow he (a * r)).isLocalGenerator_invSection φ h hhmod g hσU
  have hval : (jT.stalkMap (genericPoint T)).hom (X.presheaf.germ (f ⁻¹ᵁ U)
      (jT (genericPoint T)) hU (f.appLE U (f ⁻¹ᵁ U) le_rfl h)) =
      (gT.stalkMap (genericPoint T)).hom (V.presheaf.germ (ιV ⁻¹ᵁ U) _ hPV g) := by
    rw [hg, Scheme.Hom.appLE_eq_app]
    exact stalkMap_germ_app_eq jT f gT ιV hgT.symm U _ hU hPV h
  have hres := isPoincareResidue_pullback_smul_formPowR hdim f hj hU ha u w φ h
    (by rw [hhval, evalFF_inv_pow]) ω c₁ hρ
  rw [hval] at hres
  exact hres

/-- **The lifting on `X`.** Equal positive powers of finitely many admissible floor systems lift to
sections of `am(K_X + B)`; when the family generates the floor components, every point of `X` has a
generating section of `am(K_X + B)` that lifts the `a`-th power of a member of the family or of the
zero system. -/
private theorem exists_liftsPow
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : Mori.IsProjectiveVariety ℂ sX) {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ)) (hQ : IsQFactorial sX)
    {B : QDivisor X} (hB : IsPair sX B) (hdlt : MMP.Intersection.IsDltPair sX B)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    {R : Scheme.{0}} [IsIntegral R] [CompactSpace R] [IsLocallyNoetherian R] [IsNormal R]
    {sR : R ⟶ Spec (.of ℂ)} (hRn : IsNormalVariety ℂ sR) (hRp : Mori.IsProjectiveVariety ℂ sR)
    (f : X ⟶ R) (hf : f ≫ sR = sX) (hfp : IsProjectiveMorphism f)
    (hfO : ∀ U : R.Opens, IsIso (f.app U))
    {k : ℕ} (hk : 0 < k) {H : Divisor R} (hH : H.IsCartier)
    {M : Divisor X} {u : X.functionField} (hu0 : u ≠ 0)
    (hMu : ∀ Γ : Mori.PrimeDivisor X,
      (X.ord u Γ.genericPoint : ℚ) = M.coeff Γ - k * (K.coeff Γ + B.coeff Γ))
    (hM : ∃ hfH, H.IsPullback f hfH M)
    (hS0 : B.roundDown ≠ 0)
    {S : Scheme.{0}} (ιS : S ⟶ X) [IsClosedImmersion ιS] [IsReduced S]
    (hS : Set.range ιS.base = ⋃ E ∈ B.roundDown.support, (E.support : Set X))
    {V : Scheme.{0}} (ιV : V ⟶ R) [IsClosedImmersion ιV] [IsReduced V]
    (hV : Set.range ιV.base = f.base '' Set.range ιS.base)
    (fS : S ⟶ V) (hfS : fS ≫ ιV = ιS ≫ f) (hfSO : ∀ U : V.Opens, IsIso (fS.app U))
    (hq₀ : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction ιV).unit.app
        (q • H).divisorialSheaf).app ⊤))
    (hq₁ : ∃ q₁ : ℕ, ∀ q : ℕ, q₁ ≤ q → ∀ y : R, y ∉ Set.range ιV.base →
      ∃ φ : Γ((q • H).divisorialSheaf, ⊤),
        ((Scheme.Modules.pullbackPushforwardAdjunction ιV).unit.app
          (q • H).divisorialSheaf).app ⊤ φ = 0 ∧
        ∃ (U : R.Opens) (_ : Nonempty U) (e : (RationalFunctions R)ˣ) (_ : H.IsLocalEquation U e)
          (h : Γ(R, U)), y ∈ R.basicOpen h ∧
          divisorialSectionValue φ = R.germToFunctionField U h *
            MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
              (((e ^ q)⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R))
    (C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0})
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    (j : ∀ P, C P ⟶ X) (BC : ∀ P, QDivisor (C P))
    (hC : ∀ P, IsAdjunctionStep sX B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X))
    {m : ℕ} (hm : Even m) (hkm : k ∣ m)
    (hCartKB : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    (RS : ResidueRestriction (fun P => j P ≫ sX) BC n m)
    {A : Type} [Finite A] (t : A → ∀ P, logPluricanonicalSections (j P ≫ sX) n m (BC P))
    (ht : ∀ α, t α ∈ admissibleSections RS) :
    ∃ a : ℕ, 0 < a ∧
      (∀ α, ∃ s ∈ logPluricanonicalSections sX (n + 1) (a * m) B,
        LiftsPow sX j BC (t α) a s) ∧
      ((∀ P (y : C P), ∃ α, ∃ W : (C P).Opens, y ∈ W ∧
          GeneratesOn (BC P) m W (t α P : RationalPluriForms (j P ≫ sX) n m)) →
        ∀ x : X, ∃ s ∈ logPluricanonicalSections sX (n + 1) (a * m) B,
          ∃ U : X.Opens, x ∈ U ∧ GeneratesOn B (a * m) U s ∧
            ((∃ α, LiftsPow sX j BC (t α) a s) ∨ LiftsPow sX j BC 0 a s)) := by
  classical
  obtain ⟨r, rfl⟩ := hkm
  haveI : IsDominant f := isDominant_of_forall_isIso_app f hfO
  have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  obtain ⟨w, hw⟩ := exists_formPowR_ordForm_eq hXn hdim hK
  obtain ⟨hfH, hpb⟩ := hM
  have hr : 0 < r := Nat.pos_of_mul_pos_left RS.setting.pos
  -- the maps from the floor components to `V`
  have hcP : ∀ P, ∃ cP : C P ⟶ S, cP ≫ ιS = j P := fun P => by
    obtain ⟨-, -, -, -, hci, -⟩ := id (hC P).1
    haveI := hci
    refine exists_comp_eq_of_range_subset ιS (j P) ?_
    rw [(hC P).2, hS]
    refine Set.subset_biUnion_of_mem (u := fun E : Mori.PrimeDivisor X => (E.support : Set X)) ?_
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    have := P.2
    rwa [← DivisorWithCoeffs.coeff_roundDown] at this
  choose cP hcP using hcP
  set gV : ∀ P, C P ⟶ V := fun P => cP P ≫ fS with hgVdef
  have hgV : ∀ P, gV P ≫ ιV = j P ≫ f := fun P => by
    rw [hgVdef, Category.assoc, hfS, ← Category.assoc, hcP P]
  obtain ⟨q₀, hq₀⟩ := hq₀
  obtain ⟨q₁, hq₁⟩ := hq₁
  set a := q₀ + q₁ + 1 with ha_def
  have ha0 : 0 < a := by omega
  have har₀ : q₀ ≤ a * r := by nlinarith
  have har₁ : q₁ ≤ a * r := by nlinarith
  have hN : 0 < a * (k * r) := by positivity
  -- the zero floor system and the lifts of the members of the family
  have hdesc := fun (t' : ∀ P, logPluricanonicalSections (j P ≫ sX) n (k * r) (BC P))
      (ht' : t' ∈ admissibleSections RS) =>
    exists_section_of_mem_admissibleSections hX hdim hQ hB hdlt hK hRn hRp f hf
      hfp hfO hk hH hu0 hMu ⟨hfH, hpb⟩ hS0 ιS hS ιV hV fS hfS hfSO C j BC hC hm hCartKB RS w hw gV hgV
      ht' ha0
  have key : ∀ t' : ∀ P, logPluricanonicalSections (j P ≫ sX) n (k * r) (BC P),
      t' ∈ admissibleSections RS → ∃ φ : Γ(((a * r) • H).divisorialSheaf, ⊤),
        LiftsPow sX j BC t' a
          ((functionFieldMap f (divisorialSectionValue φ) * u ^ (a * r)) • formPowR sX w (a * (k * r))) ∧
        ∀ P (y : C P), (∃ W : (C P).Opens, y ∈ W ∧ GeneratesOn (BC P) (k * r) W
            ((t' P : logPluricanonicalSections (j P ≫ sX) n (k * r) (BC P)) :
              RationalPluriForms (j P ≫ sX) n ((k * r : ℕ) : ℤ))) →
          ∃ U' : R.Opens, f (j P y) ∈ U' ∧ GeneratesOn B (a * (k * r)) (f ⁻¹ᵁ U')
            ((functionFieldMap f (divisorialSectionValue φ) * u ^ (a * r)) • formPowR sX w (a * (k * r))) := by
    intro t' ht'
    obtain ⟨σ, hσ⟩ := hdesc t' ht'
    obtain ⟨φ, hφ⟩ := hq₀ (a * r) har₀ σ
    refine ⟨φ, ?_, ?_⟩
    · intro P ω c htc
      obtain ⟨U, hU, e, he⟩ := hH (f (j P (genericPoint (C P))))
      haveI : Nonempty U := ⟨⟨_, hU⟩⟩
      obtain ⟨ω₁, c₁, γ, g, hPV, hρ, htγ, hσU, hgval, -⟩ := hσ U e he P hU
      have hres := isPoincareResidue_pullback_of_unit_app_eq hdim f hH (hC P).1 ιV (gV P)
        (hgV P) hU he ha0 u w φ g hPV (by rwa [hφ]) ω₁ c₁ hρ
      rw [hgval] at hres
      letI := functionFieldAlgebra (j P ≫ sX)
      haveI : LocallyOfFiniteType (j P ≫ sX) :=
        (RS.setting.isPair P).isPair.isNormalVariety.1.toLocallyOfFiniteType
      obtain ⟨b⟩ := exists_basis_topForms (sX := j P ≫ sX) (d := n)
        (RS.setting.topologicalKrullDim_eq P)
      have heq : ((γ * c₁) • formPow ω₁ (k * r) : PluriForms ℂ (C P).functionField n (k * r)) =
          c • formPow ω (k * r) := by
        rw [mul_smul]
        exact htγ.symm.trans htc
      have hpw := smul_formPow_pow_eq b heq a
      have hpw' : (c ^ a • formPow ω (a * (k * r)) :
          RationalPluriForms (j P ≫ sX) n ((a * (k * r) : ℕ) : ℤ)) =
          (γ ^ a * c₁ ^ a) • formPowR (j P ≫ sX) ω₁ (a * (k * r)) := by
        rw [← mul_pow]
        exact hpw.symm
      rw [hpw']
      exact hres
    · intro P y hyW
      obtain ⟨U, hU, e, he⟩ := hH (f (j P y))
      haveI : Nonempty U := ⟨⟨_, hU⟩⟩
      have hU' : f (j P (genericPoint (C P))) ∈ U := by
        have hsp : genericPoint (C P) ⤳ y := (genericPoint_spec (C P)).specializes trivial
        exact ((hsp.map (j P).continuous).map f.continuous).mem_open U.isOpen hU
      obtain ⟨ω₁, c₁, γ, g, hPV, hρ, htγ, hσU, hgval, hunitg⟩ := hσ U e he P hU'
      have hyV : gV P y ∈ ιV ⁻¹ᵁ U := by
        show ιV (gV P y) ∈ U
        rw [← Scheme.Hom.comp_apply, hgV P, Scheme.Hom.comp_apply]
        exact hU
      have hgu := hunitg y hyW hyV
      obtain ⟨h, hhmod, hhval⟩ := exists_divisorialSectionValue_eq he (a * r) φ
      haveI := (hH.nsmul (a * r)).isInvertibleModule_divisorialSheaf
      have hg : g = ιV.app U h := eq_app_of_unit_app_eq ιV _
        (isLocalEquation_pow he (a * r)).isLocalGenerator_invSection φ h hhmod g
        (by rwa [hφ])
      have hfy : f (j P y) ∈ R.basicOpen h := by
        have hmem : ιV (gV P y) ∈ U := hyV
        rw [show f (j P y) = ιV (gV P y) by
          rw [← Scheme.Hom.comp_apply, ← hgV P, Scheme.Hom.comp_apply]]
        rw [R.mem_basicOpen h _ hmem]
        have hst := Scheme.Hom.germ_stalkMap_apply ιV U (gV P y) hyV h
        rw [← hg] at hst
        rw [← hst] at hgu
        exact isUnit_of_map_unit _ _ hgu
      exact ⟨R.basicOpen h, hfy, generatesOn_pullback_smul_formPowR hdim f hpb hu0 hMu w hw hN φ he h
        hhval hfy⟩
  refine ⟨a, ha0, fun α => ?_, ?_⟩
  · obtain ⟨φ, hφ, -⟩ := key (t α) (ht α)
    exact ⟨_, pullback_smul_formPow_mem_logPluricanonicalSections hdim f hH hpb hu0 hMu w hw hN φ, hφ⟩
  · intro hgen x
    by_cases hx : f x ∈ Set.range ιV.base
    · -- over the floor image: a lift of a member of the family generating at a floor point
      rw [hV] at hx
      obtain ⟨_, ⟨y', rfl⟩, hy'⟩ := hx
      have hy'S : ιS y' ∈ ⋃ E ∈ B.roundDown.support, (E.support : Set X) := by
        rw [← hS]; exact ⟨y', rfl⟩
      simp only [Set.mem_iUnion] at hy'S
      obtain ⟨E, hE, hyE⟩ := hy'S
      have hEc : ⌊B.coeff E⌋ ≠ 0 := by
        have h1 := hE
        rw [Finsupp.mem_support_iff] at h1
        rw [← DivisorWithCoeffs.coeff_roundDown]
        exact h1
      set P : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} := ⟨E, hEc⟩
      have hyP : ιS y' ∈ Set.range (j P).base := by rwa [(hC P).2]
      obtain ⟨y, hy⟩ := hyP
      obtain ⟨α, W, hyW, hW⟩ := hgen P y
      obtain ⟨φ, hφ, hφgen⟩ := key (t α) (ht α)
      obtain ⟨U', hU', hgenU'⟩ := hφgen P y ⟨W, hyW, hW⟩
      refine ⟨_, pullback_smul_formPow_mem_logPluricanonicalSections hdim f hH hpb hu0 hMu w hw hN φ,
        f ⁻¹ᵁ U', ?_, hgenU', Or.inl ⟨α, hφ⟩⟩
      show f x ∈ U'
      rw [← hy', ← hy]
      exact hU'
    · -- off the floor image: a section vanishing on `V`
      obtain ⟨φ, hφ0, U, _, e, he, h, hxh, hval⟩ := hq₁ (a * r) har₁ (f x) hx
      refine ⟨_, pullback_smul_formPow_mem_logPluricanonicalSections hdim f hH hpb hu0 hMu w hw hN φ,
        f ⁻¹ᵁ R.basicOpen h, hxh,
        generatesOn_pullback_smul_formPowR hdim f hpb hu0 hMu w hw hN φ he h hval hxh, Or.inr ?_⟩
      intro P ω c htc
      obtain ⟨σ0, hσ0⟩ := hdesc 0 (zero_mem _)
      obtain ⟨UP, hUP, eP, heP⟩ := hH (f (j P (genericPoint (C P))))
      haveI : Nonempty UP := ⟨⟨_, hUP⟩⟩
      obtain ⟨ω₁, c₁, -, -, hPV, hρ, -⟩ := hσ0 UP eP heP P hUP
      have hres := isPoincareResidue_pullback_of_unit_app_eq hdim f hH (hC P).1 ιV (gV P)
        (hgV P) hUP heP ha0 u w φ 0 hPV (by rw [hφ0, map_zero, zero_smul]; rfl) ω₁ c₁ hρ
      rw [map_zero, map_zero, zero_mul, zero_smul] at hres
      letI := functionFieldAlgebra (j P ≫ sX)
      haveI : LocallyOfFiniteType (j P ≫ sX) :=
        (RS.setting.isPair P).isPair.isNormalVariety.1.toLocallyOfFiniteType
      obtain ⟨b⟩ := exists_basis_topForms (sX := j P ≫ sX) (d := n)
        (RS.setting.topologicalKrullDim_eq P)
      have heq : ((0 : (C P).functionField) • formPow ω (k * r) :
          PluriForms ℂ (C P).functionField n (k * r)) = c • formPow ω (k * r) := by
        rw [zero_smul]
        exact htc
      have hpw := smul_formPow_pow_eq b heq a
      have hpw' : (c ^ a • formPow ω (a * (k * r)) :
          RationalPluriForms (j P ≫ sX) n ((a * (k * r) : ℕ) : ℤ)) = 0 := by
        rw [← hpw, zero_pow ha0.ne', zero_smul]
      rw [hpw']
      exact hres

/-! ### Residue restriction maps in every Cartier degree -/

section ResidueAdd

open exteriorPower

variable {k : Type*} [Field k] {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
  {K : Type*} [Field K] [Algebra k K] [Algebra O K] [IsScalarTower k O K] [IsFractionRing O K]
  {L : Type*} [Field L] [Algebra k L] [Algebra O L] [IsScalarTower k O L]

/-- **Sums of logarithmic pluriforms and of their residues.** On a line `Ω^{e+1}_{K/k}`, the sum
of two logarithmic pluriforms is a logarithmic pluriform along one of the two frames, and its
residue is the sum of the residues. -/
private theorem exists_logPluriForm_add [Module.Free O Ω[O⁄k]] [ValuationRing O] {e : ℕ}
    (hline : Module.finrank K (⋀[K]^(e + 1) Ω[K⁄k]) = 1)
    (hπ : Function.Surjective (algebraMap O L)) {t₀ : O} (ht₀ : algebraMap O L t₀ = 0)
    {r : Ω[O⁄k] →ₗ[O] O} (hr : r (KaehlerDifferential.D k O t₀) = 1) (m : ℕ) (g₁ g₂ : O)
    {u₁ u₂ : O} (hu₁ : IsUnit u₁) (hu₂ : IsUnit u₂) (x₁ x₂ : Fin e → O) :
    ∃ (g u : O) (x : Fin e → O), (u = u₁ ∨ u = u₂) ∧
      logPluriForm (O := O) k K m e g₁ (u₁ * t₀) x₁ +
          logPluriForm (O := O) k K m e g₂ (u₂ * t₀) x₂ =
        logPluriForm (O := O) k K m e g (u * t₀) x ∧
      logPluriResidue (O := O) k L m e g₁ x₁ + logPluriResidue (O := O) k L m e g₂ x₂ =
        logPluriResidue (O := O) k L m e g x := by
  have hω : ∀ (g t : O) (x : Fin e → O), logPluriForm (O := O) k K m e g t x =
      algebraMap O K g • formPow ((algebraMap O K t)⁻¹ • ιMulti K (e + 1)
        (Fin.cons (KaehlerDifferential.D k K (algebraMap O K t))
          fun i => KaehlerDifferential.D k K (algebraMap O K (x i)))) m := fun _ _ _ => rfl
  have hv : ∀ (g : O) (x : Fin e → O), logPluriResidue (O := O) k L m e g x =
      algebraMap O L g • formPow (ιMulti L e
        fun i => KaehlerDifferential.D k L (algebraMap O L (x i))) m := fun _ _ => rfl
  rcases exists_frame_comparison (L := L) hline hπ ht₀ hr hu₁ hu₂ x₁ x₂ with
    ⟨c, hcK, hcL⟩ | ⟨c, hcK, hcL⟩
  · beta_reduce at hcK hcL
    refine ⟨g₁ + g₂ * c ^ m, u₁, x₁, Or.inl rfl, ?_, ?_⟩
    · rw [hω, hω, hω, hcK, formPow_smul (algebraMap O K c)]
      simp only [map_add, map_mul, map_pow, add_smul, mul_smul]
      try rfl
    · rw [hv, hv, hv, hcL, formPow_smul (algebraMap O L c)]
      simp only [map_add, map_mul, map_pow, add_smul, mul_smul]
      try rfl
  · beta_reduce at hcK hcL
    refine ⟨g₁ * c ^ m + g₂, u₂, x₂, Or.inr rfl, ?_, ?_⟩
    · rw [hω, hω, hω, hcK, formPow_smul (algebraMap O K c)]
      simp only [map_add, map_mul, map_pow, add_smul, mul_smul]
      try rfl
    · rw [hv, hv, hv, hcL, formPow_smul (algebraMap O L c)]
      simp only [map_add, map_mul, map_pow, add_smul, mul_smul]
      try rfl

end ResidueAdd

section PoincareAdd

variable {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}

/-- **Additivity of the Poincaré residue** along an adjunction step of a variety of dimension
`n + 1`: `Res(τ₁ + τ₂) = Res(τ₁) + Res(τ₂)`. -/
private theorem IsPoincareResidue.add [LocallyOfFiniteType sY] {BY : QDivisor Y}
    {BT : QDivisor T} (hj : IsAdjunctionStep sY BY j BT) {n m : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    {τ₁ τ₂ : RationalPluriForms sY (n + 1) m} {ρ₁ ρ₂ : RationalPluriForms (j ≫ sY) n m}
    (h₁ : IsPoincareResidue sY j n m τ₁ ρ₁) (h₂ : IsPoincareResidue sY j n m τ₂ ρ₂) :
    IsPoincareResidue sY j n m (τ₁ + τ₂) (ρ₁ + ρ₂) := by
  obtain ⟨P, hP, hci⟩ := hj.exists_primeDivisor
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨hdvr, hfree, -, -, -, -⟩ := stalk_facts_of_eq_genericPoint (sY := sY) P hP
  obtain ⟨htow, hsurj⟩ := stalkMap_facts_of_isClosedImmersion (sY := sY) (j := j)
  obtain ⟨ϖ, r, hϖ0, hr, -, -, hunif⟩ := exists_uniformizer_of_eq_genericPoint (sY := sY) P hP
  obtain ⟨b₀⟩ := MMP.Fourfold.exists_basis_topForms (sX := sY) (by exact_mod_cast hY)
  have hline : Module.finrank Y.functionField (⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄ℂ]) =
      1 := by rw [Module.finrank_eq_card_basis b₀, Fintype.card_unit]
  obtain ⟨t₁, g₁, x₁, ht₁, hτ₁, rfl⟩ := h₁
  obtain ⟨t₂, g₂, x₂, ht₂, hτ₂, rfl⟩ := h₂
  obtain ⟨u₁, hu₁, rfl⟩ := hunif t₁ ht₁
  obtain ⟨u₂, hu₂, rfl⟩ := hunif t₂ ht₂
  obtain ⟨g, u, x, hu, hK, hL⟩ := exists_logPluriForm_add (L := T.functionField) hline hsurj hϖ0
    hr m g₁ g₂ hu₁ hu₂ x₁ x₂
  refine ⟨u * ϖ, g, x, ?_, hτ₁ ▸ hτ₂ ▸ hK, hL.symm ▸ rfl⟩
  rcases hu with rfl | rfl
  · exact ht₁
  · exact ht₂

/-- **`ℂ`-linearity of the Poincaré residue**: `Res(c τ) = c Res(τ)`. -/
private theorem IsPoincareResidue.smul {BY : QDivisor Y} {BT : QDivisor T}
    (hj : IsAdjunctionStep sY BY j BT) {n m : ℕ} {τ : RationalPluriForms sY (n + 1) m}
    {ρ : RationalPluriForms (j ≫ sY) n m} (h : IsPoincareResidue sY j n m τ ρ) (c : ℂ) :
    IsPoincareResidue sY j n m (c • τ) (c • ρ) := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨htow, -⟩ := hj.stalkMap_facts
  obtain ⟨t, g, x, ht, hτ, hρ⟩ := h
  refine ⟨t, algebraMap ℂ _ c * g, x, ht, ?_, ?_⟩
  · rw [hτ, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul]
    rfl
  · rw [hρ, map_mul]
    have e : (j.stalkMap (genericPoint T)).hom (algebraMap ℂ _ c) =
        algebraMap ℂ T.functionField c :=
      (IsScalarTower.algebraMap_apply ℂ (Y.presheaf.stalk (j (genericPoint T)))
        T.functionField c).symm
    rw [e, mul_smul]
    rfl

end PoincareAdd

/-- Sums of rational pluriforms do not depend on the structure morphism beyond equality. -/
private theorem add_heq {X : Scheme.{0}} [IsIntegral X] {s s' : X ⟶ Spec (.of ℂ)} (h : s = s')
    {d : ℕ} {m : ℤ} {x₁ x₂ : RationalPluriForms s d m} {y₁ y₂ : RationalPluriForms s' d m}
    (h₁ : HEq x₁ y₁) (h₂ : HEq x₂ y₂) : HEq (x₁ + x₂) (y₁ + y₂) := by
  subst h
  rw [eq_of_heq h₁, eq_of_heq h₂]

/-- Scalar multiples of rational pluriforms do not depend on the structure morphism beyond
equality. -/
private theorem smul_heq {X : Scheme.{0}} [IsIntegral X] {s s' : X ⟶ Spec (.of ℂ)} (h : s = s')
    {d : ℕ} {m : ℤ} (c : ℂ) {x : RationalPluriForms s d m} {y : RationalPluriForms s' d m}
    (h₁ : HEq x y) : HEq (c • x) (c • y) := by
  subst h
  rw [eq_of_heq h₁]

/-- Iterated residues, in the unfolded form, are additive and `ℂ`-linear along a flag whose final
stratum has dimension `e`. -/
private theorem isIteratedResidueRec_add_smul {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} {B : QDivisor S} {n m : ℕ}
    {T : Scheme.{0}} {ι : T ⟶ S} {BT : QDivisor T} (F : StratumAdjunctionData sS B ι BT) :
    ∀ {e : ℕ}, topologicalKrullDim T = e →
      (∀ (τ₁ τ₂ : RationalPluriForms sS n m)
        (ρ₁ ρ₂ : @RationalPluriForms ℂ _ T (ι ≫ sS) F.isIntegral_stratum e m),
        IsIteratedResidueRec τ₁ F e ρ₁ → IsIteratedResidueRec τ₂ F e ρ₂ →
          IsIteratedResidueRec (τ₁ + τ₂) F e (ρ₁ + ρ₂)) ∧
      ∀ (c : ℂ) (τ : RationalPluriForms sS n m)
        (ρ : @RationalPluriForms ℂ _ T (ι ≫ sS) F.isIntegral_stratum e m),
        IsIteratedResidueRec τ F e ρ → IsIteratedResidueRec (c • τ) F e (c • ρ) := by
  induction F with
  | refl h =>
    intro e _
    refine ⟨?_, ?_⟩
    · rintro τ₁ τ₂ ρ₁ ρ₂ ⟨rfl, h₁⟩ ⟨-, h₂⟩
      exact ⟨rfl, add_heq (Category.id_comp sS) h₁ h₂⟩
    · rintro c τ ρ ⟨rfl, h₁⟩
      exact ⟨rfl, smul_heq (Category.id_comp sS) c h₁⟩
  | @step S' T ι BS F j BT hj ih =>
    intro e he
    haveI := F.isIntegral_stratum
    haveI := F.isNormal_stratum
    haveI := F.isLocallyNoetherian_stratum
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : LocallyOfFiniteType (ι ≫ sS) := F.isNormalVariety.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (j ≫ ι ≫ sS) := hj.1.1.toLocallyOfFiniteType
    have hS' : topologicalKrullDim S' = (e + 1 : ℕ) := by
      have h1 := hj.trdeg_add_one
      have h2 := topologicalKrullDim_eq_toNat_trdeg (j ≫ ι ≫ sS)
      have h3 := topologicalKrullDim_eq_toNat_trdeg (ι ≫ sS)
      rw [he] at h2
      rw [h3]
      have : e = (letI := functionFieldAlgebra (j ≫ ι ≫ sS)
          (Algebra.trdeg ℂ T.functionField).toNat) := by exact_mod_cast h2
      congr 1
      omega
    obtain ⟨ihadd, ihsmul⟩ := ih hS'
    refine ⟨?_, ?_⟩
    · rintro τ₁ τ₂ ρ₁ ρ₂ ⟨ρ₀₁, h₀₁, ρ'₁, hr₁, hh₁⟩ ⟨ρ₀₂, h₀₂, ρ'₂, hr₂, hh₂⟩
      exact ⟨ρ₀₁ + ρ₀₂, ihadd _ _ _ _ h₀₁ h₀₂, ρ'₁ + ρ'₂,
        IsPoincareResidue.add hj (by exact_mod_cast hS') hr₁ hr₂,
        add_heq (Category.assoc j ι sS) hh₁ hh₂⟩
    · rintro c τ ρ ⟨ρ₀, h₀, ρ', hr, hh⟩
      exact ⟨c • ρ₀, ihsmul c _ _ h₀, c • ρ', IsPoincareResidue.smul hj hr c,
        smul_heq (Category.assoc j ι sS) c hh⟩

/-- **Iterated residues are additive and `ℂ`-linear** along every flag of strata whose final
stratum has dimension `e`. -/
private theorem isIteratedResidue_add_smul {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} {B : QDivisor S} {n m : ℕ}
    {T : Scheme.{0}} {ι : T ⟶ S} {BT : QDivisor T} (F : StratumAdjunctionData sS B ι BT) (e : ℕ)
    (he : topologicalKrullDim T = e) :
    haveI := F.isIntegral_stratum
    (∀ (τ₁ τ₂ : RationalPluriForms sS n m) (ρ₁ ρ₂ : RationalPluriForms (ι ≫ sS) e m),
      IsIteratedResidue sS B τ₁ F e ρ₁ → IsIteratedResidue sS B τ₂ F e ρ₂ →
        IsIteratedResidue sS B (τ₁ + τ₂) F e (ρ₁ + ρ₂)) ∧
    ∀ (c : ℂ) (τ : RationalPluriForms sS n m) (ρ : RationalPluriForms (ι ≫ sS) e m),
      IsIteratedResidue sS B τ F e ρ → IsIteratedResidue sS B (c • τ) F e (c • ρ) := by
  haveI := F.isIntegral_stratum
  obtain ⟨hadd, hsmul⟩ := isIteratedResidueRec_add_smul (n := n) (m := m) F he
  exact ⟨fun τ₁ τ₂ ρ₁ ρ₂ h₁ h₂ => IsIteratedResidue.of_rec F (hadd _ _ _ _ h₁.rec' h₂.rec'),
    fun c τ ρ h => IsIteratedResidue.of_rec F (hsmul c _ _ h.rec')⟩

/-- **The pull-back of an effective `ℚ`-Cartier `ℚ`-divisor is effective.** With `m` the Cartier
index of `A`, `m f^*A` is the pull-back of the effective Cartier divisor `mA`, whose local
equations are regular (algebraic Hartogs), so their pull-backs have nonnegative order. -/
private theorem nonneg_of_isPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ A.supp}
    {B : QDivisor Y} (h : A.IsPullback f hB B) : 0 ≤ B := by
  have hm := QDivisor.cartierIndex_pos hAq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hAq
  obtain ⟨D', hD', hp⟩ := h _ hm D₀ hD₀ hD₀c
  have hmq : (0 : ℚ) < (A.cartierIndex hAq : ℚ) := by exact_mod_cast hm
  have hD₀n : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ (⊤ : X.Opens)).Nonempty →
      0 ≤ D₀.coeff P := by
    intro P _
    have h2 : (D₀ P : ℚ) = A.cartierIndex hAq * A P :=
      (by simpa using congrArg (· P) hD₀ :
        Divisor.toQDivisor D₀ P = A.cartierIndex hAq * A P)
    exact_mod_cast h2 ▸ mul_nonneg hmq.le (hA P)
  intro E
  have hE : (E.support ∩ f ⁻¹ᵁ (⊤ : X.Opens)).Nonempty :=
    ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, trivial⟩
  have h0 := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hD₀c hD₀n hp E hE
  have h1 : (D' E : ℚ) = A.cartierIndex hAq * B E :=
    (by simpa using congrArg (· E) hD' :
      Divisor.toQDivisor D' E = A.cartierIndex hAq * B E)
  have h0' : (0 : ℚ) ≤ (D' E : ℚ) := by exact_mod_cast h0
  exact nonneg_of_mul_nonneg_right (h1 ▸ h0') hmq

/-- Pull-back of `ℚ`-Cartier `ℚ`-divisors is additive. -/
private theorem qDivisor_isPullback_add {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {G₁ G₂ : QDivisor Y}
    (hG₁ : G₁.IsQCartier) (hG₂ : G₂.IsQCartier)
    {h₁ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₁.supp}
    {h₂ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₂.supp}
    {R₁ R₂ : QDivisor X} (p₁ : G₁.IsPullback f h₁ R₁) (p₂ : G₂.IsPullback f h₂ R₂)
    (h : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (G₁ + G₂).supp) :
    (G₁ + G₂).IsPullback f h (R₁ + R₂) := by
  intro m hm D hD hDc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨m₁, hm₁, A₁, hA₁, hA₁c⟩ := hG₁.exists_pos
  obtain ⟨m₂, hm₂, A₂, hA₂, hA₂c⟩ := hG₂.exists_pos
  have hm₁' : (m₁ : ℤ) ≠ 0 := by exact_mod_cast hm₁.ne'
  have hm₂' : (m₂ : ℤ) ≠ 0 := by exact_mod_cast hm₂.ne'
  obtain ⟨A₁', hA₁', p₁'⟩ := p₁ m₁ hm₁ A₁ hA₁ hA₁c
  obtain ⟨A₂', hA₂', p₂'⟩ := p₂ m₂ hm₂ A₂ hA₂ hA₂c
  have hsuppD : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ D.supp :=
    fun W hW => h W (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hD] at hW)
  -- the supports of the auxiliary divisors
  have hsupp : ∀ {G : QDivisor Y} (A : Divisor Y) (c : ℤ), c ≠ 0 →
      Divisor.toQDivisor A = c • G →
      (∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G.supp) →
      ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ A.supp :=
    fun A c hc hA hG W hW => hG W (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hc hA] at hW)
  set N : ℤ := (m₁ : ℤ) * m₂
  have hN : N ≠ 0 := mul_ne_zero hm₁' hm₂'
  set A : Divisor Y := (m : ℤ) • ((m₂ : ℤ) • A₁ + (m₁ : ℤ) • A₂)
  have hAD : A = N • D := by
    apply Divisor.toQDivisor_injective
    simp only [A, N, map_zsmul, map_add, hA₁, hA₂, hD, smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  have hAc : A.IsCartier := ((hA₁c.zsmul _).add (hA₂c.zsmul _)).zsmul _
  have hA₁N : Divisor.toQDivisor ((m₂ : ℤ) • A₁) = N • G₁ := by
    simp only [map_zsmul, hA₁, smul_smul, N]; congr 1; ring
  have hA₂N : Divisor.toQDivisor ((m₁ : ℤ) • A₂) = N • G₂ := by
    simp only [map_zsmul, hA₂, smul_smul, N]
  have hsum : Divisor.toQDivisor ((m₂ : ℤ) • A₁ + (m₁ : ℤ) • A₂) = N • (G₁ + G₂) := by
    rw [map_add, hA₁N, hA₂N, smul_add]
  have hAq : Divisor.toQDivisor A = ((m : ℤ) * N) • (G₁ + G₂) := by
    simp only [A, map_zsmul, hsum, smul_smul]
  have pA := ((p₁'.zsmul hA₁c (m₂ : ℤ) (hsupp _ _ hN hA₁N h₁)).add (hA₁c.zsmul _)
    (hA₂c.zsmul _) (hsupp _ _ hN hsum h) (p₂'.zsmul hA₂c (m₁ : ℤ) (hsupp _ _ hN hA₂N h₂))).zsmul
    ((hA₁c.zsmul _).add (hA₂c.zsmul _)) (m : ℤ)
    (hsupp _ _ (mul_ne_zero hm' hN) hAq h)
  obtain ⟨D', hD'⟩ := hDc.exists_isPullback hsuppD
  refine ⟨D', ?_, hD'⟩
  have pND := hD'.zsmul hDc N (hsupp _ _ (mul_ne_zero hN hm') (by
    rw [map_zsmul, hD, smul_smul]) h)
  have heq := pA.eq hAc (pND.of_eq hAD.symm)
  have heqQ := congrArg Divisor.toQDivisor heq
  simp only [map_zsmul, map_add, hA₁', hA₂', smul_smul] at heqQ
  ext E
  have := congrArg (fun G : QDivisor X => G.coeff E) heqQ
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, N] at this ⊢
  have hNq : ((m₁ : ℚ) * m₂) ≠ 0 := by positivity
  apply mul_left_cancel₀ hNq
  push_cast at this ⊢
  linear_combination -this

/-- Integral multiples of `ℚ`-Cartier `ℚ`-divisors are `ℚ`-Cartier. -/
private theorem isQCartier_zsmul {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {G : QDivisor X} (hG : G.IsQCartier) (c : ℤ) : (c • G).IsQCartier := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hG
  refine ⟨m, hm, c • D, ?_, hDc.zsmul c⟩
  rw [map_zsmul, hD, smul_smul, smul_smul, mul_comm]

/-- A `ℚ`-divisor with coefficient zero along a prime divisor `P` is pulled back along a morphism
from an irreducible scheme whose generic point maps to the generic point of `P`. -/
private theorem forall_notMem_supp_of_coeff_eq_zero {T Y : Scheme.{0}} [IsIntegral T]
    (j : T ⟶ Y) {P : Mori.PrimeDivisor Y} (hP : j (genericPoint T) = P.genericPoint)
    {G : QDivisor Y} (hG : G.coeff P = 0) :
    ∀ W : irreducibleComponents T, j (componentGenericPoint T W) ∉ G.supp := by
  intro W
  rw [componentGenericPoint_eq_genericPoint, hP]
  exact genericPoint_notMem_supp_of_coeff_eq_zero hG

/-- The pull-back of `G' + cG` is `R' + cR`. -/
private theorem qDivisor_isPullback_add_zsmul {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [IsIntegral X] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : X ⟶ Y} {P : Mori.PrimeDivisor Y} (hfP : f (genericPoint X) = P.genericPoint)
    {G G' : QDivisor Y} (hG : G.IsQCartier) (hG' : G'.IsQCartier) (hGP : G.coeff P = 0)
    (hG'P : G'.coeff P = 0) {R R' : QDivisor X}
    (p : G.IsPullback f (forall_notMem_supp_of_coeff_eq_zero f hfP hGP) R)
    (p' : G'.IsPullback f (forall_notMem_supp_of_coeff_eq_zero f hfP hG'P) R') (c : ℕ)
    (hc : (G' + (c : ℤ) • G).coeff P = 0) :
    (G' + (c : ℤ) • G).IsPullback f (forall_notMem_supp_of_coeff_eq_zero f hfP hc)
      (R' + (c : ℤ) • R) := by
  induction c with
  | zero =>
    have e1 : G' = G' + ((0 : ℕ) : ℤ) • G := by simp
    have e2 : R' = R' + ((0 : ℕ) : ℤ) • R := by simp
    rw [← e2]
    exact isPullback_of_eq_source e1 p'
  | succ c ih =>
    have hcP : (G' + (c : ℤ) • G).coeff P = 0 := by
      simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, hGP, hG'P,
        smul_zero, add_zero]
    have hq : (G' + (c : ℤ) • G).IsQCartier := hG'.add (isQCartier_zsmul hG _)
    have e1 : G' + (c : ℤ) • G + G = G' + ((c + 1 : ℕ) : ℤ) • G := by
      rw [add_assoc]; congr 1; push_cast; rw [add_smul, one_smul]
    have e2 : R' + (c : ℤ) • R + R = R' + ((c + 1 : ℕ) : ℤ) • R := by
      rw [add_assoc]; congr 1; push_cast; rw [add_smul, one_smul]
    rw [← e2]
    refine isPullback_of_eq_source e1 (qDivisor_isPullback_add hq hG (ih hcP) p ?_)
    exact forall_notMem_supp_of_coeff_eq_zero f hfP (by
      rwa [e1])

/-- Log pluricanonical sections along equal structure morphisms. -/
private theorem mem_logPluricanonicalSections_of_heq {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {s s' : Y ⟶ Spec (.of ℂ)} (h : s = s') {d N : ℕ}
    {B : QDivisor Y} {τ : RationalPluriForms s d N} {τ' : RationalPluriForms s' d N}
    (hτ : HEq τ τ') (hm : τ ∈ logPluricanonicalSections s d N B) :
    τ' ∈ logPluricanonicalSections s' d N B := by
  subst h
  cases hτ
  exact hm

/-- **Adjunction steps of dlt pairs are dlt.** If `(Y, B_Y)` is dlt and `T ⟶ Y` is an adjunction
step with different `B_T`, then `(T, B_T)` is dlt. -/
private theorem isDltPair_of_isAdjunctionStep {Y T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {BY : QDivisor Y}
    (hdlt : MMP.Intersection.IsDltPair sY BY) (hpair : MMP.Mori.IsPair sY BY) [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] {j : T ⟶ Y} {BT : QDivisor T}
    (hj : IsAdjunctionStep sY BY j BT) : MMP.Intersection.IsDltPair (j ≫ sY) BT := by
  obtain ⟨-, Q, hQ, hQr, -, -⟩ := id hj
  have hinter : (⋂ P ∈ ({Q} : Finset (Mori.PrimeDivisor Y)), (P.support : Set Y)) =
      Q.support := by simp
  have hS : IsDltStratum sY BY (Q.support : Set Y) := by
    refine ⟨hdlt, {Q}, Finset.singleton_nonempty _, by simpa using hQ, ?_, ?_⟩
    · rw [hinter]
      exact ⟨Q.genericPoint, by
        rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
    · rw [hinter]
      refine ⟨⟨?_, le_rfl⟩, fun T hT _ => hT.2⟩
      rw [PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
  have hj' : IsAdjunctionStep (𝟙 Y ≫ sY) BY j BT := by simpa only [Category.id_comp] using hj
  have h := hS.exists_isStratumAdjunctionPair_and_isDltPair.1.2
    (StratumAdjunctionData.step (.refl hpair) j BT hj') (by simpa using hQr)
  exact isDltPair_congr (by simp) h

/-- `formPow 0 N = 0` for `N > 0`. -/
private theorem formPow_zero_of_pos {K : Type} [Field K] [Algebra ℂ K] {d N : ℕ} (hN : 0 < N) :
    (formPow (0 : ⋀[K]^d Ω[K⁄ℂ]) N : PluriForms ℂ K d N) = 0 := by
  unfold formPow
  exact (PiTensorProduct.tprod K).map_coord_zero ⟨0, hN⟩ rfl

/-- **Residues of log pluricanonical sections are log pluricanonical sections.** Let `(Y, B_Y)` be
a pair on a normal variety of dimension `d + 1` with `B_Y ≤ 1` and `K_Y + B_Y` `ℚ`-Cartier, and
`j : T ⟶ Y` an adjunction step with different `B_T`. Every section `τ` of `N(K_Y + B_Y)` has a
Poincaré residue along `T`, and it is a section of `N(K_T + B_T)`: writing `τ = h ω^{⊗N}` in a
logarithmic frame `ω` along `T`, the divisor
`div τ + N B_Y = (div(hω) + B_Y) + (N - 1)(div ω + B_Y)` is effective and `ℚ`-Cartier, and by
adjunction for the forms `hω` and `ω` its restriction to `T` is `div(Res τ) + N B_T`. -/
private theorem exists_isPoincareResidue_mem_logPluricanonicalSections
    {Y T : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] (hYn : IsNormalVariety ℂ sY) {d : ℕ}
    (hd : topologicalKrullDim Y = (d + 1 : ℕ)) {BY : QDivisor Y} (hle : ∀ P, BY.coeff P ≤ 1)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY (d + 1))
    (hKB : (Divisor.toQDivisor K + BY).IsQCartier)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] {j : T ⟶ Y} {BT : QDivisor T}
    (hj : IsAdjunctionStep sY BY j BT) {N : ℕ} (hN : 0 < N) {τ : RationalPluriForms sY (d + 1) N}
    (hτ : τ ∈ logPluricanonicalSections sY (d + 1) N BY) :
    ∃ ρ : RationalPluriForms (j ≫ sY) d N, IsPoincareResidue sY j d N τ ρ ∧
      ρ ∈ logPluricanonicalSections (j ≫ sY) d N BT := by
  classical
  obtain ⟨hTn, P, hP1, hPr, hci, -⟩ := id hj
  haveI := hci
  haveI : LocallyOfFiniteType (j ≫ sY) := hTn.1.toLocallyOfFiniteType
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace j
  have hBP : BY.coeff P = 1 := le_antisymm (hle P) hP1
  have hjgen : j (genericPoint T) = P.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hPr
  have hdT : topologicalKrullDim T = d := topologicalKrullDim_eq_of_range_eq_support sY j P hPr hd
  have hPmem : (P.support ∩ ((⊤ : Y.Opens) : Set Y)).Nonempty :=
    ⟨P.genericPoint, by rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩
  have hpole : τ ≠ 0 → -(N : ℤ) ≤ P.ordForm τ := by
    intro hτ0
    have h1 := hτ.2 P hPmem hτ0
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, hBP, zsmul_eq_mul,
      mul_one, Int.floor_intCast] at h1
    omega
  have htop : (⊤ : T.Opens) ≠ ⊥ := fun h =>
    (show genericPoint T ∈ (⊥ : T.Opens) from h ▸ trivial).elim
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · -- `T` is a point
    obtain ⟨ρ, hρ⟩ := exists_isPoincareResidue_of_curve hYn (by rw [hd]; rfl) hj τ
      fun P' hP' h0 => by
        obtain rfl : P' = P :=
          AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP'.symm.trans hjgen)
        exact hpole h0
    refine ⟨ρ, hρ, fun h => absurd h htop, fun Γ _ _ => ?_⟩
    exfalso
    have h1 := AlgebraicGeometry.coheight_le_topologicalKrullDim Γ.genericPoint
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hdT] at h1
    exact absurd h1 (by decide)
  obtain ⟨σ, hσ0, hσP, ρσ, hρσ, hρσ0⟩ := exists_simplePole_isPoincareResidue_ne_zero sY hYn
    hdpos (by rw [hd]; norm_cast) j hTn hdT P hPr
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  obtain ⟨t, g₀, x, ht, hg₀u, hσeq, -, hall⟩ := exists_logFrame hd P hjgen hσ0 hσP hρσ hρσ0
  obtain ⟨h, hh⟩ := hall N τ hpole
  set ω₀ := logFrame sY j t x with hω₀def
  set ω₁ := resFrame sY j x with hω₁def
  set ρN : RationalPluriForms (j ≫ sY) d N := (j.stalkMap (genericPoint T)).hom h • formPow ω₁ N
    with hρN
  set r₁ : RationalPluriForms (j ≫ sY) d 1 := (j.stalkMap (genericPoint T)).hom h • formPow ω₁ 1
    with hr₁
  set r₀ : RationalPluriForms (j ≫ sY) d 1 := (1 : T.functionField) • formPow ω₁ 1 with hr₀
  set w₁ : RationalPluriForms (j ≫ sY) d 1 := formPow ω₁ 1 with hw₁
  refine ⟨ρN, hh ▸ isPoincareResidue_smul_formPow_logFrame sY j ht x h, ?_⟩
  by_cases hρ0 : ρN = 0
  · rw [hρ0]; exact zero_mem _
  refine ⟨fun h' => absurd h' htop, fun Γ _ hne => ?_⟩
  have hhb : (j.stalkMap (genericPoint T)).hom h ≠ 0 := fun h0 => hρ0 (by rw [hρN, h0, zero_smul]; rfl)
  have hω₁ : ω₁ ≠ 0 := fun h0 => hρ0 (by rw [hρN, h0, formPow_zero_of_pos hN, smul_zero]; rfl)
  have hω₀ : ω₀ ≠ 0 := fun h0 => hσ0 (by rw [hσeq, h0, formPow_zero_of_pos one_pos, smul_zero]; rfl)
  have hunit_ord : ∀ u : Y.presheaf.stalk (j (genericPoint T)), IsUnit u →
      Y.ord (algebraMap _ Y.functionField u) P.genericPoint = 0 :=
    fun _ hu => ord_algebraMap_stalk_eq_zero_of_isUnit P hjgen hu
  have hhu : IsUnit h := isUnit_of_stalkMap_genericPoint_ne_zero j hhb
  have hhK : algebraMap _ Y.functionField h ≠ 0 := (hhu.map _).ne_zero
  have hg₀K : algebraMap _ Y.functionField g₀ ≠ 0 := (hg₀u.map _).ne_zero
  have hdY : topologicalKrullDim Y = (d + 1 : ℕ) := hd
  -- orders along `P`
  have hω₀P : P.ordForm (show RationalPluriForms sY (d + 1) 1 from formPow ω₀ 1) = -1 := by
    have h1 := ordForm_smul_formPow hdY P hω₀ hg₀K 1
    rw [← hσeq, hσP, hunit_ord g₀ hg₀u] at h1
    simp only [Nat.cast_one, one_mul, zero_add] at h1
    exact h1.symm
  -- the two top forms `ω₀` and `h ω₀`, their residues and their divisors
  set α : RationalPluriForms sY (d + 1) 1 := (1 : Y.functionField) • formPow ω₀ 1 with hαdef
  set α' : RationalPluriForms sY (d + 1) 1 := algebraMap _ Y.functionField h • formPow ω₀ 1
    with hα'def
  have hα0 : α ≠ 0 := smul_formPow_ne_zero hdY hω₀ one_ne_zero 1
  have hα'0 : α' ≠ 0 := smul_formPow_ne_zero hdY hω₀ hhK 1
  have hordα : ∀ Γ : Mori.PrimeDivisor Y, Γ.ordForm α =
      Γ.ordForm (show RationalPluriForms sY (d + 1) 1 from formPow ω₀ 1) := fun Γ => by
    rw [hαdef, ordForm_smul_formPow hdY Γ hω₀ one_ne_zero 1, Scheme.ord_one]; push_cast; ring
  have hordα' : ∀ Γ : Mori.PrimeDivisor Y, Γ.ordForm α' = Y.ord (algebraMap _ Y.functionField h)
      Γ.genericPoint + Γ.ordForm (show RationalPluriForms sY (d + 1) 1 from formPow ω₀ 1) :=
    fun Γ => by rw [hα'def, ordForm_smul_formPow hdY Γ hω₀ hhK 1]; push_cast; ring
  have hordτ : ∀ Γ : Mori.PrimeDivisor Y, Γ.ordForm τ = Y.ord (algebraMap _ Y.functionField h)
      Γ.genericPoint + N * Γ.ordForm (show RationalPluriForms sY (d + 1) 1 from formPow ω₀ 1) :=
    fun Γ => by rw [hh, ordForm_smul_formPow hdY Γ hω₀ hhK N]
  have hresα : IsPoincareResidue sY j d 1 α r₀ := by
    have := isPoincareResidue_smul_formPow_logFrame (m := 1) sY j ht x 1
    rwa [map_one, map_one] at this
  have hresα' : IsPoincareResidue sY j d 1 α' r₁ :=
    isPoincareResidue_smul_formPow_logFrame (m := 1) sY j ht x h
  have hαP : P.ordForm α = -1 := by rw [hordα, hω₀P]
  have hα'P : P.ordForm α' = -1 := by rw [hordα', hω₀P, hunit_ord h hhu, zero_add]
  have hQC : ∀ β : RationalPluriForms sY (d + 1) 1, β ≠ 0 →
      (Divisor.toQDivisor (divisorOfForm β) + BY).IsQCartier := fun β hβ =>
    hKB.add_of_linearlyEquivalent (by
      simpa using (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYn hK hβ).symm)
  set A := Divisor.toQDivisor (divisorOfForm α) + BY with hAdef
  set A' := Divisor.toQDivisor (divisorOfForm α') + BY with hA'def
  have hAP : A.coeff P = 0 := by
    rw [hAdef, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hαP,
      hBP]; norm_num
  have hA'P : A'.coeff P = 0 := by
    rw [hA'def, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hα'P,
      hBP]; norm_num
  obtain ⟨hgA, hpA⟩ := hj.isPullback_divisorOfForm_add_of_isPoincareResidue (by rw [hd]; norm_cast)
    P hPr α hα0 hαP _ hresα (hQC α hα0)
  obtain ⟨hgA', hpA'⟩ := hj.isPullback_divisorOfForm_add_of_isPoincareResidue (by rw [hd]; norm_cast)
    P hPr α' hα'0 hα'P _ hresα' (hQC α' hα'0)
  have hEP : (A' + ((N - 1 : ℕ) : ℤ) • A).coeff P = 0 := by
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, hAP, hA'P, smul_zero,
      add_zero]
  have hpE := qDivisor_isPullback_add_zsmul (f := j) hjgen (hQC α hα0) (hQC α' hα'0) hAP hA'P hpA hpA'
    (N - 1) hEP
  -- the coefficients of `E = div τ + N B_Y`
  have hEcoeff : ∀ Γ : Mori.PrimeDivisor Y, (A' + ((N - 1 : ℕ) : ℤ) • A).coeff Γ =
      (Γ.ordForm τ : ℚ) + N * BY.coeff Γ := by
    intro Γ
    simp only [hAdef, hA'def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, coeff_divisorOfForm, zsmul_eq_mul, hordα, hordα', hordτ]
    have : ((N - 1 : ℕ) : ℚ) = (N : ℚ) - 1 := by
      rw [Nat.cast_sub hN]; push_cast; ring
    push_cast [this]
    ring
  have hE0 : 0 ≤ A' + ((N - 1 : ℕ) : ℤ) • A := by
    intro Γ
    change 0 ≤ (A' + ((N - 1 : ℕ) : ℤ) • A).coeff Γ
    rw [hEcoeff]
    by_cases hτ0 : τ = 0
    · exfalso
      apply hρ0
      have : (algebraMap _ Y.functionField h • formPow ω₀ N : RationalPluriForms sY (d + 1) N) ≠ 0 :=
        smul_formPow_ne_zero hdY hω₀ hhK N
      exact absurd (hh.symm.trans hτ0) this
    have h1 := hτ.2 Γ ⟨Γ.genericPoint, by
      rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩ hτ0
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h1
    have h2 := Int.floor_le (((N : ℤ) : ℚ) * BY.coeff Γ)
    have h1' : (0 : ℚ) ≤ (Γ.ordForm τ : ℚ) + ⌊((N : ℤ) : ℚ) * BY.coeff Γ⌋ := by exact_mod_cast h1
    push_cast at h2 h1' ⊢
    linarith
  have hEq : (A' + ((N - 1 : ℕ) : ℤ) • A).IsQCartier :=
    (hQC α' hα'0).add (isQCartier_zsmul (hQC α hα0) _)
  have hE'0 := nonneg_of_isPullback hE0 hEq hpE Γ
  -- the coefficient of the restriction along `Γ`
  have hρord : Γ.ordForm ρN = T.ord ((j.stalkMap (genericPoint T)).hom h) Γ.genericPoint +
      N * Γ.ordForm w₁ := ordForm_smul_formPow hdT Γ hω₁ hhb N
  have e1 : (divisorOfForm r₁).coeff Γ = T.ord ((j.stalkMap (genericPoint T)).hom h)
      Γ.genericPoint + Γ.ordForm w₁ := by
    rw [coeff_divisorOfForm]
    have := ordForm_smul_formPow hdT Γ hω₁ hhb 1
    simp only [Nat.cast_one, one_mul] at this
    exact this
  have e2 : (divisorOfForm r₀).coeff Γ = Γ.ordForm w₁ := by
    rw [coeff_divisorOfForm]
    have := ordForm_smul_formPow hdT Γ hω₁ one_ne_zero 1
    simp only [Nat.cast_one, one_mul, Scheme.ord_one, zero_add] at this
    exact this
  have hcast : ((N - 1 : ℕ) : ℚ) = (N : ℚ) - 1 := by
    rw [Nat.cast_sub hN]; push_cast; ring
  have key : (0 : ℚ) ≤ (T.ord ((j.stalkMap (genericPoint T)).hom h) Γ.genericPoint : ℚ) +
      N * (Γ.ordForm w₁ : ℚ) + N * BT.coeff Γ := by
    have h0 : (0 : ℚ) ≤ (Divisor.toQDivisor (divisorOfForm r₁) + BT + ((N - 1 : ℕ) : ℤ) •
        (Divisor.toQDivisor (divisorOfForm r₀) + BT)).coeff Γ := hE'0
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, zsmul_eq_mul, e1, e2] at h0
    push_cast [hcast] at h0
    linarith
  rw [hρord, DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul]
  have hfl : -((T.ord ((j.stalkMap (genericPoint T)).hom h) Γ.genericPoint : ℤ) +
      N * Γ.ordForm w₁) ≤ ⌊((N : ℤ) : ℚ) * BT.coeff Γ⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  omega

/-- **Iterated residues of log pluricanonical sections exist.** Let `(X, B)` be a projective dlt
pair of dimension `n` such that `N(K_S + B_S)` is Cartier for every stratum pair `(S, B_S)` reached
by a flag of iterated adjunction. Along every flag, every section of `N(K_X + B)` has an iterated
residue, which is a section of `N(K_S + B_S)`; and `(S, B_S)` is dlt. -/
private theorem exists_isIteratedResidue_of_isCartierDivisor {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : Mori.IsProjectiveVariety ℂ sX) {B : QDivisor X} (hdlt : MMP.Intersection.IsDltPair sX B)
    {n N : ℕ} (hdim : topologicalKrullDim X = n) (hN : 0 < N)
    (hcart : ∀ {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
      (F : StratumAdjunctionData sX B ι BS),
      haveI := F.isIntegral_stratum
      haveI := F.isNormal_stratum
      haveI := F.isLocallyNoetherian_stratum
      ∃ (d : ℕ) (K : Divisor S), K.IsCanonicalDivisor (ι ≫ sX) d ∧
        ((N : ℤ) • (Divisor.toQDivisor K + BS)).IsCartierDivisor) :
    ∀ {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS)
      (e : ℕ), topologicalKrullDim S = e → ∀ τ ∈ logPluricanonicalSections sX n N B,
      haveI := F.isIntegral_stratum
      haveI := F.isNormal_stratum
      haveI := F.isLocallyNoetherian_stratum
      ∃ ρ : RationalPluriForms (ι ≫ sX) e N, IsIteratedResidue sX B τ F e ρ ∧
        ρ ∈ logPluricanonicalSections (ι ≫ sX) e N BS ∧
        MMP.Intersection.IsDltPair (ι ≫ sX) BS := by
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  intro S ι BS F
  induction F with
  | refl h =>
    intro e he τ hτ
    obtain rfl : e = n := by
      have := he.symm.trans hdim
      exact_mod_cast this
    exact ⟨_, IsIteratedResidue.refl h, mem_logPluricanonicalSections_of_heq
      (Category.id_comp sX).symm (cast_heq _ _).symm hτ, isDltPair_congr (Category.id_comp sX).symm hdlt⟩
  | @step S T ι BS F j BT hj ih =>
    intro e he τ hτ
    haveI := F.isIntegral_stratum
    haveI := F.isNormal_stratum
    haveI := F.isLocallyNoetherian_stratum
    haveI := F.isClosedImmersion
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : IsNormal T := hj.1.2
    haveI : IsLocallyNoetherian T := by
      have := hj.1.1
      exact LocallyOfFiniteType.isLocallyNoetherian (j ≫ ι ≫ sX)
    haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (j ≫ ι ≫ sX) := hj.1.1.toLocallyOfFiniteType
    haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace ι
    have hS' : topologicalKrullDim S = (e + 1 : ℕ) := by
      have h1 := hj.trdeg_add_one
      have h2 := topologicalKrullDim_eq_toNat_trdeg (j ≫ ι ≫ sX)
      have h3 := topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX)
      rw [he] at h2
      rw [h3]
      have : e = (letI := functionFieldAlgebra (j ≫ ι ≫ sX)
          (Algebra.trdeg ℂ T.functionField).toNat) := by exact_mod_cast h2
      congr 1
      omega
    obtain ⟨ρ, hρF, hρmem, hdltS⟩ := ih (e + 1) hS' τ hτ
    obtain ⟨d', K, hK, hKC⟩ := hcart F
    have hd' : d' = e + 1 := by
      have := hK.topologicalKrullDim_eq
      rw [hS'] at this
      exact_mod_cast this.symm
    subst hd'
    have hKB : (Divisor.toQDivisor K + BS).IsQCartier := ⟨N, by exact_mod_cast hN.ne', hKC⟩
    obtain ⟨ρ', hr, hρ'mem⟩ := exists_isPoincareResidue_mem_logPluricanonicalSections
      F.isNormalVariety hS' hdltS.2.1 hK hKB hj hN hρmem
    have hpair : MMP.Mori.IsPair (ι ≫ sX) BS := ⟨F.isNormalVariety, e + 1, K, hK, hKB⟩
    refine ⟨_, IsIteratedResidue.step hρF hr,
      mem_logPluricanonicalSections_of_heq (Category.assoc j ι sX).symm (cast_heq _ _).symm hρ'mem,
      isDltPair_congr (Category.assoc j ι sX).symm (isDltPair_of_isAdjunctionStep hdltS hpair hj)⟩

/-- **Residue restriction maps exist in every degree of the stratified setting**: the iterated
residue along a flag exists (`exists_isIteratedResidue_of_isCartierDivisor`), is unique and is
linear. -/
private theorem nonempty_residueRestriction {I : Type*} {X : I → Scheme.{0}}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {sX : ∀ i, X i ⟶ Spec (.of ℂ)} {B : ∀ i, QDivisor (X i)} {n N : ℕ}
    (hset : IsStratifiedSectionSetting sX B n N) :
    Nonempty (ResidueRestriction sX B n N) := by
  classical
  have hex : ∀ (i : I) {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T}
      (F : StratumAdjunctionData (sX i) (B i) ι BT) (e : ℕ), topologicalKrullDim T = e →
      ∀ τ ∈ logPluricanonicalSections (sX i) n N (B i),
        haveI := F.isIntegral_stratum
        ∃ ρ : RationalPluriForms (ι ≫ sX i) e N, IsIteratedResidue (sX i) (B i) τ F e ρ :=
    fun i _ _ _ F e he τ hτ => by
      haveI := F.isIntegral_stratum
      obtain ⟨ρ, hρ, -⟩ := exists_isIteratedResidue_of_isCartierDivisor
        (hset.isProjectiveVariety i) (hset.isDltPair i) (hset.topologicalKrullDim_eq i) hset.pos
        (hset.isCartierDivisor i) F e he τ hτ
      exact ⟨ρ, hρ⟩
  exact ⟨{ setting := hset,
            toFun := fun i T ι BT F e =>
              haveI := F.isIntegral_stratum
              if he : topologicalKrullDim T = e then
                { toFun := fun τ => (hex i F e he τ τ.2).choose
                  map_add' := fun τ₁ τ₂ => IsIteratedResidue.unique
                    (hex i F e he (τ₁ + τ₂) (τ₁ + τ₂).2).choose_spec
                    ((isIteratedResidue_add_smul F e he).1 _ _ _ _
                      (hex i F e he τ₁ τ₁.2).choose_spec
                      (hex i F e he τ₂ τ₂.2).choose_spec)
                  map_smul' := fun c τ => IsIteratedResidue.unique
                    (hex i F e he (c • τ) (c • τ).2).choose_spec
                    ((isIteratedResidue_add_smul F e he).2 c _ _
                      (hex i F e he τ τ.2).choose_spec) }
              else 0,
            isIteratedResidue := fun i T ι BT F e τ he => by
              haveI := F.isIntegral_stratum
              simp only [dif_pos he]
              exact (hex i F e he τ τ.2).choose_spec }⟩

/-! ### Passing to a multiple of the degree -/

/-- Serre's lifting for `qH` gives Serre's lifting for `q(m₀H)`. -/
private theorem exists_forall_surjective_unit_app_top_nsmul {R Z : Scheme.{0}}
    [IsLocallyNoetherian R] [IsNormal R] (ιZ : Z ⟶ R)
    {H : Divisor R} {m₀ : ℕ} (hm₀ : 0 < m₀)
    (h : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app
        (q • H).divisorialSheaf).app ⊤)) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app
        (q • m₀ • H).divisorialSheaf).app ⊤) := by
  obtain ⟨q₀, hq₀⟩ := h
  refine ⟨q₀, fun q hq => ?_⟩
  rw [smul_smul]
  exact hq₀ _ (hq.trans (Nat.le_mul_of_pos_right q hm₀))

/-- Sections of `𝓘_Z(qH)` generating off `Z` give sections of `𝓘_Z(q(m₀H))` generating off `Z`. -/
private theorem exists_forall_exists_mem_basicOpen_nsmul {R Z : Scheme.{0}} [IsIntegral R]
    [IsLocallyNoetherian R] [IsNormal R] (ιZ : Z ⟶ R) {H : Divisor R} {m₀ : ℕ} (hm₀ : 0 < m₀)
    (h : ∃ q₁ : ℕ, ∀ q : ℕ, q₁ ≤ q → ∀ y : R, y ∉ Set.range ιZ.base →
      ∃ φ : Γ((q • H).divisorialSheaf, ⊤),
        ((Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app
          (q • H).divisorialSheaf).app ⊤ φ = 0 ∧
        ∃ (U : R.Opens) (_ : Nonempty U) (e : (RationalFunctions R)ˣ) (_ : H.IsLocalEquation U e)
          (h : Γ(R, U)), y ∈ R.basicOpen h ∧
          divisorialSectionValue φ = R.germToFunctionField U h *
            MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
              (((e ^ q)⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R)) :
    ∃ q₁ : ℕ, ∀ q : ℕ, q₁ ≤ q → ∀ y : R, y ∉ Set.range ιZ.base →
      ∃ φ : Γ((q • m₀ • H).divisorialSheaf, ⊤),
        ((Scheme.Modules.pullbackPushforwardAdjunction ιZ).unit.app
          (q • m₀ • H).divisorialSheaf).app ⊤ φ = 0 ∧
        ∃ (U : R.Opens) (_ : Nonempty U) (e : (RationalFunctions R)ˣ)
          (_ : (m₀ • H).IsLocalEquation U e) (h : Γ(R, U)), y ∈ R.basicOpen h ∧
          divisorialSectionValue φ = R.germToFunctionField U h *
            MMP.Threefold.Mori.Helpers.evalFF (univComponent R)
              (((e ^ q)⁻¹ : (RationalFunctions R)ˣ) : RationalFunctions R) := by
  obtain ⟨q₁, hq₁⟩ := h
  refine ⟨q₁, fun q hq y hy => ?_⟩
  rw [smul_smul]
  obtain ⟨φ, hφ0, U, hU, e, he, h, hyh, hval⟩ :=
    hq₁ (q * m₀) (hq.trans (Nat.le_mul_of_pos_right q hm₀)) y hy
  refine ⟨φ, hφ0, U, hU, e ^ m₀, isLocalEquation_pow he m₀, h, hyh, ?_⟩
  rw [hval, ← pow_mul, mul_comm m₀ q]

/-- **Equal powers of an admissible system.** Raising every member of an admissible system `t` of
sections of `m(K_{X_i} + B_i)` to the power `q`, in coordinates `c ω^{⊗m} ↦ c^q ω^{⊗qm}`, gives an
admissible system in degree `qm` for every residue restriction structure in that degree: by
uniqueness its iterated residues are the `q`-th powers of those of `t`. The powers generate where
`t` does. -/
private theorem exists_pow_mem_admissibleSections {I : Type*} {Y : I → Scheme.{0}}
    [∀ i, IsIntegral (Y i)] [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    {sY : ∀ i, Y i ⟶ Spec (.of ℂ)} {BY : ∀ i, QDivisor (Y i)} {n m q : ℕ} (hq : 0 < q)
    (RS : ResidueRestriction sY BY n m) (RS' : ResidueRestriction sY BY n (q * m))
    {t : ∀ i, logPluricanonicalSections (sY i) n m (BY i)} (ht : t ∈ admissibleSections RS) :
    ∃ t' : ∀ i, logPluricanonicalSections (sY i) n (q * m) (BY i),
      t' ∈ admissibleSections RS' ∧
      (∀ i, letI := functionFieldAlgebra (sY i)
        ∀ (ω : ⋀[(Y i).functionField]^n Ω[(Y i).functionField⁄ℂ]) (c : (Y i).functionField),
          (t i : RationalPluriForms (sY i) n m) =
              c • (formPow ω m : RationalPluriForms (sY i) n m) →
            (t' i : RationalPluriForms (sY i) n ((q * m : ℕ) : ℤ)) =
              c ^ q • (formPow ω (q * m) : RationalPluriForms (sY i) n ((q * m : ℕ) : ℤ))) ∧
      (∀ i (W : (Y i).Opens), GeneratesOn (BY i) m W (t i : RationalPluriForms (sY i) n m) →
        GeneratesOn (BY i) (q * m) W (t' i : RationalPluriForms (sY i) n ((q * m : ℕ) : ℤ))) := by
  classical
  have hlft : ∀ i, LocallyOfFiniteType (sY i) := fun i =>
    (RS.setting.isPair i).isPair.isNormalVariety.1.toLocallyOfFiniteType
  have hbex : ∀ i, Nonempty (letI := functionFieldAlgebra (sY i)
      Module.Basis Unit (Y i).functionField (⋀[(Y i).functionField]^n Ω[(Y i).functionField⁄ℂ])) :=
    fun i => by
      haveI := hlft i
      exact exists_basis_topForms (sX := sY i) (RS.setting.topologicalKrullDim_eq i)
  let b := fun i => (hbex i).some
  let c : ∀ i, (Y i).functionField := fun i =>
    letI := functionFieldAlgebra (sY i)
    (ZTensorPower.basis (b i) m).repr (t i : RationalPluriForms (sY i) n m) ()
  have htc : ∀ i, letI := functionFieldAlgebra (sY i)
      (t i : RationalPluriForms (sY i) n m) = c i • (formPow ((b i) ()) m :
        RationalPluriForms (sY i) n m) := fun i => by
    letI := functionFieldAlgebra (sY i)
    exact eq_repr_smul_formPow (b i) _
  let v : ∀ i, RationalPluriForms (sY i) n ((q * m : ℕ) : ℤ) := fun i =>
    letI := functionFieldAlgebra (sY i)
    show RationalPluriForms (sY i) n ((q * m : ℕ) : ℤ) from c i ^ q • formPow ((b i) ()) (q * m)
  -- orders of the powers
  have hord : ∀ i (Γ : Mori.PrimeDivisor (Y i)), c i ≠ 0 →
      Γ.ordForm (v i) = q * Γ.ordForm (t i : RationalPluriForms (sY i) n m) := by
    intro i Γ hc
    haveI := hlft i
    letI := functionFieldAlgebra (sY i)
    have hd := RS.setting.topologicalKrullDim_eq i
    have hb0 : (b i) () ≠ 0 := (b i).ne_zero ()
    rw [htc i]
    change Γ.ordForm (show RationalPluriForms (sY i) n ((q * m : ℕ) : ℤ) from
      c i ^ q • formPow ((b i) ()) (q * m)) = _
    rw [ordForm_smul_formPow hd Γ hb0 (pow_ne_zero _ hc) (q * m),
      ordForm_smul_formPow hd Γ hb0 hc m, Scheme.ord_pow hc]
    push_cast
    ring
  have hv0 : ∀ i, v i ≠ 0 → c i ≠ 0 := fun i hv h0 => hv (by
    letI := functionFieldAlgebra (sY i)
    change (show RationalPluriForms (sY i) n ((q * m : ℕ) : ℤ) from
      c i ^ q • formPow ((b i) ()) (q * m)) = 0
    rw [h0, zero_pow hq.ne', zero_smul]; rfl)
  have ht0 : ∀ i, c i ≠ 0 → (t i : RationalPluriForms (sY i) n m) ≠ 0 := fun i hc => by
    haveI := hlft i
    letI := functionFieldAlgebra (sY i)
    rw [htc i]
    exact smul_formPow_ne_zero (RS.setting.topologicalKrullDim_eq i) ((b i).ne_zero ()) hc m
  have hmem : ∀ i, v i ∈ logPluricanonicalSections (sY i) n (q * m) (BY i) := by
    intro i
    letI := functionFieldAlgebra (sY i)
    refine ⟨fun hU => ?_, fun Γ hΓ hne => ?_⟩
    · have h1 := (t i).2.1 hU
      have hc : c i = 0 := by
        by_contra hc
        exact ht0 i hc h1
      change (show RationalPluriForms (sY i) n ((q * m : ℕ) : ℤ) from
        c i ^ q • formPow ((b i) ()) (q * m)) = 0
      rw [hc, zero_pow hq.ne', zero_smul]; rfl
    · have hc := hv0 i hne
      have h1 := (t i).2.2 Γ hΓ (ht0 i hc)
      rw [hord i Γ hc]
      rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h1 ⊢
      have hfl : (q : ℤ) * ⌊((m : ℤ) : ℚ) * (BY i).coeff Γ⌋ ≤
          ⌊(((q * m : ℕ) : ℤ) : ℚ) * (BY i).coeff Γ⌋ := by
        rw [Int.le_floor]
        have := Int.floor_le (((m : ℤ) : ℚ) * (BY i).coeff Γ)
        have hq0 : (0 : ℚ) ≤ q := by positivity
        push_cast at this ⊢
        nlinarith
      nlinarith
  refine ⟨fun i => ⟨v i, hmem i⟩, ?_, fun i ω c' hc' => ?_, fun i W hW => ?_⟩
  · -- admissibility
    intro i i' S S' ι ι' BS BS' F F' e h₁ h₂ hdS hdS' σ hσ
    haveI := F.isIntegral_stratum
    haveI := F.isNormal_stratum
    haveI := F.isLocallyNoetherian_stratum
    haveI := F'.isIntegral_stratum
    haveI := F'.isNormal_stratum
    haveI := F'.isLocallyNoetherian_stratum
    haveI : LocallyOfFiniteType (ι ≫ sY i) := F.isNormalVariety.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (ι' ≫ sY i') := F'.isNormalVariety.1.toLocallyOfFiniteType
    have hrec : ∀ (k : I) {T : Scheme.{0}} {ιT : T ⟶ Y k} {BT : QDivisor T}
        (G : StratumAdjunctionData (sY k) (BY k) ιT BT),
        haveI := G.isIntegral_stratum
        topologicalKrullDim T = e →
        letI := functionFieldAlgebra (ιT ≫ sY k)
        ∀ (bT : Module.Basis Unit T.functionField (⋀[T.functionField]^e Ω[T.functionField⁄ℂ]))
          (cT : T.functionField),
          RS.toFun k G e (t k) = cT • (formPow (bT ()) m : RationalPluriForms (ιT ≫ sY k) e m) →
          RS'.toFun k G e ⟨v k, hmem k⟩ = cT ^ q • (formPow (bT ()) (q * m) :
            RationalPluriForms (ιT ≫ sY k) e ((q * m : ℕ) : ℤ)) := by
      intro k T ιT BT G hT bT cT hcT
      haveI := G.isIntegral_stratum
      letI := functionFieldAlgebra (sY k)
      letI := functionFieldAlgebra (ιT ≫ sY k)
      have hIt := (RS.isIteratedResidue k G e (t k) hT).rec'
      rw [hcT, htc k] at hIt
      have hpow := isIteratedResidueRec_pow ((b k) ()) (c k) G hT (bT ()) cT hIt q hq
      exact IsIteratedResidueRec.unique G (RS'.isIteratedResidue k G e ⟨v k, hmem k⟩ hT).rec' hpow
    letI := functionFieldAlgebra (ι ≫ sY i)
    letI := functionFieldAlgebra (ι' ≫ sY i')
    obtain ⟨b₁⟩ := exists_basis_topForms (sX := ι ≫ sY i) hdS
    obtain ⟨b₂⟩ := exists_basis_topForms (sX := ι' ≫ sY i') hdS'
    set c₁ := (ZTensorPower.basis b₁ m).repr (RS.toFun i F e (t i)) ()
    set c₂ := (ZTensorPower.basis b₂ m).repr (RS.toFun i' F' e (t i')) ()
    have hc₁ : RS.toFun i F e (t i) =
        c₁ • (formPow (b₁ ()) m : RationalPluriForms (ι ≫ sY i) e m) :=
      eq_repr_smul_formPow b₁ _
    have hc₂ : RS.toFun i' F' e (t i') =
        c₂ • (formPow (b₂ ()) m : RationalPluriForms (ι' ≫ sY i') e m) :=
      eq_repr_smul_formPow b₂ _
    have hadm := ht i i' F F' e (Nat.zero_le _) (Nat.zero_le _) hdS hdS' σ hσ
    beta_reduce at hadm
    rw [hc₁, hc₂, pluriformPullback_smul_formPow' hdS hdS' σ.toHom (b₂ ()) m c₂] at hadm
    beta_reduce
    rw [hrec i F hdS b₁ c₁ hc₁, hrec i' F' hdS' b₂ c₂ hc₂,
      pluriformPullback_smul_formPow' hdS hdS' σ.toHom (b₂ ()) (q * m) (c₂ ^ q),
      map_pow (σ.toHom) c₂ q]
    exact smul_formPow_pow_eq b₁ hadm q
  · -- the powers in coordinates
    letI := functionFieldAlgebra (sY i)
    exact smul_formPow_pow_eq (b i) ((htc i).symm.trans hc') q
  · -- generation
    haveI := hlft i
    letI := functionFieldAlgebra (sY i)
    have htn := hW.1
    have hc : c i ≠ 0 := fun h0 => htn (by rw [htc i, h0, zero_smul]; rfl)
    refine ⟨smul_formPow_ne_zero (RS.setting.topologicalKrullDim_eq i) ((b i).ne_zero ())
      (pow_ne_zero _ hc) (q * m), fun Γ hΓ => ?_⟩
    · change (Γ.ordForm (v i) : ℚ) + _ = 0
      rw [hord i Γ hc]
      have := hW.2 Γ hΓ
      push_cast at this ⊢
      linear_combination (q : ℚ) * this

/-- Transport of a property along an equality of degrees. -/
private theorem exists_of_eq_degree {N₁ N₂ : ℕ} (h : N₁ = N₂) {F : ℕ → Type*}
    {Pr : ∀ N, F N → Prop} {x : F N₁} (hx : Pr N₁ x) : ∃ y : F N₂, Pr N₂ y := by
  subst h
  exact ⟨x, hx⟩

/-- **Preadmissible lifting when the floor image has the structure-sheaf property.** Let `(X, B)`
be a `ℚ`-factorial projective dlt pair (`MMP.Fourfold.IsPair`, `MMP.Intersection.IsDltPair`) on
a normal complex variety of dimension `n + 1`, with a canonical divisor `K`, `K + B` semiample, and
`f : X ⟶ R` a projective morphism to a normal projective variety with `f_* 𝒪_X = 𝒪_R` and
`k(K + B) ∼_ℚ f^*H` for an ample Cartier divisor `H` on `R`, `k > 0`. Let `ιS : S ⟶ X` be the
reduced floor `⌊B⌋ ≠ 0`, `ιV : V ⟶ R` the reduced image `f(S)`, and `fS : S ⟶ V` over `f` with
`fS_* 𝒪_S = 𝒪_V`; let `j_P : C_P ⟶ X` with `B_{C_P}` be the adjunction steps onto the floor
components `P`. Let `m` be even with `k ∣ m`, and `RS` a residue restriction structure on the
pairs `(C_P, B_{C_P})` in degree `m`. Then for every finite family `t_α ∈ admissibleSections RS`
there is `a > 0` such that, for every residue restriction structure `RX` on `(X, B)` in degree
`am`,
* for every `α` some `s ∈ preadmissibleSections RX` has Poincaré residue `(t_α)_P^{⊗a}` along
  every `j_P`;
* if the systems `t_α` generate every `𝒪_{C_P}(m(K_{C_P} + B_{C_P}))` at every point, then for
  every `x ∈ X` some section `σ` of `am(K + B)` generates `𝒪_X(am(K + B))` near `x`, and either
  every Poincaré residue of `σ` along the `j_P` is zero, or for one `α` every residue is
  `(t_α)_P^{⊗a}`. -/
@[mmp "lem_fourfold_admissible_lifting_stein_floor"]
public theorem _root_.MMP.Fourfold.exists_isPoincareResidue_pow_of_mem_admissibleSections
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : Mori.IsProjectiveVariety ℂ sX) {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ)) (hQ : IsQFactorial sX)
    {B : QDivisor X} (hB : IsPair sX B) (hdlt : MMP.Intersection.IsDltPair sX B)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (hsemi : QDivisor.IsRelativelySemiample sX (Divisor.toQDivisor K + B))
    {R : Scheme.{0}} [IsIntegral R] [CompactSpace R] [IsLocallyNoetherian R] [IsNormal R]
    {sR : R ⟶ Spec (.of ℂ)} (hRn : IsNormalVariety ℂ sR) (hRp : Mori.IsProjectiveVariety ℂ sR)
    (f : X ⟶ R) (hf : f ≫ sR = sX) (hfp : IsProjectiveMorphism f)
    (hfO : ∀ U : R.Opens, IsIso (f.app U))
    {k : ℕ} (hk : 0 < k) {H : Divisor R} (hH : H.IsCartier) (hHamp : H.IsRelativelyAmple sR hH)
    {M : Divisor X} (hM : ∃ hfH, H.IsPullback f hfH M)
    (hMeq : (Divisor.toQDivisor M).QLinearlyEquivalent ((k : ℚ) • (Divisor.toQDivisor K + B)))
    (hS0 : B.roundDown ≠ 0)
    {S : Scheme.{0}} (ιS : S ⟶ X) [IsClosedImmersion ιS] [IsReduced S]
    (hS : Set.range ιS.base = ⋃ E ∈ B.roundDown.support, (E.support : Set X))
    {V : Scheme.{0}} (ιV : V ⟶ R) [IsClosedImmersion ιV] [IsReduced V]
    (hV : Set.range ιV.base = f.base '' Set.range ιS.base)
    (fS : S ⟶ V) (hfS : fS ≫ ιV = ιS ≫ f) (hfSO : ∀ U : V.Opens, IsIso (fS.app U))
    (C : {P : Mori.PrimeDivisor X // ⌊B.coeff P⌋ ≠ 0} → Scheme.{0})
    [∀ P, IsIntegral (C P)] [∀ P, IsLocallyNoetherian (C P)] [∀ P, IsNormal (C P)]
    (j : ∀ P, C P ⟶ X) (BC : ∀ P, QDivisor (C P))
    (hC : ∀ P, IsAdjunctionStep sX B (j P) (BC P) ∧
      Set.range (j P).base = (P.1.support : Set X))
    {m : ℕ} (hm : Even m) (hkm : k ∣ m) (RS : ResidueRestriction (fun P => j P ≫ sX) BC n m)
    {A : Type} [Finite A] (t : A → ∀ P, logPluricanonicalSections (j P ≫ sX) n m (BC P))
    (ht : ∀ α, t α ∈ admissibleSections RS) :
    ∃ a : ℕ, 0 < a ∧
      (∀ RX : ResidueRestriction (fun _ : Unit => sX) (fun _ => B) (n + 1) (a * m),
        ∀ α, ∃ s ∈ preadmissibleSections RX, ∀ P,
          letI := functionFieldAlgebra (j P ≫ sX)
          ∀ (ω : ⋀[(C P).functionField]^n Ω[(C P).functionField⁄ℂ]) (c : (C P).functionField),
            (t α P : RationalPluriForms (j P ≫ sX) n m) =
                c • (formPow ω m : RationalPluriForms (j P ≫ sX) n m) →
              IsPoincareResidue sX (j P) n (a * m)
                (s () : RationalPluriForms sX (n + 1) ((a * m : ℕ) : ℤ))
                (c ^ a • (formPow ω (a * m) :
                  RationalPluriForms (j P ≫ sX) n ((a * m : ℕ) : ℤ)))) ∧
      ((∀ P (y : C P), ∃ α, ∃ W : (C P).Opens, y ∈ W ∧
          GeneratesOn (BC P) m W (t α P : RationalPluriForms (j P ≫ sX) n m)) →
        ∀ x : X, ∃ σ ∈ logPluricanonicalSections sX (n + 1) (a * m) B, ∃ U : X.Opens, x ∈ U ∧
          GeneratesOn B (a * m) U (σ : RationalPluriForms sX (n + 1) ((a * m : ℕ) : ℤ)) ∧
          ((∀ P, IsPoincareResidue sX (j P) n (a * m)
              (σ : RationalPluriForms sX (n + 1) ((a * m : ℕ) : ℤ)) 0) ∨
            ∃ α, ∀ P,
              letI := functionFieldAlgebra (j P ≫ sX)
              ∀ (ω : ⋀[(C P).functionField]^n Ω[(C P).functionField⁄ℂ])
                (c : (C P).functionField),
                (t α P : RationalPluriForms (j P ≫ sX) n m) =
                    c • (formPow ω m : RationalPluriForms (j P ≫ sX) n m) →
                  IsPoincareResidue sX (j P) n (a * m)
                    (σ : RationalPluriForms sX (n + 1) ((a * m : ℕ) : ℤ))
                    (c ^ a • (formPow ω (a * m) :
                      RationalPluriForms (j P ≫ sX) n ((a * m : ℕ) : ℤ))))) := by
  classical
  obtain ⟨m₀, hm₀, φ, hφ⟩ := hMeq
  obtain ⟨hfH, hpb⟩ := hM
  obtain ⟨r, rfl⟩ := hkm
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  -- the principal divisor `m₀(M - k(K + B)) = div φ`, read in the function field
  set u := MMP.Threefold.Mori.Helpers.evalFF (univComponent X) (φ : RationalFunctions X) with hu
  have hu0 : u ≠ 0 := (φ.isUnit.map _).ne_zero
  have hcoefP : ∀ Γ : Mori.PrimeDivisor X, (m₀ : ℚ) * ((M.coeff Γ : ℚ) -
      k * ((K.coeff Γ : ℚ) + B.coeff Γ)) = ((principalDivisor φ).coeff Γ : ℚ) := by
    intro Γ
    have h1 := congrArg (fun D : QDivisor X => D.coeff Γ) hφ
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, zsmul_eq_mul, smul_eq_mul] at h1
    push_cast at h1 ⊢
    linear_combination h1
  have hordu : ∀ Γ : Mori.PrimeDivisor X, X.ord u Γ.genericPoint = (principalDivisor φ).coeff Γ := by
    intro Γ
    have hc : Γ.component = univComponent X := by
      apply Subtype.ext
      have h2 : (Γ.component : Set X) ∈ ({Set.univ} : Set (Set X)) := by
        rw [← irreducibleComponents_eq_singleton]
        exact Γ.component.2
      exact h2
    rw [coeff_principalDivisor, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hc]
  have hMu : ∀ Γ : Mori.PrimeDivisor X, (X.ord u Γ.genericPoint : ℚ) =
      (m₀ • M).coeff Γ - ((m₀ * k : ℕ) : ℚ) * (K.coeff Γ + B.coeff Γ) := by
    intro Γ
    rw [hordu, ← hcoefP Γ, DivisorWithCoeffs.coeff_smul, nsmul_eq_mul]
    push_cast
    ring
  -- `m₀ M` is the pull-back of `m₀ H`
  have hpb' : ∃ hfH', (m₀ • H).IsPullback f hfH' (m₀ • M) := by
    have hsupp : ∀ Z : irreducibleComponents X,
        f (componentGenericPoint X Z) ∉ ((m₀ : ℤ) • H).supp := fun Z hZ => hfH Z (by
      obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
      exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, fun h0 => hE (by
        rw [DivisorWithCoeffs.coeff_smul, h0, smul_zero]), hmem⟩)
    have e1 : ((m₀ : ℤ) • H) = m₀ • H := natCast_zsmul _ _
    have e2 : ((m₀ : ℤ) • M) = m₀ • M := natCast_zsmul _ _
    rw [← e1, ← e2]
    exact ⟨hsupp, hpb.zsmul hH (m₀ : ℤ) hsupp⟩
  -- `m₀ k r (K + B)` is Cartier
  have hCart : (((m₀ * (k * r) : ℕ) : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor := by
    refine ⟨r • (m₀ • M) - r • principalDivisor φ, ?_,
      (((hpb.isCartier hH).nsmul m₀).nsmul r).sub ((Divisor.isCartier_principalDivisor φ).nsmul r)⟩
    refine Finsupp.ext fun Γ => ?_
    change (Divisor.toQDivisor _).coeff Γ =
      DivisorWithCoeffs.coeff (((m₀ * (k * r) : ℕ) : ℤ) • (Divisor.toQDivisor K + B)) Γ
    have h1 := hcoefP Γ
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, nsmul_eq_mul, zsmul_eq_mul, smul_eq_mul]
    push_cast at h1 ⊢
    linear_combination (r : ℚ) * h1
  -- Serre's theorems for `m₀ H`
  have hq₀ := exists_forall_surjective_unit_app_top_nsmul ιV hm₀
    (exists_forall_surjective_unit_app_top hRp hH hHamp ιV)
  have hq₁ := exists_forall_exists_mem_basicOpen_nsmul ιV hm₀
    (exists_forall_exists_mem_basicOpen_of_notMem_range hRp hH hHamp ιV)
  -- residue restrictions in degree `m₀ m`, and the `m₀`-th powers of the floor systems
  have hset : IsStratifiedSectionSetting (fun P => j P ≫ sX) BC n (m₀ * (k * r)) :=
    { finite := RS.setting.finite
      isProjectiveVariety := RS.setting.isProjectiveVariety
      isPair := RS.setting.isPair
      isDltPair := RS.setting.isDltPair
      topologicalKrullDim_eq := RS.setting.topologicalKrullDim_eq
      even := hm.mul_left m₀
      pos := Nat.mul_pos hm₀ RS.setting.pos
      isCartierDivisor := by
        intro P S ι BS F
        haveI := F.isIntegral_stratum
        haveI := F.isNormal_stratum
        haveI := F.isLocallyNoetherian_stratum
        obtain ⟨d, K', hK', D', hD', hD'c⟩ := RS.setting.isCartierDivisor P F
        refine ⟨d, K', hK', (m₀ : ℤ) • D', ?_, hD'c.zsmul _⟩
        rw [map_zsmul, hD', smul_smul]
        congr 1
        all_goals (push_cast; ring) }
  obtain ⟨RS'⟩ := nonempty_residueRestriction hset
  choose t' ht' htpow htgen using fun α => exists_pow_mem_admissibleSections hm₀ RS RS' (ht α)
  obtain ⟨a', ha', hlift, hgen⟩ := exists_liftsPow hX hdim hQ hB hdlt hK hRn hRp f hf hfp hfO
    (Nat.mul_pos hm₀ hk) (hH.nsmul m₀) hu0 hMu hpb' hS0 ιS hS ιV hV fS hfS hfSO hq₀ hq₁ C j BC hC
    (hm.mul_left m₀) ⟨r, by ring⟩ hCart RS' t' ht'
  have hdeg : a' * (m₀ * (k * r)) = a' * m₀ * (k * r) := by ring
  refine ⟨a' * m₀, Nat.mul_pos ha' hm₀, fun RX α => ?_, fun hg x => ?_⟩
  · obtain ⟨s, hs, hl⟩ := hlift α
    obtain ⟨s₂, hs₂, hl₂⟩ := exists_of_eq_degree (F := fun N => RationalPluriForms sX (n + 1)
      ((N : ℕ) : ℤ)) (Pr := fun N σ => σ ∈ logPluricanonicalSections sX (n + 1) N B ∧ ∀ P,
        letI := functionFieldAlgebra (j P ≫ sX)
        ∀ (ω : ⋀[(C P).functionField]^n Ω[(C P).functionField⁄ℂ]) (c : (C P).functionField),
          (t α P : RationalPluriForms (j P ≫ sX) n ((k * r : ℕ) : ℤ)) =
              c • (formPow ω (k * r) : RationalPluriForms (j P ≫ sX) n ((k * r : ℕ) : ℤ)) →
            IsPoincareResidue sX (j P) n N σ
              (c ^ (a' * m₀) • (formPow ω N : RationalPluriForms (j P ≫ sX) n ((N : ℕ) : ℤ))))
      hdeg ⟨hs, fun P ω c hc => by
        have h1 := hl P ω (c ^ m₀) (htpow α P ω c hc)
        rwa [← pow_mul, mul_comm m₀ a'] at h1⟩
    exact ⟨fun _ => ⟨s₂, hs₂⟩, mem_preadmissibleSections_of_liftsPow hX hdim hC RS (ht α) RX _ hl₂,
      hl₂⟩
  · have hg' : ∀ P (y : C P), ∃ α, ∃ W : (C P).Opens, y ∈ W ∧
        GeneratesOn (BC P) (m₀ * (k * r)) W
          (t' α P : RationalPluriForms (j P ≫ sX) n ((m₀ * (k * r) : ℕ) : ℤ)) := by
      intro P y
      obtain ⟨α, W, hyW, hW⟩ := hg P y
      exact ⟨α, W, hyW, htgen α P W hW⟩
    obtain ⟨s, hs, U, hxU, hU, hl⟩ := hgen hg' x
    obtain ⟨s₂, hs₂, hU₂, hl₂⟩ := exists_of_eq_degree (F := fun N => RationalPluriForms sX (n + 1)
      ((N : ℕ) : ℤ)) (Pr := fun N σ => σ ∈ logPluricanonicalSections sX (n + 1) N B ∧
        GeneratesOn B N U σ ∧ ((∀ P, IsPoincareResidue sX (j P) n N σ 0) ∨ ∃ α, ∀ P,
          letI := functionFieldAlgebra (j P ≫ sX)
          ∀ (ω : ⋀[(C P).functionField]^n Ω[(C P).functionField⁄ℂ]) (c : (C P).functionField),
            (t α P : RationalPluriForms (j P ≫ sX) n ((k * r : ℕ) : ℤ)) =
                c • (formPow ω (k * r) : RationalPluriForms (j P ≫ sX) n ((k * r : ℕ) : ℤ)) →
              IsPoincareResidue sX (j P) n N σ
                (c ^ (a' * m₀) • (formPow ω N :
                  RationalPluriForms (j P ≫ sX) n ((N : ℕ) : ℤ)))))
      hdeg ⟨hs, hU, by
        rcases hl with ⟨α, hl⟩ | hl
        · refine Or.inr ⟨α, fun P ω c hc => ?_⟩
          have h1 := hl P ω (c ^ m₀) (htpow α P ω c hc)
          rwa [← pow_mul, mul_comm m₀ a'] at h1
        · refine Or.inl fun P => ?_
          letI := functionFieldAlgebra (j P ≫ sX)
          have h0 := hl P 0 0 (by rw [zero_smul]; rfl)
          rwa [zero_pow (Nat.pos_iff_ne_zero.mp ha'), zero_smul] at h0⟩
    exact ⟨s₂, hs₂, U, hxU, hU₂, hl₂⟩

end Proof_lem_fourfold_admissible_lifting_stein_floor

end
