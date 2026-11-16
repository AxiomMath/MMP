module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import StacksFrontier.AlgebraicGeometry.Properties.Dimension
import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Curves.RationalFunctionDegree
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.LogCanonicalOneResolution
import MMP.AlgebraicGeometry.Singularities.SncStrata.ZeroPlaceExtraction
import MMP.AlgebraicGeometry.Singularities.FiniteLowDiscrepancyKlt
import MMP.AlgebraicGeometry.Resolution.CommonLogResolution
import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.StratumDiscrepancyMonotone
public import MMP.AlgebraicGeometry.StalkValuationRing

/-!
# Crepant birational maps match the differents of matched floor curves

Let `(X_i, B_i)` be the components of a stratified section setting of dimension two, and
`σ : k(X_j) ≅ k(X_i)` the pull-back of a crepant birational map `(X_i, B_i) ⇢ (X_j, B_j)` which
carries the valuation of a floor curve `P ⊆ X_i` to that of a floor curve `P' ⊆ X_j`. Let
`T ⟶ X_i`, `T' ⟶ X_j` be the normal curves over `P`, `P'`, with their residue differents `B_T`,
`B_{T'}`, and `σ_T : k(T') ≅ k(T)` the isomorphism of residue fields induced by `σ`. Then `σ_T`
matches the points of `T` and `T'` (`ord_Q ∘ σ_T = ord_{Q'}`), and matched points carry the same
coefficient of the differents: `B_T(Q) = B_{T'}(Q')`.

## Main results

* `MMP.Fourfold.ordForm_pluriformPullback_eq_ordPullback`: orders of pulled-back forms along a
  divisor over the target with the transported valuation.
* `MMP.Fourfold.isPoincareResidue_pluriformPullback`: Poincaré residues commute with pull-back.
* `MMP.Fourfold.exists_isOpenImmersion_functionFieldMap_eq_of_functionFieldEquiv`: a
  `k`-isomorphism of function fields of integral schemes of finite type over `k` is induced by an
  isomorphism of dense open subschemes.
* `MMP.Fourfold.exists_primeDivisor_coeff_eq_residue_of_isCrepantBirationalMap`: crepant maps
  match the points and the differents of matched floor curves.

## Implementation notes

The coefficients of the differents are compared on a common log resolution `W` of the birational
map: the crepant boundaries of the two pairs on `W` agree, since `σ` preserves log discrepancies,
and adjunction along the strict transform of the floor curve, a smooth component of the snc
boundary of `W`, makes the restricted crepant boundary the crepant boundary of both curve pairs.

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Definition 4.2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori TopologicalSpace
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

/-! ### Pull-backs of forms along isomorphisms of function fields -/

section OrdForm

open MMP.Threefold.Mori.Helpers MMP.Threefold.Mori.ModelIndependence

/-- **Orders of pulled-back forms along a valuation.** Let `σ : k(X') ≅ k(X)` be a
`k`-isomorphism, `Γ` a prime divisor of `X` and `(Y, f, E)` a divisor over `X'` whose valuation
is `v_Γ ∘ σ`. Then `ord_Γ(σ^* τ) = ord_E(f^* τ)` for every rational form `τ` on `X'`. -/
theorem ordForm_pluriformPullback_eq_ordPullback {k : Type} [Field k] [CharZero k]
    {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hX' : IsNormalVariety k sX') {n : ℕ} (hn' : topologicalKrullDim X' = n)
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
    · subst hy
      simp [Scheme.ord_zero]
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
    exact (Γ.divisorialValuation_le_one_iff _).mp this
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
  have hd : (Algebra.trdeg k X'.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX') hn'
  have htr : Algebra.trdeg k X'.functionField = Algebra.trdeg k D.Y.functionField :=
    trdeg_functionField_eq_of_bijective sX' D.f hb
  have htrσ : Algebra.trdeg k X'.functionField = Algebra.trdeg k X.functionField :=
    AlgEquiv.trdeg_eq σ
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
    IsScalarTower.of_algebraMap_eq hψ
  have hS4 : IsScalarTower k D.E.localRing X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = algebraMap Γ.localRing X.functionField (ψ (algebraMap k D.E.localRing c))
    rw [IsScalarTower.algebraMap_apply k Γ.localRing X.functionField c,
      IsScalarTower.algebraMap_apply k D.E.localRing Γ.localRing c]
    rfl
  have : Algebra.EssFiniteType k D.Y.functionField :=
    essFiniteType_functionField (sX := D.f ≫ sX')
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX' D.f hb hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator (k := k) (K := D.Y.functionField)
    (K' := X.functionField) (htr.symm.trans htrσ) hd1
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
    hord hσE hωT (pullbackForms (K' := D.Y.functionField) m τ)
  let Aσ : Algebra X'.functionField X.functionField := (σ.toHom).toRingHom.toAlgebra
  have tσ : @IsScalarTower k X'.functionField X.functionField _ Aσ.toSMul _ := by
    letI := Aσ
    exact IsScalarTower.of_algebraMap_eq fun c => ((σ.toHom).commutes c).symm
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

end OrdForm

section ResidueFunctoriality

variable {k : Type} [Field k] {X X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']

/-- `φ^*(c w^{⊗a}) = φ(c) (φ^*w)^{⊗a}` for every `d`-form `w`, on varieties of dimension `d`. -/
theorem pluriformPullback_smul_formPow_of_topologicalKrullDim_eq [CharZero k]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {d : ℕ} (hX : topologicalKrullDim X = d)
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
      unfold formPow
      congr 1
      funext i
      exact i.elim0
    have e2 : (formPow (topFormsMap k X'.functionField X.functionField d w) 0 :
        PluriForms k X.functionField d (0 : ℕ)) =
        formPow (topFormsMap k X'.functionField X.functionField d ω) 0 := by
      unfold formPow
      congr 1
      funext i
      exact i.elim0
    rw [e1, e2]
    exact pluriformPullback_smul_formPow φ hω 0 c
  by_cases hw : w = 0
  · have h0 : ∀ {K : Type} [Field K] [Algebra k K],
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
theorem topFormsMap_smul_ιMulti_D (φ : FunctionFieldHom sX sX') {d : ℕ}
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

/-- **Poincaré residues commute with pull-back.** Let `σ : k(X') → k(X)` and
`σ_T : k(T') → k(T)` be `k`-homomorphisms of function fields, and `ψ : 𝒪_{X',T'} → 𝒪_{X,T}` a ring
homomorphism of the local rings along the divisors, compatible with `σ` and `σ_T` and preserving
orders. Then `Res_T(σ^*τ) = σ_T^* Res_{T'}(τ)`. -/
theorem isPoincareResidue_pluriformPullback [CharZero k] {T T' : Scheme.{0}} [IsIntegral T]
    [IsIntegral T'] [IsLocallyNoetherian X] [IsLocallyNoetherian X'] (j : T ⟶ X) (j' : T' ⟶ X')
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sX']
    [LocallyOfFiniteType (j ≫ sX)] [LocallyOfFiniteType (j' ≫ sX')]
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
  · have e := pluriformPullback_smul_formPow_of_topologicalKrullDim_eq hX hX' σ
      ((algebraMap _ X'.functionField t)⁻¹ • exteriorPower.ιMulti X'.functionField (n + 1)
        (Fin.cons (KaehlerDifferential.D k X'.functionField (algebraMap _ _ t))
          fun i => KaehlerDifferential.D k X'.functionField (algebraMap _ _ (x i)))) m
      (algebraMap _ X'.functionField g)
    have e2 := topFormsMap_smul_ιMulti_D σ (algebraMap _ X'.functionField t)⁻¹
      (Fin.cons (algebraMap _ X'.functionField t) fun i => algebraMap _ X'.functionField (x i) :
        Fin (n + 1) → X'.functionField)
    have hc : ∀ {K : Type} [Field K] [Algebra k K] (a : K) (b : Fin n → K),
        (Fin.cons (KaehlerDifferential.D k K a) (fun i => KaehlerDifferential.D k K (b i)) :
          Fin (n + 1) → Ω[K⁄k]) =
          fun i => KaehlerDifferential.D k K ((Fin.cons a b : Fin (n + 1) → K) i) := by
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
  · have e := pluriformPullback_smul_formPow_of_topologicalKrullDim_eq hT hT' σT
      (exteriorPower.ιMulti T'.functionField n
        fun i => KaehlerDifferential.D k T'.functionField
          ((j'.stalkMap (genericPoint T')).hom (x i)))
      m ((j'.stalkMap (genericPoint T')).hom g)
    refine e.trans ?_
    have e2 := topFormsMap_smul_ιMulti_D σT 1
      (fun i => (j'.stalkMap (genericPoint T')).hom (x i))
    rw [one_smul, map_one, one_smul] at e2
    rw [e2]
    simp only [hψT, formPow]
    rfl

end ResidueFunctoriality

/-! ### Isomorphisms of function fields spread out to birational maps -/

section Spread

variable {k : Type} [Field k]

/-- `Spec k(X) ⟶ X ⟶ Spec k` is `Spec` of the `k`-algebra structure of `k(X)`. -/
private theorem fromSpecStalk_genericPoint_comp_eq {X : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) :
    X.fromSpecStalk (genericPoint X) ≫ sX =
      Spec.map (CommRingCat.ofHom
        (@algebraMap k X.functionField _ _ (functionFieldAlgebra sX))) := by
  rw [MMP.fromSpecStalk_comp_eq]
  rfl

/-- **Isomorphisms of function fields are birational maps.** Let `X`, `X'` be integral schemes
locally of finite type over `k` and `σ : k(X') ≅ k(X)` a `k`-isomorphism. There are an integral
scheme `U` and dominant open immersions `j : U ⟶ X`, `j' : U ⟶ X'` with `j' ≫ sX' = j ≫ sX` and
`j'^* = j^* ∘ σ` on function fields. -/
theorem exists_isOpenImmersion_functionFieldMap_eq_of_functionFieldEquiv {X X' : Scheme.{0}}
    [IsIntegral X] [IsIntegral X'] {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] (σ : FunctionFieldEquiv sX sX') :
    ∃ (U : Scheme.{0}) (_ : IsIntegral U) (j : U ⟶ X) (j' : U ⟶ X') (_ : IsOpenImmersion j)
      (_ : IsOpenImmersion j') (_ : IsDominant j) (_ : IsDominant j'),
      j' ≫ sX' = j ≫ sX ∧ ∀ t, functionFieldMap j' t = functionFieldMap j ((σ.toHom) t) := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  have hα : (Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
      X'.fromSpecStalk (genericPoint X')) ≫ sX' = X.fromSpecStalk (genericPoint X) ≫ sX := by
    rw [Category.assoc, fromSpecStalk_genericPoint_comp_eq, fromSpecStalk_genericPoint_comp_eq,
      ← Spec.map_comp]
    congr 1
    ext c
    exact σ.commutes c
  let Pm := Scheme.PartialMap.ofFromSpecStalk sX sX' _ hα
  have hη : genericPoint X ∈ Pm.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sX' _ hα
  have hP : Pm.domain.fromSpecStalkOfMem (genericPoint X) hη ≫ Pm.hom =
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
        X'.fromSpecStalk (genericPoint X') :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sX' _ hα
  have hPs : Pm.hom ≫ sX' = Pm.domain.ι ≫ sX :=
    Scheme.PartialMap.ofFromSpecStalk_comp sX sX' _ hα
  haveI : Nonempty Pm.domain := ⟨⟨_, hη⟩⟩
  haveI : IsIntegral Pm.domain.toScheme := isIntegral_of_isOpenImmersion Pm.domain.ι
  haveI : IsDominant Pm.domain.ι :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion Pm.domain.ι
  -- `Pm.hom` maps the generic point to the generic point
  have hpt : Pm.domain.fromSpecStalkOfMem (genericPoint X) hη (IsLocalRing.closedPoint _) =
      ⟨genericPoint X, hη⟩ := by
    apply Subtype.ext
    change (Pm.domain.fromSpecStalkOfMem (genericPoint X) hη ≫ Pm.domain.ι)
      (IsLocalRing.closedPoint _) = _
    rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint]
  have hgen : Pm.hom ⟨genericPoint X, hη⟩ = genericPoint X' := by
    have e := congr($hP (IsLocalRing.closedPoint X.functionField))
    change Pm.hom (Pm.domain.fromSpecStalkOfMem (genericPoint X) hη
        (IsLocalRing.closedPoint _)) = X'.fromSpecStalk (genericPoint X')
        (Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom)
          (IsLocalRing.closedPoint X.functionField)) at e
    haveI : Subsingleton (Spec X'.functionField) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum X'.functionField))
    rwa [hpt, Subsingleton.elim (Spec.map _ (IsLocalRing.closedPoint X.functionField))
        (IsLocalRing.closedPoint X'.functionField), Scheme.fromSpecStalk_closedPoint] at e
  haveI : IsDominant Pm.hom := ⟨Dense.mono
    (Set.singleton_subset_iff.mpr (Set.mem_range.mpr ⟨_, hgen⟩))
    (dense_iff_closure_eq.mpr (genericPoint_spec X').def)⟩
  -- on function fields, morphisms factoring through `Pm.hom` are `σ` followed by the inclusion
  have key : ∀ (V : Scheme.{0}) [IsIntegral V] (a : V ⟶ Pm.domain.toScheme) (g₁ : V ⟶ X)
      (g₂ : V ⟶ X') [IsDominant g₁] [IsDominant g₂], a ≫ Pm.domain.ι = g₁ → a ≫ Pm.hom = g₂ →
      functionFieldMap g₂ = (functionFieldMap g₁).comp σ.toRingEquiv.toRingHom := by
    intro V _ a g₁ g₂ _ _ h₁ h₂
    have ha : V.fromSpecStalk (genericPoint V) ≫ a =
        Spec.map (CommRingCat.ofHom (functionFieldMap g₁)) ≫
          Pm.domain.fromSpecStalkOfMem (genericPoint X) hη := by
      rw [← cancel_mono Pm.domain.ι, Category.assoc, h₁, Category.assoc,
        Scheme.Opens.fromSpecStalkOfMem_ι, functionFieldMap_fromSpecStalk]
    have h : Spec.map (CommRingCat.ofHom (functionFieldMap g₂)) ≫
          X'.fromSpecStalk (genericPoint X') =
        Spec.map (CommRingCat.ofHom ((functionFieldMap g₁).comp σ.toRingEquiv.toRingHom)) ≫
          X'.fromSpecStalk (genericPoint X') := by
      rw [functionFieldMap_fromSpecStalk, ← h₂, ← Category.assoc, ha, CommRingCat.ofHom_comp,
        Spec.map_comp, Category.assoc, Category.assoc, hP]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp h))
  -- `Pm.hom` induces an isomorphism of local rings at the generic point
  have hbij : Function.Bijective (functionFieldMap Pm.hom) := by
    rw [key Pm.domain (𝟙 _) Pm.domain.ι Pm.hom (Category.id_comp _) (Category.id_comp _)]
    exact (MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion Pm.domain.ι ⊤
      ⟨⟨_, hη⟩, trivial⟩).comp σ.bijective
  let e := X'.presheaf.stalkCongr
    (Inseparable.of_eq (map_genericPoint_of_isDominant Pm.hom).symm)
  haveI : IsIso (e.hom ≫ Pm.hom.stalkMap (genericPoint Pm.domain)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI : IsIso (Pm.hom.stalkMap (genericPoint Pm.domain)) := IsIso.of_isIso_comp_left e.hom _
  haveI : LocallyOfFiniteType (Pm.hom ≫ sX') := hPs ▸ inferInstance
  haveI : LocallyOfFiniteType Pm.hom := LocallyOfFiniteType.of_comp (g := sX') ‹_›
  obtain ⟨A, hA, hAimm⟩ := exists_isOpenImmersion_res_of_isIso_stalkMap Pm.hom
    (genericPoint Pm.domain)
    (by rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _) inferInstance
  haveI := hAimm
  haveI : Nonempty A := ⟨⟨_, hA⟩⟩
  haveI : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
  haveI : IsDominant (A.ι ≫ Pm.domain.ι) :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant (A.ι ≫ Pm.hom) := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  refine ⟨A, inferInstance, A.ι ≫ Pm.domain.ι, A.ι ≫ Pm.hom, inferInstance, inferInstance,
    inferInstance, inferInstance, by rw [Category.assoc, hPs, Category.assoc], fun t => ?_⟩
  exact congrArg (fun φ => φ t) (key A A.ι _ _ rfl rfl)

end Spread

/-! ### Points over prime divisors and strict transforms -/

section StrictTransform

/-- Over the generic point of a prime divisor `P` of a normal integral scheme `S`, a proper
birational morphism `q : Z ⟶ S` is a local isomorphism: `η_P` lies in the biregular locus of `q`
and is the image of a point of `Z` of coheight one. -/
theorem exists_map_eq_genericPoint_of_isBirationalMorphism {Z S : Scheme.{0}}
    [IsIntegral Z] [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] (q : Z ⟶ S) [IsProper q]
    (hq : IsBirationalMorphism q) (P : MMP.Mori.PrimeDivisor S) :
    ∃ t : Z, q t = P.genericPoint ∧ P.genericPoint ∈ biregularLocus q ∧
      Order.coheight t = 1 := by
  have hb : P.genericPoint ∈ biregularLocus q :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal q hq
      P.coheight_genericPoint.le
  set V := biregularLocus q
  haveI : IsIso (q ∣_ V) := isBiregular_biregularLocus q
  let v : V.toScheme := ⟨P.genericPoint, hb⟩
  have e : inv (q ∣_ V) ≫ (q ⁻¹ᵁ V).ι ≫ q = V.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hqt : q ((q ⁻¹ᵁ V).ι ((inv (q ∣_ V)) v)) = P.genericPoint := by
    have := congrArg (fun φ : V.toScheme ⟶ S => φ v) e
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  refine ⟨_, hqt, hb, ?_⟩
  have := MMP.Positivity.coheight_map_of_mem_biregularLocus q
    (x := (q ⁻¹ᵁ V).ι ((inv (q ∣_ V)) v)) (by rwa [hqt])
  rw [← this, hqt, P.coheight_genericPoint]

/-- A divisor `(Y, f, E)` over a normal variety `X` whose centre `f(η_E)` is the generic point of
a prime divisor `P` in the biregular locus of `f` has the valuation of `P`. -/
theorem valuation_eq_ofPrimeDivisor_of_mem_biregularLocus {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (D : DivisorOver k sX)
    (P : MMP.Mori.PrimeDivisor X) (hD : D.f D.E.genericPoint = P.genericPoint)
    (hb : P.genericPoint ∈ biregularLocus D.f) :
    D.valuation = (DivisorOver.ofPrimeDivisor k hX P).valuation := by
  set V := biregularLocus D.f
  haveI : IsIso (D.f ∣_ V) := isBiregular_biregularLocus D.f
  have hU : D.E.genericPoint ∈ D.f ⁻¹ᵁ V := by
    change D.f D.E.genericPoint ∈ V
    rwa [hD]
  let e : (D.f ⁻¹ᵁ V).toScheme ≅ V.toScheme := asIso (D.f ∣_ V)
  refine MMP.Positivity.DivisorOver.valuation_eq_of_iso D (DivisorOver.ofPrimeDivisor k hX P)
    (D.f ⁻¹ᵁ V) V hU hb e ?_ ?_
  · change (D.f ∣_ V) ≫ V.ι ≫ 𝟙 X = (D.f ⁻¹ᵁ V).ι ≫ D.f
    rw [Category.comp_id, morphismRestrict_ι]
  · apply Subtype.ext
    change ((D.f ∣_ V) ≫ V.ι) ⟨_, hU⟩ = P.genericPoint
    rwa [morphismRestrict_ι]

/-- A closed immersion from an integral scheme maps the generic point to the generic point of the
closure `P` of its range. -/
private theorem map_genericPoint_eq_of_range_eq {T S : Scheme.{0}} [IsIntegral T] (j : T ⟶ S)
    [IsClosedImmersion j] (P : MMP.Mori.PrimeDivisor S)
    (hP : Set.range j.base = (P.support : Set S)) : j (genericPoint T) = P.genericPoint := by
  have h1 := (genericPoint_spec T).image j.base.hom.continuous
  rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq, hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact h1.eq isGenericPoint_closure

/-- The range of the reduced closure of a point `t` is `closure {t}`. -/
theorem range_subschemeι_vanishingIdeal_closure {W : Scheme.{0}} (t : W) :
    Set.range (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {t})).subschemeι =
      closure {t} := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure]

/-- **The strict transform of a prime divisor.** Let `p : W ⟶ S` be proper, a local isomorphism
at a point `t` over the generic point of a prime divisor `P ⊆ S`, and `j : T ⟶ S` a closed
immersion of an integral scheme onto `P`. Then the reduced closure of `t` maps to `T` by a proper
birational morphism lifting `p`. -/
theorem exists_strictTransform_of_isIso_stalkMap {W S T : Scheme.{0}} [IsIntegral W]
    (t : W) [IsIntegral S] [IsIntegral T] (p : W ⟶ S) [IsProper p] (j : T ⟶ S)
    [IsClosedImmersion j] (P : MMP.Mori.PrimeDivisor S)
    (hP : Set.range j.base = (P.support : Set S)) (ht : p t = P.genericPoint)
    (hiso : IsIso (p.stalkMap t)) :
    haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure t
    ∃ pT : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {t})).subscheme ⟶ T,
      pT ≫ j = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {t})).subschemeι ≫ p ∧
        IsProper pT ∧ IsBirationalMorphism pT := by
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure t
  set jW := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {t})).subschemeι
  have H : j.ker ≤ (jW ≫ p).ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range j,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range (jW ≫ p)]
    apply Scheme.IdealSheafData.vanishingIdeal_antimono
    change closure (Set.range (jW ≫ p)) ⊆ closure (Set.range j)
    apply closure_mono
    rintro _ ⟨x, rfl⟩
    have hx : jW x ∈ closure {t} := by
      rw [← range_subschemeι_vanishingIdeal_closure]
      exact ⟨x, rfl⟩
    have h2 := (specializes_iff_mem_closure.mpr hx).map p.base.hom.continuous
    rw [ht] at h2
    rw [hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp h2
  set pT := IsClosedImmersion.lift j (jW ≫ p) H
  have hsq : pT ≫ j = jW ≫ p := IsClosedImmersion.lift_fac j (jW ≫ p) H
  haveI : IsProper (pT ≫ j) := by
    rw [hsq]
    infer_instance
  haveI : IsProper pT := IsProper.of_comp pT j
  refine ⟨pT, hsq, inferInstance, ?_⟩
  set g := genericPoint (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {t})).subscheme
  have hjg : jW g = t := Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure t
  have hjT := map_genericPoint_eq_of_range_eq j P hP
  have hpTg : pT g = genericPoint T := by
    apply j.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, hjg, ht, hjT]
  have hiso' : IsIso (p.stalkMap (jW g)) := by rwa [hjg]
  have hsurj : Function.Surjective (pT.stalkMap g) := by
    have e1 := Scheme.Hom.stalkMap_congr_hom (pT ≫ j) (jW ≫ p) hsq g
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e1
    have hs : Function.Surjective (j.stalkMap (pT g) ≫ pT.stalkMap g) := by
      rw [e1]
      have h1 := jW.stalkMap_surjective g
      have h2 := (ConcreteCategory.bijective_of_isIso (p.stalkMap (jW g))).2
      have h3 := (ConcreteCategory.bijective_of_isIso (S.presheaf.stalkCongr (Inseparable.of_eq
        (congrArg (fun φ => φ.base g) hsq))).hom).2
      exact h1.comp (h2.comp h3)
    exact Function.Surjective.of_comp hs
  have hinj : Function.Injective (pT.stalkMap g) := by
    have hF : IsField (T.presheaf.stalk (pT g)) := by
      rw [hpTg]
      exact Field.toIsField _
    letI := hF.toField
    exact (pT.stalkMap g).hom.injective
  haveI : IsIso (pT.stalkMap g) := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  haveI : LocallyOfFiniteType pT :=
    LocallyOfFiniteType.of_comp (inferInstance : LocallyOfFiniteType (pT ≫ j))
  have hfin : (irreducibleComponents T).Finite := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, hgU, hU⟩ := exists_isOpenImmersion_res_of_isIso_stalkMap pT g hfin inferInstance
  exact MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' pT U ⟨g, hgU⟩

/-- The canonical isomorphism of stalks at equal points commutes with the maps to the function
field. -/
theorem algebraMap_stalkCongr_hom {X : Scheme.{0}} [IsIntegral X] {z z' : X}
    (h : z = z') (a : X.presheaf.stalk z) :
    algebraMap (X.presheaf.stalk z') X.functionField
        ((X.presheaf.stalkCongr (.of_eq h)).hom.hom a) =
      algebraMap (X.presheaf.stalk z) X.functionField a := by
  subst h
  simp

/-- Along a commutative square `p_V ≫ ι = j_W ≫ p` with `p_V` dominant, the extension of function
fields `p_V^*` carries the restriction `ι^♯ a` of a germ `a` at `ι(z)`, `z = p_V(y)`, to the
restriction along `j_W` of the germ `p^♯ a` at `j_W(y)`. -/
theorem functionFieldMap_algebraMap_stalkMap_of_comp_eq {Y T X W : Scheme.{0}}
    [IsIntegral Y] [IsIntegral T] (pV : Y ⟶ T) [IsDominant pV] (ι : T ⟶ X) (jW : Y ⟶ W)
    (p : W ⟶ X) (hsq : pV ≫ ι = jW ≫ p) (y : Y) {z : T} (hz : pV y = z)
    (hzw : ι z = p (jW y)) (a : X.presheaf.stalk (ι z)) :
    functionFieldMap pV (algebraMap (T.presheaf.stalk z) T.functionField
        ((ι.stalkMap z).hom a)) =
      algebraMap (Y.presheaf.stalk y) Y.functionField ((jW.stalkMap y).hom
        ((p.stalkMap (jW y)).hom ((X.presheaf.stalkCongr (.of_eq hzw)).hom.hom a))) := by
  subst hz
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
  congr 1
  have e3 := Scheme.Hom.stalkMap_congr_hom (pV ≫ ι) (jW ≫ p) hsq y
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e3
  exact congrArg (fun φ => φ.hom a) e3

end StrictTransform

variable {k : Type} [Field k] {I : Type*} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of k)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {B : ∀ i, QDivisor (X i)} {m : ℕ}

/-! ### Points of curves matched by an isomorphism of function fields -/

section Centre

/-- **The centre of a valuation on a scheme universally closed over `k`.** A valuation `ξ` of the
function field of an integral scheme `W`, universally closed over `k`, which is at most one on
`k`, dominates the local ring of some point of `W` (valuative criterion). -/
private theorem exists_center_of_universallyClosed {W : Scheme.{0}}
    [IsIntegral W] (sW : W ⟶ Spec (.of k)) [UniversallyClosed sW]
    (ξ : Valuation W.functionField ℤᵐ⁰)
    (hk : ∀ c : k, ξ (letI := functionFieldAlgebra sW; algebraMap k W.functionField c) ≤ 1) :
    ∃ x : W, (∀ a : W.presheaf.stalk x, ξ (algebraMap _ W.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk x),
        ξ (algebraMap _ W.functionField a) < 1 := by
  letI := functionFieldAlgebra sW
  let R := ξ.valuationSubring
  let φ : k →+* R := (algebraMap k W.functionField).codRestrict R
    fun c => (ξ.mem_valuationSubring_iff _).2 (hk c)
  have hex : ValuativeCriterion.Existence sW :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed sW) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) sW).1
  have hφ : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap R W.functionField) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ sW.appTop ≫
        W.presheaf.germ ⊤ (genericPoint W) trivial := rfl
  have hsq : W.fromSpecStalk (genericPoint W) ≫ sW =
      Spec.map (CommRingCat.ofHom (algebraMap R W.functionField)) ≫
        Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, hφ]
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
    rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv]
    simp [Scheme.ΓSpecIso_naturality]
    rfl
  let S : ValuativeCommSq sW :=
    { R := R
      K := W.functionField
      i₁ := W.fromSpecStalk (genericPoint W)
      i₂ := Spec.map (CommRingCat.ofHom φ)
      commSq := ⟨hsq⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R W.functionField)) ≫ l =
      W.fromSpecStalk (genericPoint W) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint W ⤳ x := (genericPoint_spec W).specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R W.functionField) =
      W.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (W.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : W.presheaf.stalk x,
      algebraMap _ W.functionField a = ((f.hom a : R) : W.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]
    exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

/-- The coheight of a point is at most the dimension of the scheme. -/
private theorem coheight_le_of_topologicalKrullDim_eq' {X : Scheme.{0}} {n : ℕ∞}
    (h : topologicalKrullDim X = n) (x : X) : Order.coheight x ≤ n := by
  have h2 : ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
    rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X]
    exact le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, h] at h2
  exact_mod_cast h2

/-- **Points of proper normal curves are matched by isomorphisms of function fields.** Let
`e : k(C') ≅ k(C)` be a `k`-isomorphism, `C'` a normal integral curve universally closed over `k`
and `Q` a prime divisor of the normal integral scheme `C`. Then `ord_Q ∘ e = ord_{Q'}` on nonzero
rational functions, for a prime divisor `Q'` of `C'`. -/
theorem exists_primeDivisor_ord_eq_of_curve {C C' : Scheme.{0}}
    {sC : C ⟶ Spec (.of k)} {sC' : C' ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C]
    [IsNormal C] [IsIntegral C'] [IsLocallyNoetherian C'] [IsNormal C'] [UniversallyClosed sC']
    (hdim' : topologicalKrullDim C' = 1) (e : FunctionFieldEquiv sC sC')
    (Q : MMP.Mori.PrimeDivisor C) :
    ∃ Q' : MMP.Mori.PrimeDivisor C', ∀ f, f ≠ 0 →
      C.ord ((e.toHom) f) Q.genericPoint = C'.ord f Q'.genericPoint := by
  letI := functionFieldAlgebra sC
  letI := functionFieldAlgebra sC'
  set ξ : Valuation C'.functionField ℤᵐ⁰ := Q.divisorialValuation.comap e.toHom.toRingHom
    with hξdef
  have hξ : ∀ f, ξ f = Q.divisorialValuation ((e.toHom) f) := fun f => rfl
  have hk : ∀ c : k, ξ (algebraMap k C'.functionField c) ≤ 1 := by
    intro c
    rw [hξ, AlgHom.commutes]
    letI := stalkAlgebra sC Q.genericPoint
    haveI := isScalarTower_stalk_functionField sC Q.genericPoint
    rw [IsScalarTower.algebraMap_apply k (C.presheaf.stalk Q.genericPoint) C.functionField]
    exact (Q.divisorialValuation_le_one_iff _).2 ⟨_, rfl⟩
  obtain ⟨x, hle, hlt⟩ := exists_center_of_universallyClosed sC' ξ hk
  -- a uniformizer of `Q`, pulled back to `k(C')`
  have := Q.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Q.localRing
  have hg : Q.divisorialValuation (algebraMap Q.localRing C.functionField ϖ) =
      WithZero.exp (-1) := Q.divisorialValuation_algebraMap_of_irreducible hϖ
  set h₀ : C'.functionField := e.symm (algebraMap Q.localRing C.functionField ϖ) with hh₀
  have hξh₀ : ξ h₀ = WithZero.exp (-1) := by
    rw [hξ, hh₀]
    change Q.divisorialValuation (e (e.symm _)) = _
    rw [AlgEquiv.apply_symm_apply, hg]
  -- the centre is not the generic point
  have hx : x ≠ genericPoint C' := by
    rintro rfl
    letI : Algebra (C'.presheaf.stalk (genericPoint C')) C'.functionField :=
      AlgebraicGeometry.stalkFunctionFieldAlgebra C' (genericPoint C')
    obtain ⟨a, ha⟩ : ∃ a : C'.presheaf.stalk (genericPoint C'),
        algebraMap (C'.presheaf.stalk (genericPoint C')) C'.functionField a = h₀⁻¹ :=
      (IsFractionRing.surjective_iff_isField (R := C'.presheaf.stalk (genericPoint C'))
        (K := C'.functionField)).2 (Field.toIsField C'.functionField) h₀⁻¹
    have h1 : ξ h₀⁻¹ ≤ 1 := (congrArg ξ ha).symm.trans_le (hle a)
    rw [map_inv₀, hξh₀, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h1
    exact absurd h1 (by norm_num)
  have hcoh : Order.coheight x = 1 := by
    have hle1 : Order.coheight x ≤ 1 := by
      exact_mod_cast coheight_le_of_topologicalKrullDim_eq' (n := 1) (by rw [hdim']; rfl) x
    have h0 : Order.coheight x ≠ 0 := by
      intro h0
      have hmax := Order.coheight_eq_zero.1 h0
      have h1 : genericPoint C' ⤳ x := (genericPoint_spec C').specializes trivial
      have h2 : x ⤳ genericPoint C' := hmax h1
      exact hx (h2.antisymm h1).eq
    exact le_antisymm hle1 (Order.one_le_iff_ne_zero.2 h0)
  obtain ⟨Q', hQ'⟩ : ∃ Q' : MMP.Mori.PrimeDivisor C', Q'.genericPoint = x :=
    ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hcoh,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hcoh⟩
  subst hQ'
  refine ⟨Q', ?_⟩
  set ν := Q'.divisorialValuation
  have hA : ∀ f, ν f ≤ 1 → ξ f ≤ 1 := by
    intro f hf
    obtain ⟨r, rfl⟩ := (Q'.divisorialValuation_le_one_iff f).1 hf
    exact hle r
  have hB : ∀ f, ν f < 1 → ξ f < 1 := by
    intro f hf
    obtain ⟨r, rfl⟩ := (Q'.divisorialValuation_le_one_iff f).1 hf.le
    exact hlt r ((Q'.divisorialValuation_algebraMap_lt_one_iff r).1 hf)
  have hC : ∀ f, f ≠ 0 → ν f = 1 → ξ f = 1 := by
    intro f hf0 hf
    refine le_antisymm (hA f hf.le) ((ξ.one_le_val_iff hf0).mpr (hA f⁻¹ ?_))
    rw [map_inv₀, hf, inv_one]
  -- a uniformizer of `Q'`
  have := Q'.isDiscreteValuationRing_localRing
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible Q'.localRing
  set p : C'.functionField := algebraMap Q'.localRing C'.functionField ϖ'
  have hp : ν p = WithZero.exp (-1) := Q'.divisorialValuation_algebraMap_of_irreducible hϖ'
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  have hνf : ∀ f, f ≠ 0 → ν f = ν p ^ (C'.ord f Q'.genericPoint) := by
    intro f hf
    rw [hp, Q'.divisorialValuation_eq_exp_neg_ord hf, ← WithZero.exp_zsmul]
    congr 1
    simp
  have hξf : ∀ f, f ≠ 0 → ξ f = ξ p ^ (C'.ord f Q'.genericPoint) := by
    intro f hf
    set n := C'.ord f Q'.genericPoint
    have hpn : p ^ (-n) ≠ 0 := zpow_ne_zero _ hp0
    have hu : ν (f * p ^ (-n)) = 1 := by
      rw [map_mul, map_zpow₀, hνf f hf, ← zpow_add₀ (by rw [hp]; exact WithZero.exp_ne_zero),
        add_neg_cancel, zpow_zero]
    have := hC _ (mul_ne_zero hf hpn) hu
    rwa [map_mul, map_zpow₀, zpow_neg,
      mul_inv_eq_one₀ (zpow_ne_zero _ fun h0 => hp0 ((map_eq_zero ξ).1 h0))] at this
  -- `ξ(p) = exp(-1)`
  have hp1 : ξ p = WithZero.exp (-1) := by
    have hep : (e.toHom) p ≠ 0 := (map_ne_zero_iff _ e.injective).2 hp0
    set c := C.ord ((e.toHom) p) Q.genericPoint
    have hξp : ξ p = WithZero.exp (-c) := by
      rw [hξ, Q.divisorialValuation_eq_exp_neg_ord hep]
    have hc0 : 0 < c := by
      have := hB p (by rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
      rw [hξp, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
      omega
    have hh0 : h₀ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hξh₀
      exact WithZero.exp_ne_zero hξh₀.symm
    have := hξf h₀ hh0
    rw [hξh₀, hξp, ← WithZero.exp_zsmul, WithZero.exp_inj, smul_eq_mul] at this
    have hc1 : c = 1 := by
      have hm : c * C'.ord h₀ Q'.genericPoint = 1 := by
        rw [mul_neg] at this
        linarith [mul_comm c (C'.ord h₀ Q'.genericPoint)]
      exact Int.eq_one_of_mul_eq_one_right hc0.le hm
    rw [hξp, hc1]
  intro f hf
  have hef : (e.toHom) f ≠ 0 := (map_ne_zero_iff _ e.injective).2 hf
  have h1 : ξ f = ν f := by rw [hξf f hf, hνf f hf, hp1, hp]
  rwa [hξ, Q.divisorialValuation_eq_exp_neg_ord hef, Q'.divisorialValuation_eq_exp_neg_ord hf,
    WithZero.exp_inj, neg_inj] at h1

end Centre

/-! ### The coefficient comparison -/

open MMP.Fold06.LemMmpStratumDiscrepancyNondecreasing in
/-- **Matched points carry the same coefficient of the differents.** In the situation of
`exists_primeDivisor_coeff_eq_residue_of_isCrepantBirationalMap`, if `ord_Q ∘ σ_T = ord_{Q'}`
then `B_T(Q) = B_{T'}(Q')`. On a common log resolution `p : W ⟶ X_i`, `q : W ⟶ X_j` of `σ`, the
crepant boundaries `Θ` of `(X_i, B_i)` and of `(X_j, B_j)` coincide, since `σ` preserves log
discrepancies. The strict transform `Y` of `P` is the strict transform of `P'`, and adjunction
along `Y` makes `(Θ - Y)|_Y` the crepant boundary of both `(T, B_T)` and `(T', B_{T'})`; the
point of `Y` over `Q` lies over `Q'`, because `σ_T` is induced by `q^* = p^* ∘ σ`. -/
private theorem coeff_eq_of_ord_eq_of_isCrepantBirationalMap
    (R : ResidueRestriction sX B 2 m) {i j : I}
    (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T T' : Scheme.{0}} [IsIntegral T] [IsIntegral T'] {ι : T ⟶ X i} {ι' : T' ⟶ X j}
    {BT : QDivisor T} {BT' : QDivisor T'} (h : MMP.Mori.IsPair (sX i) (B i))
    (h' : MMP.Mori.IsPair (sX j) (B j))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT)
    (hι' : IsAdjunctionStep (𝟙 (X j) ≫ sX j) (B j) ι' BT')
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (P' : MMP.Mori.PrimeDivisor (X j)) (hP'g : ι' (genericPoint T') = P'.genericPoint)
    (hP' : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g))
    (ψ : (X j).presheaf.stalk (ι' (genericPoint T')) →+* (X i).presheaf.stalk (ι (genericPoint T)))
    (hψ : ∀ a, algebraMap _ (X i).functionField (ψ a) =
      (σ.toHom) (algebraMap _ (X j).functionField a))
    (σT : FunctionFieldEquiv ((ι ≫ 𝟙 (X i)) ≫ sX i) ((ι' ≫ 𝟙 (X j)) ≫ sX j))
    (hσT : ∀ a, (ι.stalkMap (genericPoint T)).hom (ψ a) =
      (σT.toHom) ((ι'.stalkMap (genericPoint T')).hom a))
    (hdim : topologicalKrullDim T = (1 : ℕ)) (hdim' : topologicalKrullDim T' = (1 : ℕ)) :
    haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isNormal_stratum
    haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
    haveI := (StratumAdjunctionData.step (.refl h') ι' BT' hι').isNormal_stratum
    haveI := (StratumAdjunctionData.step (.refl h') ι' BT' hι').isLocallyNoetherian_stratum
    ∀ (Q : MMP.Mori.PrimeDivisor T) (Q' : MMP.Mori.PrimeDivisor T'),
      (∀ f, f ≠ 0 → T.ord ((σT.toHom) f) Q.genericPoint = T'.ord f Q'.genericPoint) →
        BT.coeff Q = BT'.coeff Q' := by
  intro Q Q' hQQ'
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  haveI := hPi.isAlgClosed
  haveI := hPi.charZero
  have hXi : IsNormalVariety k (sX i) := hPi.isPair.isNormalVariety
  have hXj : IsNormalVariety k (sX j) := hPj.isPair.isNormalVariety
  haveI : LocallyOfFiniteType (sX i) := hXi.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  have hXip := (R.setting.isProjectiveVariety i).isProjective
  have hXjp := (R.setting.isProjectiveVariety j).isProjective
  haveI : IsProper (sX i) := isProper_of_isProjectiveMorphism (sX i) hXip
  haveI : IsProper (sX j) := isProper_of_isProjectiveMorphism (sX j) hXjp
  haveI : CompactSpace (X i) := QuasiCompact.compactSpace_of_compactSpace (sX i)
  haveI : CompactSpace (X j) := QuasiCompact.compactSpace_of_compactSpace (sX j)
  -- the adjunction steps, over `s_{X_i}` and `s_{X_j}`
  have hι0 := hι
  have hι0' := hι'
  rw [Category.id_comp] at hι0 hι0'
  obtain ⟨hTv, P₀, hP₀1, hP₀r, hιci, -, -, -, -, -, -, hTln, hTn, hTc, hTlft, -⟩ := id hι0
  obtain ⟨hT'v, P₀', -, hP₀r', hιci', -, -, -, -, -, -, hT'ln, hT'n, hT'c, hT'lft, -⟩ := id hι0'
  haveI := hιci
  haveI := hιci'
  haveI := hTln
  haveI := hTn
  haveI := hTc
  haveI := hTlft
  haveI := hT'ln
  haveI := hT'n
  haveI := hT'c
  haveI := hT'lft
  obtain rfl : P = P₀ := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hP.symm.trans (map_genericPoint_eq_of_range_eq ι P₀ hP₀r))
  obtain rfl : P' = P₀' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hP'g.symm.trans (map_genericPoint_eq_of_range_eq ι' P₀' hP₀r'))
  have hdi : topologicalKrullDim (X i) = ((1 : ℕ) : WithBot ℕ∞) + 1 := by
    rw [R.setting.topologicalKrullDim_eq i]
    norm_num
  have hdj : topologicalKrullDim (X j) = ((1 : ℕ) : WithBot ℕ∞) + 1 := by
    rw [R.setting.topologicalKrullDim_eq j]
    norm_num
  have hBi : MMP.Flips.IsBoundary (MMP.Mori.QDivisor.toRDivisor (B i)) := fun E => by
    rw [MMP.Mori.QDivisor.coeff_toRDivisor]
    exact ⟨by exact_mod_cast hPi.nonneg E, by exact_mod_cast (R.setting.isDltPair i).2.1 E⟩
  have hBj : MMP.Flips.IsBoundary (MMP.Mori.QDivisor.toRDivisor (B j)) := fun E => by
    rw [MMP.Mori.QDivisor.coeff_toRDivisor]
    exact ⟨by exact_mod_cast hPj.nonneg E, by exact_mod_cast (R.setting.isDltPair j).2.1 E⟩
  /- Step 1: the birational map `X_i ⇢ X_j` with pull-back `σ`, and a common log resolution. -/
  obtain ⟨U, _, j₁, j₂, _, _, _, _, hj₁₂, hσj⟩ :=
    exists_isOpenImmersion_functionFieldMap_eq_of_functionFieldEquiv σ
  let φ : (X i).PartialIso (X j) :=
    { source := j₁.opensRange
      dense_source := j₁.opensRange.isOpen.dense ⟨_, ⟨genericPoint U, rfl⟩⟩
      target := j₂.opensRange
      dense_target := j₂.opensRange.isOpen.dense ⟨_, ⟨genericPoint U, rfl⟩⟩
      iso := j₁.isoOpensRange.symm ≪≫ j₂.isoOpensRange }
  have hφι : φ.iso.hom ≫ φ.target.ι = j₁.isoOpensRange.inv ≫ j₂ := by
    change (j₁.isoOpensRange.inv ≫ j₂.isoOpensRange.hom) ≫ j₂.opensRange.ι = _
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  have hsrc : j₁.isoOpensRange.inv ≫ j₁ = φ.source.ι :=
    (Iso.inv_comp_eq _).mpr (Scheme.Hom.isoOpensRange_hom_ι j₁).symm
  have hφ : φ.IsOver (sX i) (sX j) := by
    change φ.iso.hom ≫ φ.target.ι ≫ sX j = φ.source.ι ≫ sX i
    rw [← Category.assoc, hφι, Category.assoc, hj₁₂, ← Category.assoc, hsrc]
  have hbot : ∀ (Z : Scheme.{0}), IsEmpty (⊥ : Z.Opens).toScheme :=
    fun Z => ⟨fun x => by simpa using x.2⟩
  have hsm0 : ∀ (Z : Scheme.{0}) (s : Z ⟶ Spec (.of k)), IsSmoothScheme ((⊥ : Z.Opens).ι ≫ s) := by
    intro Z s
    haveI := hbot Z
    change smoothLocus _ = ⊤
    ext x
    exact isEmptyElim x
  have hsnc0 : ∀ (Z : Scheme.{0}) (s : Z ⟶ Spec (.of k)) (S : Closeds (⊥ : Z.Opens).toScheme),
      IsSNCSubset ((⊥ : Z.Opens).ι ≫ s) S := by
    intro Z s S
    haveI := hbot Z
    exact Or.inl (Closeds.ext (Set.ext fun x => isEmptyElim x))
  obtain ⟨W, p, q, hpres, -, hqres, -, hcompat, -, -⟩ :=
    MMP.Flips.exists_isLogResolution_isIso_restrict_of_partialIso (sX i) (sX j) hXi hXj hXip hXjp
      (B i) (B j) hBi hBj φ hφ ⊥ ⊥ bot_le bot_le (by simp) (hsm0 _ _) (hsnc0 _ _ _)
      (hsnc0 _ _ _) (hsnc0 _ _ _)
  obtain ⟨-, hvarW, hsmW, hpP, hp, G, -, hGiff, hGsnc⟩ := hpres
  obtain ⟨-, hvarW', hsmW', hqP, hq, -⟩ := hqres
  haveI := hpP
  haveI := hqP
  haveI : IsIntegral W := hvarW.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sX i) := hvarW.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sX j) := hvarW'.toLocallyOfFiniteType
  obtain ⟨hWln, hWn⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsmW
  haveI := hWln
  haveI := hWn
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX i)
  have hWv : IsNormalVariety k (p ≫ sX i) := ⟨hvarW, hWn⟩
  have hWv' : IsNormalVariety k (q ≫ sX j) := ⟨hvarW', hWn⟩
  haveI : IsDominant p := hp.isDominant
  haveI : IsDominant q := hq.isDominant
  /- Step 2: `q^* = p^* ∘ σ` on function fields, and `p ≫ s_{X_i} = q ≫ s_{X_j}`. -/
  set A := p ⁻¹ᵁ φ.source
  have hηA : genericPoint W ∈ A := by
    change p (genericPoint W) ∈ φ.source
    rw [MMP.Positivity.map_genericPoint_eq_of_isDominant p]
    obtain ⟨x, hx⟩ := φ.dense_source.nonempty
    exact ((genericPoint_spec (X i)).mem_open_set_iff φ.source.isOpen).mpr
      ⟨x, Set.mem_univ _, hx⟩
  haveI : Nonempty A := ⟨⟨_, hηA⟩⟩
  haveI : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
  haveI : IsDominant A.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion A.ι
  set b := (p ∣_ φ.source) ≫ j₁.isoOpensRange.inv with hb
  have hb₁ : b ≫ j₁ = A.ι ≫ p := by
    rw [hb, Category.assoc, hsrc, morphismRestrict_ι]
  have hb₂ : b ≫ j₂ = A.ι ≫ q := by
    rw [hb, Category.assoc, ← hφι, ← hcompat]
  haveI : IsDominant (b ≫ j₁) := by
    rw [hb₁]
    infer_instance
  haveI : IsDominant b := IsDominant.of_comp_of_isOpenImmersion b j₁
  have hfq : ∀ g, functionFieldMap q g = functionFieldMap p ((σ.toHom) g) := by
    intro g
    apply (functionFieldMap A.ι).injective
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      ← MMP.Positivity.DivisorOver.functionFieldMap_congr hb₂,
      ← MMP.Positivity.DivisorOver.functionFieldMap_congr hb₁,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply b j₂,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply b j₁, hσj]
  have hpq : p ≫ sX i = q ≫ sX j := by
    refine ext_of_isDominant A.ι ?_
    calc A.ι ≫ p ≫ sX i = (b ≫ j₁) ≫ sX i := by rw [hb₁, Category.assoc]
      _ = (b ≫ j₂) ≫ sX j := by simp only [Category.assoc, hj₁₂]
      _ = A.ι ≫ q ≫ sX j := by rw [hb₂, Category.assoc]
  /- Step 3: the crepant boundaries of `(X_i, B_i)` and `(X_j, B_j)` on `W` coincide. -/
  obtain ⟨-, n, K₀, hK₀, -⟩ := id hPi.isPair
  obtain ⟨-, n', K₀', hK₀', -⟩ := id hPj.isPair
  obtain ⟨⟨Θ, hΘ, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPi.isPair hK₀ p hWv hp
  obtain ⟨⟨Θ', hΘ', -⟩, -⟩ :=
    MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPj.isPair hK₀' q hWv' hq
  have hcr : ∀ (d : ℕ) (K : Divisor (X i)), K.IsCanonicalDivisor (sX i) d →
      IsCrepantBoundary (sX i) d K (B i) p hWv hp Θ := by
    intro d K hK
    obtain rfl : d = n := by
      have h1 := hK.topologicalKrullDim_eq
      rw [hK₀.topologicalKrullDim_eq] at h1
      exact_mod_cast h1.symm
    exact fun F => MMP.Spreading.isDiscrepancy_of_linearlyEquivalent (hΘ F)
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (sX i) hXi hK hK₀)
  have hcr' : ∀ (d : ℕ) (K : Divisor (X j)), K.IsCanonicalDivisor (sX j) d →
      IsCrepantBoundary (sX j) d K (B j) q hWv' hq Θ' := by
    intro d K hK
    obtain rfl : d = n' := by
      have h1 := hK.topologicalKrullDim_eq
      rw [hK₀'.topologicalKrullDim_eq] at h1
      exact_mod_cast h1.symm
    exact fun F => MMP.Spreading.isDiscrepancy_of_linearlyEquivalent (hΘ' F)
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (sX j) hXj hK hK₀')
  have hΘΘ' : Θ = Θ' := by
    ext F
    have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hΘ F)
      (show IsProper (⟨W, p, hWv, hp, F⟩ : DivisorOver k (sX i)).f from hpP)
    have h2 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hΘ' F)
      (show IsProper (⟨W, q, hWv', hq, F⟩ : DivisorOver k (sX j)).f from hqP)
    obtain ⟨n'', D'', hD'', h3⟩ := (hσ _ _).mp ⟨n, _, rfl, h1⟩
    have hv : D''.valuation = (⟨W, q, hWv', hq, F⟩ : DivisorOver k (sX j)).valuation := by
      rw [hD'']
      ext g
      change F.divisorialValuation (functionFieldMap p ((σ.toHom) g)) =
        F.divisorialValuation (functionFieldMap q g)
      rw [hfq]
    have h4 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h3 h2 hv
    have h5 : ((Θ.coeff F : ℚ) : ℝ) = ((Θ'.coeff F : ℚ) : ℝ) := by
      push_cast at h4
      linarith
    exact_mod_cast h5
  rw [← hΘΘ'] at hcr'
  /- Step 4: the strict transform `Pt` of `P` on `W` is the strict transform of `P'`. -/
  obtain ⟨t, hpt, hPb, hcoh⟩ := exists_map_eq_genericPoint_of_isBirationalMorphism p hp P
  set Pt : MMP.Mori.PrimeDivisor W := AlgebraicGeometry.PrimeDivisor.ofCoheightOne t hcoh
    with hPtdef
  have hPtg : Pt.genericPoint = t :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne t hcoh
  have hPtP : p Pt.genericPoint = P.genericPoint := by rw [hPtg, hpt]
  haveI : IsIso (p.stalkMap Pt.genericPoint) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus p (by rwa [hPtP])
  have hvq : (⟨W, q, hWv', hq, Pt⟩ : DivisorOver k (sX j)).valuation =
      (DivisorOver.ofPrimeDivisor k hXj P').valuation := by
    have h1 := valuation_eq_ofPrimeDivisor_of_mem_biregularLocus hXi ⟨W, p, hWv, hp, Pt⟩ P hPtP hPb
    ext g
    have h2 := congrArg (fun v : Valuation (X i).functionField ℤᵐ⁰ => v ((σ.toHom) g)) h1
    change Pt.divisorialValuation (functionFieldMap p _) =
      P.divisorialValuation (functionFieldMap (𝟙 (X i)) _) at h2
    change Pt.divisorialValuation (functionFieldMap q g) =
      P'.divisorialValuation (functionFieldMap (𝟙 (X j)) g)
    rw [functionFieldMap_id_apply] at h2
    rw [functionFieldMap_id_apply, hfq, hP', h2]
  have hqPt : q Pt.genericPoint = P'.genericPoint :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXj hvq
  have hqb : P'.genericPoint ∈ biregularLocus q :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal q hq
      P'.coheight_genericPoint.le
  haveI : IsIso (q.stalkMap Pt.genericPoint) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus q (by rwa [hqPt])
  have hqt : q t = P'.genericPoint := by rwa [← hPtg]
  /- Step 5: `Pt` is a component of the snc divisor of the log resolution, hence smooth. -/
  have hnotexc : Pt.genericPoint ∉ (MMP.Mori.exceptionalSet p : Set W) := fun hex =>
    (MMP.Mori.mem_exceptionalSet.mp hex) (by rwa [hPtP])
  have hGPt : G.coeff Pt = 1 := by
    refine (hGiff Pt).mpr (Or.inl ?_)
    refine (MMP.Flips.coeff_birationalInverseTransform_ne_zero_iff hXi _ hWv hp Pt hnotexc).mpr ?_
    rw [hPtP]
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, ?_, ?_⟩
    · rw [MMP.Mori.QDivisor.coeff_toRDivisor]
      have h0 : (B i).coeff P ≠ 0 := (by linarith : (0 : ℚ) < (B i).coeff P).ne'
      exact_mod_cast h0
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  have hGsnc' := MMP.Flips.IsSNCDivisor.isSNC hvarW hsmW hGsnc
  have hsnc1 : DivisorWithCoeffs.IsSNC (p ≫ sX i)
      (∑ G' ∈ ({Pt} : Finset (MMP.Mori.PrimeDivisor W)), Finsupp.single G' (1 : ℤ)) := by
    refine hGsnc'.of_support_subset fun G' hG' => ?_
    rw [Finset.sum_singleton, Finsupp.support_single_ne_zero _ one_ne_zero,
      Finset.mem_singleton] at hG'
    subst hG'
    rw [Finsupp.mem_support_iff]
    change G.coeff Pt ≠ 0
    rw [hGPt]
    exact one_ne_zero
  obtain ⟨-, hYsm, -⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC (p ≫ sX i) hsnc1
    (y := t) (fun G' hG' => by
      rw [Finset.mem_singleton.mp hG', ← hPtg, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl)
    (by rw [hcoh, Finset.card_singleton, Nat.cast_one])
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure t
  set Y := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {t})).subscheme
  set jW := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {t})).subschemeι with hjWdef
  obtain ⟨hYln, hYn⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYsm
  haveI := hYln
  haveI := hYn
  haveI : CompactSpace Y := jW.isClosedEmbedding.compactSpace
  have hYsm' : IsSmoothScheme (jW ≫ q ≫ sX j) := by rwa [← hpq]
  have hjg : jW (genericPoint Y) = t :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure t
  have hjWP : jW (genericPoint Y) = Pt.genericPoint := hjg.trans hPtg.symm
  have hPtr : Set.range jW = (Pt.support : Set W) := by
    rw [hjWdef, range_subschemeι_vanishingIdeal_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact congrArg (fun x => closure {x}) hPtg.symm
  /- Step 6: the strict transforms `Y ⟶ T` and `Y ⟶ T'`, and adjunction along `Y`. -/
  obtain ⟨pV, hsqV, hpVP, hpV⟩ := exists_strictTransform_of_isIso_stalkMap t p ι P hP₀r hpt
    (MMP.Positivity.DivisorOver.isIso_stalkMap_of_eq p hPtg.symm)
  obtain ⟨pV', hsqV', hpVP', hpV'⟩ := exists_strictTransform_of_isIso_stalkMap t q ι' P' hP₀r' hqt
    (MMP.Positivity.DivisorOver.isIso_stalkMap_of_eq q hPtg.symm)
  haveI := hpVP
  haveI := hpVP'
  haveI : IsDominant pV := hpV.isDominant
  haveI : IsDominant pV' := hpV'.isDominant
  have hsW : pV ≫ ι ≫ sX i = jW ≫ p ≫ sX i := by
    rw [← Category.assoc, hsqV, Category.assoc]
  have hsW' : pV' ≫ ι' ≫ sX j = jW ≫ q ≫ sX j := by
    rw [← Category.assoc, hsqV', Category.assoc]
  haveI := hvarW
  haveI := hvarW'
  have hYv : IsNormalVariety k (pV ≫ ι ≫ sX i) := ⟨by rw [hsW]; exact ⟨⟩, hYn⟩
  have hYv' : IsNormalVariety k (pV' ≫ ι' ≫ sX j) := ⟨by rw [hsW']; exact ⟨⟩, hYn⟩
  haveI : LocallyOfFiniteType (pV ≫ ι ≫ sX i) := hYv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (pV' ≫ ι' ≫ sX j) := hYv'.1.toLocallyOfFiniteType
  obtain ⟨hTp, -, hg, Rd, hRd, hcrR⟩ :=
    isCrepantBoundary_sub_single_of_isAdjunctionStep hPi.isPair p hWv hp hsmW hcr ι hι0 P hP₀r
      hdi hdim Nat.one_pos Pt hPtP jW hjWP hPtr hYsm pV hsqV hYv hpV
  obtain ⟨hT'p, -, hg', Rd', hRd', hcrR'⟩ :=
    isCrepantBoundary_sub_single_of_isAdjunctionStep hPj.isPair q hWv' hq hsmW' hcr' ι' hι0' P'
      hP₀r' hdj hdim' Nat.one_pos Pt hqPt jW hjWP hPtr hYsm' pV' hsqV' hYv' hpV'
  have hRR : Rd = Rd' :=
    ((MMP.Fourfold.isQCartier_of_isSmoothScheme hsmW _).existsUnique_isPullback hg).unique hRd hRd'
  subst hRR
  /- Step 7: `q^* = p^* ∘ σ` restricts to `p_{V'}^* = p_V^* ∘ σ_T` on `Y`. -/
  have hfV : ∀ f, functionFieldMap pV' f = functionFieldMap pV ((σT.toHom) f) := by
    intro f
    obtain ⟨a, rfl⟩ := ι'.stalkMap_surjective (genericPoint T') f
    rw [← hσT]
    have hpVg : pV (genericPoint Y) = genericPoint T :=
      MMP.Positivity.map_genericPoint_eq_of_isDominant pV
    have hpVg' : pV' (genericPoint Y) = genericPoint T' :=
      MMP.Positivity.map_genericPoint_eq_of_isDominant pV'
    have hzw : ι (genericPoint T) = p (jW (genericPoint Y)) := by rw [hjg, hpt, hP]
    have hzw' : ι' (genericPoint T') = q (jW (genericPoint Y)) := by rw [hjg, hqt, hP'g]
    have h1 := functionFieldMap_algebraMap_stalkMap_of_comp_eq pV ι jW p hsqV (genericPoint Y)
      hpVg hzw (ψ a)
    have h2 := functionFieldMap_algebraMap_stalkMap_of_comp_eq pV' ι' jW q hsqV' (genericPoint Y)
      hpVg' hzw' a
    rw [MMP.Resolution.algebraMap_stalk_genericPoint_apply] at h1 h2
    have hw : (q.stalkMap (jW (genericPoint Y))).hom
          (((X j).presheaf.stalkCongr (.of_eq hzw')).hom.hom a) =
        (p.stalkMap (jW (genericPoint Y))).hom
          (((X i).presheaf.stalkCongr (.of_eq hzw)).hom.hom (ψ a)) := by
      apply IsFractionRing.injective (W.presheaf.stalk (jW (genericPoint Y))) W.functionField
      rw [← functionFieldMap_algebraMap_stalk q, ← functionFieldMap_algebraMap_stalk p,
        algebraMap_stalkCongr_hom hzw', algebraMap_stalkCongr_hom hzw, hfq, hψ]
    rw [h2, h1, hw]
  /- Step 8: the point of `Y` over `Q` lies over `Q'`, and both coefficients are read on `Y`. -/
  obtain ⟨y₁, hy₁, hQb, hcoh₁⟩ := exists_map_eq_genericPoint_of_isBirationalMorphism pV hpV Q
  set Qt : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y₁ hcoh₁
    with hQtdef
  have hQtg : Qt.genericPoint = y₁ :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y₁ hcoh₁
  have hQtQ : pV Qt.genericPoint = Q.genericPoint := by rw [hQtg, hy₁]
  haveI : IsIso (pV.stalkMap Qt.genericPoint) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus pV (by rwa [hQtQ])
  have hD1 : (⟨Y, pV', hYv', hpV', Qt⟩ : DivisorOver k (ι' ≫ sX j)).valuation =
      (DivisorOver.ofPrimeDivisor k hT'v Q').valuation := by
    have h1 := valuation_eq_ofPrimeDivisor_of_mem_biregularLocus hTv ⟨Y, pV, hYv, hpV, Qt⟩ Q
      hQtQ hQb
    ext g
    have h2 := congrArg (fun v : Valuation T.functionField ℤᵐ⁰ => v ((σT.toHom) g)) h1
    change Qt.divisorialValuation (functionFieldMap pV _) =
      Q.divisorialValuation (functionFieldMap (𝟙 T) _) at h2
    change Qt.divisorialValuation (functionFieldMap pV' g) =
      Q'.divisorialValuation (functionFieldMap (𝟙 T') g)
    rw [functionFieldMap_id_apply] at h2
    rw [functionFieldMap_id_apply, hfV, h2]
    by_cases hg0 : g = 0
    · subst hg0
      simp
    · letI := functionFieldAlgebra ((ι ≫ 𝟙 (X i)) ≫ sX i)
      letI := functionFieldAlgebra ((ι' ≫ 𝟙 (X j)) ≫ sX j)
      have hσg : (σT.toHom) g ≠ 0 := (map_ne_zero_iff _ σT.injective).2 hg0
      rw [Q.divisorialValuation_eq_exp_neg_ord hσg, Q'.divisorialValuation_eq_exp_neg_ord hg0,
        hQQ' g hg0]
  have hy₁' : pV' Qt.genericPoint = Q'.genericPoint :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hT'v hD1
  have hQb' : Q'.genericPoint ∈ biregularLocus pV' :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal pV' hpV'
      Q'.coheight_genericPoint.le
  haveI : IsIso (pV'.stalkMap Qt.genericPoint) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus pV' (by rwa [hy₁'])
  have hc1 := coeff_eq_coeff_of_isCrepantBoundary hTp pV hYv hpV hcrR Qt Q hQtQ
  have hc2 := coeff_eq_coeff_of_isCrepantBoundary hT'p pV' hYv' hpV' hcrR' Qt Q' hy₁'
  exact hc1.symm.trans hc2

/-- **Crepant maps match the differents of matched floor curves.** Let `σ` be a crepant
birational map `(X_i, B_i) ⇢ (X_j, B_j)` carrying the valuation of the floor curve `P ⊆ X_i` to
that of the floor curve `P' ⊆ X_j`, `T ⟶ X_i` and `T' ⟶ X_j` the normal curves over `P` and `P'`
with their differents `B_T` and `B_{T'}`, and `σ_T : k(T') ≅ k(T)` the isomorphism of residue
fields induced by `σ`. Then `σ_T` matches every point `Q` of `T` with a point `Q'` of `T'`
(`ord_Q ∘ σ_T = ord_{Q'}`), and conversely, so that the coefficients of the differents agree:
`B_T(Q) = B_{T'}(Q')`. -/
theorem exists_primeDivisor_coeff_eq_residue_of_isCrepantBirationalMap
    (R : ResidueRestriction sX B 2 m) {i j : I}
    (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T T' : Scheme.{0}} [IsIntegral T] [IsIntegral T'] {ι : T ⟶ X i} {ι' : T' ⟶ X j}
    {BT : QDivisor T} {BT' : QDivisor T'} (h : MMP.Mori.IsPair (sX i) (B i))
    (h' : MMP.Mori.IsPair (sX j) (B j))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT)
    (hι' : IsAdjunctionStep (𝟙 (X j) ≫ sX j) (B j) ι' BT')
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (P' : MMP.Mori.PrimeDivisor (X j)) (hP'g : ι' (genericPoint T') = P'.genericPoint)
    (hP' : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g))
    (ψ : (X j).presheaf.stalk (ι' (genericPoint T')) →+* (X i).presheaf.stalk (ι (genericPoint T)))
    (hψ : ∀ a, algebraMap _ (X i).functionField (ψ a) =
      (σ.toHom) (algebraMap _ (X j).functionField a))
    (σT : FunctionFieldEquiv ((ι ≫ 𝟙 (X i)) ≫ sX i) ((ι' ≫ 𝟙 (X j)) ≫ sX j))
    (hσT : ∀ a, (ι.stalkMap (genericPoint T)).hom (ψ a) =
      (σT.toHom) ((ι'.stalkMap (genericPoint T')).hom a)) :
    haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isNormal_stratum
    haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
    haveI := (StratumAdjunctionData.step (.refl h') ι' BT' hι').isNormal_stratum
    haveI := (StratumAdjunctionData.step (.refl h') ι' BT' hι').isLocallyNoetherian_stratum
    (∀ Q : MMP.Mori.PrimeDivisor T, ∃ Q' : MMP.Mori.PrimeDivisor T',
      (∀ f, f ≠ 0 → T.ord ((σT.toHom) f) Q.genericPoint = T'.ord f Q'.genericPoint) ∧
        BT.coeff Q = BT'.coeff Q') ∧
    (∀ Q' : MMP.Mori.PrimeDivisor T', ∃ Q : MMP.Mori.PrimeDivisor T,
      (∀ f, f ≠ 0 → T.ord ((σT.toHom) f) Q.genericPoint = T'.ord f Q'.genericPoint) ∧
        BT.coeff Q = BT'.coeff Q') := by
  have hPi := R.setting.isPair i
  haveI := hPi.charZero
  set F := StratumAdjunctionData.step (.refl h) ι BT hι with hF
  set F' := StratumAdjunctionData.step (.refl h') ι' BT' hι' with hF'
  haveI := F.isNormal_stratum
  haveI := F.isLocallyNoetherian_stratum
  haveI := F'.isNormal_stratum
  haveI := F'.isLocallyNoetherian_stratum
  have hvar : IsNormalVariety k ((ι ≫ 𝟙 (X i)) ≫ sX i) := F.isNormalVariety
  have hvar' : IsNormalVariety k ((ι' ≫ 𝟙 (X j)) ≫ sX j) := F'.isNormalVariety
  haveI : LocallyOfFiniteType ((ι ≫ 𝟙 (X i)) ≫ sX i) := hvar.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType ((ι' ≫ 𝟙 (X j)) ≫ sX j) := hvar'.1.toLocallyOfFiniteType
  have hdim : topologicalKrullDim T = (1 : ℕ) := by
    have hT := topologicalKrullDim_eq_toNat_trdeg ((ι ≫ 𝟙 (X i)) ≫ sX i)
    have hdl := StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq i) F hT
    simp only [hF, StratumAdjunctionData.length] at hdl
    rw [hT]
    exact_mod_cast (by omega : _ = 1)
  have hdim' : topologicalKrullDim T' = (1 : ℕ) := by
    have hT := topologicalKrullDim_eq_toNat_trdeg ((ι' ≫ 𝟙 (X j)) ≫ sX j)
    have hdl := StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq j) F' hT
    simp only [hF', StratumAdjunctionData.length] at hdl
    rw [hT]
    exact_mod_cast (by omega : _ = 1)
  -- the floor curves are proper over `k`
  haveI : IsProper (sX i) :=
    isProper_of_isProjectiveMorphism (sX i) (R.setting.isProjectiveVariety i).isProjective
  haveI : IsProper (sX j) :=
    isProper_of_isProjectiveMorphism (sX j) (R.setting.isProjectiveVariety j).isProjective
  obtain ⟨-, -, -, -, hci, -⟩ := id hι
  obtain ⟨-, -, -, -, hci', -⟩ := id hι'
  haveI : UniversallyClosed ((ι ≫ 𝟙 (X i)) ≫ sX i) := inferInstance
  haveI : UniversallyClosed ((ι' ≫ 𝟙 (X j)) ≫ sX j) := inferInstance
  have hcoeff := coeff_eq_of_ord_eq_of_isCrepantBirationalMap R σ hσ h h' hι hι' P hP P' hP'g
    hP' ψ hψ σT hσT hdim hdim'
  letI := functionFieldAlgebra ((ι ≫ 𝟙 (X i)) ≫ sX i)
  letI := functionFieldAlgebra ((ι' ≫ 𝟙 (X j)) ≫ sX j)
  refine ⟨fun Q => ?_, fun Q' => ?_⟩
  · obtain ⟨Q', hQ'⟩ := exists_primeDivisor_ord_eq_of_curve (by exact_mod_cast hdim') σT Q
    exact ⟨Q', hQ', hcoeff Q Q' hQ'⟩
  · obtain ⟨Q, hQ⟩ := exists_primeDivisor_ord_eq_of_curve (by exact_mod_cast hdim) σT.symm Q'
    have hQ'' : ∀ f, f ≠ 0 → T.ord ((σT.toHom) f) Q.genericPoint = T'.ord f Q'.genericPoint := by
      intro f hf
      have hσf : (σT.toHom) f ≠ 0 := (map_ne_zero_iff _ σT.injective).2 hf
      have := hQ ((σT.toHom) f) hσf
      change T'.ord (σT.symm (σT f)) Q'.genericPoint = _ at this
      rw [AlgEquiv.symm_apply_apply] at this
      exact this.symm
    exact ⟨Q, hQ'', hcoeff Q Q' hQ''⟩

end MMP.Fourfold
