module
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
import MMP.AlgebraicGeometry.Singularities.DivisorialValuationFiniteRestriction
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.Etale
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.EtaleStalkOrder
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion

/-!
# The variety of a local étale datum is terminal

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`) and
`(Y_e, q, η', L̃_1, …, L̃_b)` a local étale datum (`MMP.Fourfold.LocalEtaleDatum`). Then for
every canonical divisor `K_Y` of `Y`, the divisor `K_Y` is `ℚ`-Cartier and its pull-back
`q^* K_Y` along the étale morphism `q : Y_e ⟶ Y` is a `ℚ`-Cartier canonical divisor of `Y_e`;
moreover `Y_e` is terminal.

Since `Y` is terminal and `ℚ`-factorial, `K_Y` is `ℚ`-Cartier. Along an étale morphism
`f : Y ⟶ X` of normal integral schemes, a point `y` of codimension one lies over a point of
codimension one, the maximal ideal of `𝒪_{X, f y}` generates that of `𝒪_{Y, y}`, and
`Ω_{𝒪_{X, f y}/k}` generates `Ω_{𝒪_{Y, y}/k}`. Hence orders of rational functions and of rational
pluricanonical forms along prime divisors are preserved by the pull-back `f^*`. Applied to `q`,
this shows that `q^* K_Y = div(q^* ω)` for `K_Y = div(ω)`, and that local generators of
`𝒪_Y(m K_Y)` pull back to local generators of `𝒪_{Y_e}(m q^* K_Y)`.

For a divisor `(Y', g, E)` over `Y_e` with `g` proper, the restriction of `ord_E` to `ℂ(Y)` is
a power of a normalized divisorial valuation `ord_F`, `F` a prime divisor on a proper model
`μ : W ⟶ Y`; on the base change `W_e = W ×_Y Y_e` there is a prime divisor `F'` over `F` with
`ord_{F'} = ord_E`. Comparing the Kollár–Mori discrepancies of `F` over `Y` and of `F'` over `Y_e`
through the étale projection `W_e ⟶ W` shows `a(E; Y_e, 0) = a(F; Y, 0)`, and `E` is exceptional
over `Y_e` exactly when `F` is exceptional over `Y`, since `q` preserves codimensions. So
terminality of `Y` passes to `Y_e`.

## Main results

* `MMP.Fourfold.LocalEtaleDatum.exists_isCanonicalDivisor_isPullback_and_isTerminalVariety`:
  `K_{Y_e} = q^* K_Y` is `ℚ`-Cartier and `Y_e` is terminal.
* `MMP.Mori.PrimeDivisor.exists_genericPoint_eq_of_etale`: along an étale morphism, the generic
  point of a prime divisor lies over the generic point of a prime divisor.
* `MMP.Mori.Divisor.IsPullback.coeff_eq_of_etale`: the coefficient of `f^* B` along `E` is that
  of `B` along the prime divisor under `E`.
* `MMP.Mori.Divisor.exists_isCanonicalDivisor_isPullback_of_etale`: the pull-back of a
  `ℚ`-Cartier canonical divisor along an étale morphism is a `ℚ`-Cartier canonical divisor.

## Implementation notes

* `Y_e` lies over `ℂ` through `q ≫ s_Y`. Terminality is `MMP.Fourfold.IsTerminalVariety`, which
  includes that `K_{Y_e}` is `ℚ`-Cartier.
* The pull-back of the `ℚ`-Cartier divisor `K_Y` is `MMP.Mori.QDivisor.IsPullback`; it is defined
  when `q` maps the generic point of `Y_e` outside `Supp K_Y`, which holds since `q` is étale,
  hence open, and is part of the conclusion.
* The instance hypotheses on `Y_e` (integral, locally Noetherian, normal), needed to speak of its
  divisors, follow from the fields of `MMP.Fourfold.LocalEtaleDatum`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.25, 5.20
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Fourfold.LocalEtaleDatum

open MMP.Mori IsLocalRing

/-! ### Orders of rational functions and forms along an étale morphism -/

section Order

/-- Along a local homomorphism of discrete valuation rings with `𝔪_R R' = 𝔪_{R'}`, the order of
vanishing is preserved: a uniformizer maps to a uniformizer. -/
private theorem ordFrac_map_eq {R R' K K' : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K'] [IsFractionRing R' K']
    (φ : R →+* R') (hφ : (maximalIdeal R).map φ = maximalIdeal R') (ψ : K →+* K')
    (hψ : ∀ a, ψ (algebraMap R K a) = algebraMap R' K' (φ a)) (x : K) :
    Ring.ordFrac R' (ψ x) = Ring.ordFrac R x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ' : Irreducible (φ ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hφ,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have key : ∀ a : R, a ≠ 0 → Ring.ordFrac R' (algebraMap R' K' (φ a)) =
      Ring.ordFrac R (algebraMap R K a) := by
    intro a ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    simp only [map_mul, map_pow, Ring.ordFrac_irreducible hϖ, Ring.ordFrac_irreducible hϖ',
      Ring.ordFrac_of_isUnit (u.isUnit), Ring.ordFrac_of_isUnit (u.isUnit.map φ)]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  by_cases ha : a = 0
  · simp [ha]
  rw [map_div₀, map_div₀, map_div₀, hψ, hψ, key a ha, key b (nonZeroDivisors.ne_zero hb)]

/-- The local ring at a point of codimension one of a normal locally Noetherian integral scheme is
a discrete valuation ring. -/
private theorem isDiscreteValuationRing_stalk_of_coheight {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {z : X} (hz : Order.coheight z = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk z) := by
  have h5 : IsNoetherianRing (X.presheaf.stalk z) ∧ IsLocalRing (X.presheaf.stalk z) ∧
      IsDomain (X.presheaf.stalk z) ∧ IsIntegrallyClosed (X.presheaf.stalk z) ∧
      ringKrullDim (X.presheaf.stalk z) = 1 :=
    ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal z, by
      rw [ringKrullDim_stalk_eq_coheight, hz]; rfl⟩
  obtain ⟨_, h⟩ := ((isDiscreteValuationRing_tfae (X.presheaf.stalk z)).out 5 1).mp h5
  exact h

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Orders of rational functions are preserved by an étale morphism** at a point `y` of
codimension one: `v_y(f^* g) = v_{f y}(g)`. -/
private theorem ord_functionFieldMap_of_etale (f : Y ⟶ X) [Etale f] [IsDominant f] {y : Y}
    (hy : Order.coheight y = 1) (g : X.functionField) :
    Y.ord (functionFieldMap f g) y = X.ord g (f y) := by
  by_cases hg : g = 0
  · simp [hg]
  have hfy : Order.coheight (f y) = 1 := (coheight_eq_of_etale f y).trans hy
  have := isDiscreteValuationRing_stalk_of_coheight hy
  have := isDiscreteValuationRing_stalk_of_coheight hfy
  have h := ordFrac_map_eq (K := X.functionField) (K' := Y.functionField) (f.stalkMap y).hom
    (map_maximalIdeal_stalkMap_of_etale f y) (functionFieldMap f)
    (MMP.Mori.functionFieldMap_algebraMap_stalk f y) g
  rw [Scheme.ord_eq_iff hy ((map_ne_zero _).mpr hg), Scheme.ordHom]
  have h2 := (Scheme.ord_eq_iff hfy hg (n := X.ord g (f y))).mp rfl
  rw [Scheme.ordHom] at h2
  exact h.trans h2

end Order

/-! ### Top forms along a formally unramified homomorphism -/

section TopForms

variable {k A A' : Type*} [CommRing k] [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
  [Algebra A A'] [IsScalarTower k A A']

/-- For a formally unramified `A → A'`, the image of `Ω_{A/k}` spans `Ω_{A'/k}` over `A'`. -/
private theorem span_range_kaehlerDifferential_map_eq_top [Algebra.FormallyUnramified A A'] :
    Submodule.span A' (Set.range (KaehlerDifferential.map k k A A')) = ⊤ := by
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange k A A') := by
    rw [← LinearMap.range_eq_top, KaehlerDifferential.range_mapBaseChange]
    exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hsurj (KaehlerDifferential.D k A' x)
  rw [← hy]
  clear hy
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a ω =>
    rw [KaehlerDifferential.mapBaseChange_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ω, rfl⟩)
  | add y z hy hz =>
    rw [map_add]
    exact add_mem hy hz

/-- For a formally unramified `A → A'`, the image of a generator of `Ω^d_{A/k}` generates
`Ω^d_{A'/k}`. -/
private theorem span_singleton_topFormsMap_eq_top [Algebra.FormallyUnramified A A'] {d : ℕ}
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤) :
    Submodule.span A' {topFormsMap k A A' d σ} = ⊤ := by
  rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span A' d _
    (span_range_kaehlerDifferential_map_eq_top (k := k) (A := A)), Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  choose b hb using fun i => ha ⟨i, rfl⟩
  have hab : a = fun i => KaehlerDifferential.map k k A A' (b i) := funext fun i => (hb i).symm
  subst hab
  rw [← topFormsMap_ιMulti]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top
    (x := exteriorPower.ιMulti A d b))
  rw [← hc, map_smul, ← algebraMap_smul A' c]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end TopForms

/-! ### The order of a pulled-back form along an unramified extension of local rings -/

section Transport

variable {k : Type*} [CommRing k] {d : ℕ} {m : ℤ}
  {K K' : Type*} [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K']
  [IsScalarTower k K K']
  {A A' : Type*} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [Algebra A K]
  [IsScalarTower k A K] [IsFractionRing A K] [Algebra A' K'] [IsScalarTower k A' K']
  [IsFractionRing A' K'] [Algebra A A'] [IsScalarTower k A A'] [Algebra A K']
  [IsScalarTower A A' K'] [IsScalarTower A K K'] [IsScalarTower k A K']

/-- Let `A → A'` be a homomorphism of local rings with fraction fields `K → K'`, carrying a
generator `σ` of `Ω^d_{A/k}` to a generator of `Ω^d_{A'/k}`, and `v, v'` orders on `K, K'` with
`v' ∘ (K → K') = v`. Then the order of the pull-back of an `m`-canonical form is its order:
`ord_{A'}(u^* τ) = ord_A(τ)`. -/
private theorem ordAt_pullbackForms_eq_of_span {σ : ⋀[A]^d Ω[A⁄k]}
    (hσ : Submodule.span A {σ} = ⊤) (hσ' : Submodule.span A' {topFormsMap k A A' d σ} = ⊤)
    {v : K → ℤ} {v' : K' → ℤ}
    (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (hmul' : ∀ x y : K', x ≠ 0 → y ≠ 0 → v' (x * y) = v' x + v' y)
    (hunit' : ∀ a : A', IsUnit a → v' (algebraMap A' K' a) = 0)
    (hvv : ∀ x, v' (algebraMap K K' x) = v x)
    (hω : IsPullbackGenerator K' (topFormsMap k A K d σ)) (τ : PluriForms k K d m) :
    ordAt A' v' (pullbackForms (K' := K') m τ) = ordAt A v τ := by
  have h0 : topFormsMap k A K d σ ≠ 0 := hω.ne_zero
  have h0'' : topFormsMap k A' K' d (topFormsMap k A A' d σ) ≠ 0 := by
    rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp,
      ← MMP.Threefold.Mori.Helpers.topFormsMap_comp (B := K) (C := K')]
    exact hω.2.2
  rw [ordAt_eq hmul' hunit' hσ' h0'', ordAt_eq hmul hunit hσ h0, pullbackForms_eq hω]
  have hb1 : topFormsBasis A' hσ' h0'' () =
      (1 : K') • basisOfSpanSingleton hω.2.1 hω.2.2 () := by
    rw [topFormsBasis_apply, basisOfSpanSingleton_apply, one_smul,
      MMP.Threefold.Mori.Helpers.topFormsMap_comp,
      ← MMP.Threefold.Mori.Helpers.topFormsMap_comp (B := K) (C := K')]
  have hb2 : topFormsBasis A hσ h0 () = (1 : K) • basisOfSpanSingleton hω.1 hω.ne_zero () := by
    simp
  have hbas : ZTensorPower.basis (topFormsBasis A' hσ' h0'') m () =
      ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m () := by
    rw [ZTensorPower.basis_apply_of_eq_smul hb1, one_zpow, one_smul]
  have : formCoeff A' hσ' h0'' (pullbackFormsAlong hω m τ) =
      algebraMap K K' (formCoeff A hσ h0 τ) := by
    unfold formCoeff pullbackFormsAlong
    rw [← hbas, ZTensorPower.basis_repr_of_eq_smul hb2]
    simp [Algebra.smul_def]
  rw [this, hvv]

end Transport

/-! ### Orders of pulled-back forms along an étale morphism -/

section FormOrder

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sX : X ⟶ Spec (.of k)}

/-- **The order of a pulled-back form along an étale morphism.** Let `f : Y ⟶ X` be an étale
morphism of normal integral varieties of the same dimension `d` over a field of characteristic
zero, and `E ⊆ Y`, `P ⊆ X` prime divisors with `f(η_E) = η_P`. Then
`ord_E(f^* τ) = ord_P(τ)` for every rational `m`-canonical form `τ` on `X`. -/
private theorem ordForm_pullbackRationalPluriForms_of_etale [LocallyOfFiniteType sX]
    (f : Y ⟶ X) [Etale f] [IsDominant f] {d : ℕ} (hX : topologicalKrullDim X = d)
    (hY : topologicalKrullDim Y = d) (E : MMP.Mori.PrimeDivisor Y) (P : MMP.Mori.PrimeDivisor X)
    (heq : f E.genericPoint = P.genericPoint) {m : ℤ} (τ : RationalPluriForms sX d m) :
    E.ordForm (pullbackRationalPluriForms sX f τ) = P.ordForm τ := by
  have : LocallyOfFiniteType (f ≫ sX) := inferInstance
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hX
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  let := stalkAlgebra sX P.genericPoint
  have := isScalarTower_stalk_functionField sX P.genericPoint
  let := stalkAlgebra (f ≫ sX) E.genericPoint
  have := isScalarTower_stalk_functionField (f ≫ sX) E.genericPoint
  have hsp : f E.genericPoint ⤳ P.genericPoint := heq ▸ specializes_rfl
  let φ : X.presheaf.stalk P.genericPoint ⟶ Y.presheaf.stalk E.genericPoint :=
    X.presheaf.stalkSpecializes hsp ≫ f.stalkMap E.genericPoint
  have hφiso : IsIso (X.presheaf.stalkSpecializes hsp) := by
    rw [show X.presheaf.stalkSpecializes hsp =
      (X.presheaf.stalkCongr (Inseparable.of_eq heq)).inv from rfl]
    infer_instance
  let : Algebra P.localRing E.localRing := φ.hom.toAlgebra
  let : Algebra P.localRing Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap P.localRing X.functionField)).toAlgebra
  have : IsScalarTower P.localRing X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hφK : ∀ r : P.localRing, algebraMap P.localRing Y.functionField r =
      algebraMap E.localRing Y.functionField (φ.hom r) := fun r => by
    change functionFieldMap f _ = algebraMap _ Y.functionField ((f.stalkMap E.genericPoint).hom
        ((X.presheaf.stalkSpecializes hsp).hom r))
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, MMP.Mori.algebraMap_stalkSpecializes]
  have : IsScalarTower P.localRing E.localRing Y.functionField :=
    IsScalarTower.of_algebraMap_eq hφK
  have : IsScalarTower k P.localRing E.localRing := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫
          Y.presheaf.germ ⊤ E.genericPoint (Opens.mem_top _) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
          X.presheaf.germ ⊤ P.genericPoint (Opens.mem_top _)) ≫ φ := by
      simp only [φ, Scheme.Hom.comp_appTop, Category.assoc,
        TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
      rfl
    exact congrArg CommRingCat.Hom.hom h
  have : IsScalarTower k P.localRing Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [IsScalarTower.algebraMap_apply k X.functionField Y.functionField,
      IsScalarTower.algebraMap_apply k P.localRing X.functionField]
    rfl
  have hunr : Algebra.FormallyUnramified P.localRing E.localRing := by
    have h1 : (f.stalkMap E.genericPoint).hom.FormallyUnramified :=
      FormallyUnramified.stalkMap f E.genericPoint
    have h2 : (X.presheaf.stalkSpecializes hsp).hom.FormallyUnramified :=
      RingHom.FormallyUnramified.of_surjective
        (ConcreteCategory.bijective_of_isIso (X.presheaf.stalkSpecializes hsp)).2
    exact h2.comp h1
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨σ, hσ, h0⟩ := P.exists_topForms_generator hd
  have hspan : Submodule.span X.functionField {topFormsMap k P.localRing X.functionField d σ} =
      ⊤ := span_singleton_topFormsMap (nonZeroDivisors P.localRing) hσ
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq sX f hX hY
  have hgen := MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω hspan h0
  have hord : ∀ x : X.functionField, Y.ord (algebraMap X.functionField Y.functionField x)
      E.genericPoint = X.ord x P.genericPoint := fun x => by
    rw [← heq]
    exact ord_functionFieldMap_of_etale f E.coheight_genericPoint x
  exact ordAt_pullbackForms_eq_of_span (k := k) hσ (span_singleton_topFormsMap_eq_top hσ)
    P.ord_mul_of_ne_zero (fun _ ha => P.ord_algebraMap_of_isUnit ha)
    E.ord_mul_of_ne_zero (fun _ ha => E.ord_algebraMap_of_isUnit ha) hord hgen τ

end FormOrder

/-! ### Pull-back of Cartier divisors along an étale morphism -/

section DivisorPullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [Etale f] [IsDominant f]

/-- The generic point of a prime divisor of `Y` lies over the generic point of a prime divisor of
`X`, `f` being étale. -/
theorem _root_.MMP.Mori.PrimeDivisor.exists_genericPoint_eq_of_etale (E : MMP.Mori.PrimeDivisor Y) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.genericPoint = f E.genericPoint :=
  ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _
      ((coheight_eq_of_etale f _).trans E.coheight_genericPoint),
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _⟩

/-- **Coefficients of the pull-back along an étale morphism.** The coefficient of `f^* B` along a
prime divisor `E` is the coefficient of `B` along the prime divisor `P` with `η_P = f(η_E)`. -/
theorem _root_.MMP.Mori.Divisor.IsPullback.coeff_eq_of_etale {B : Divisor X} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp}
    {B' : Divisor Y} (h : B.IsPullback f hB B') (E : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X)
    (hP : P.genericPoint = f E.genericPoint) : B'.coeff E = B.coeff P := by
  obtain ⟨U, hU, φ, hφ⟩ := hBc (f E.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ E hU P.component,
    ord_functionFieldMap_of_etale f E.coheight_genericPoint, hφ P ((P.genericPoint_mem_iff U).mp
      (hP ▸ hU)), MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hP]

end DivisorPullback

/-! ### Existence of canonical divisors on normal varieties -/

section CanonicalDivisorExistence

open Opposite TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an irreducible scheme is dense. -/
private theorem isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (V : Y.Opens)
    [Nonempty V] : IsDominant V.ι :=
  Opens.isDominant_ι (V.isOpen.dense ⟨_, (Classical.arbitrary V).2⟩)

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_stalkSpecializes_apply {Y : Scheme.{u}} {x y z : Y}
    (h : x ⤳ y) (h' : y ⤳ z) (h'' : x ⤳ z) (s : Y.presheaf.stalk z) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) =
      (Y.presheaf.stalkSpecializes h'').hom s :=
  TopCat.Presheaf.stalkSpecializes_comp_apply _ h h' s

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  simpa only [componentGenericPoint_eq_genericPoint] using Z.2

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The irreducible component `X` of the integral scheme `X`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rw [componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF, evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
    rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      rw [← hx]
      exact x.2
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · intro h E' hE'
    exact (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · exact Subtype.ext (restrictRF_injective U V (congrArg Subtype.val h))
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictOpen_iso (D : Divisor X) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] :
    Nonempty (Divisor.divisorialSheaf (D.restrictOpen U) ≅ D.divisorialSheaf.restrict U.ι) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom U D)).symm⟩

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  have : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS with hT
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  have : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  have : IsDominant T.ι := isDominant_opens_ι T
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  have : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  have : IsIntegral T := inferInstance
  have : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso KS T
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

end CanonicalDivisorExistence

/-! ### Dimension along a locally quasi-finite dominant morphism -/

section Dimension

/-- A dominant, locally quasi-finite morphism of integral schemes locally of finite type over a
field has a finite extension of function fields: the generic point of the source is the only
point over the generic point of the target. -/
private theorem finite_functionField_of_locallyQuasiFinite {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀]
    [IsIntegral Yₑ] (q : Yₑ ⟶ Y₀) [IsDominant q] [LocallyQuasiFinite q]
    [LocallyOfFiniteType q] :
    letI := (functionFieldMap q).toAlgebra
    Module.Finite Y₀.functionField Yₑ.functionField := by
  have hgen : ∀ x : Yₑ, q x = genericPoint Y₀ → x = genericPoint Yₑ := fun x hx => by
    have hsp := _root_.genericPoint_specializes x
    have h₀ : q (genericPoint Yₑ) = genericPoint Y₀ :=
      ((hx ▸ hsp.map q.continuous).antisymm (_root_.genericPoint_specializes _)).eq
    exact (MMP.Flips.eq_of_specializes_of_locallyQuasiFinite q hsp (h₀.trans hx.symm)).symm
  have h := (trdeg_functionField_eq_zero_iff_finite q).mp
    (trdeg_functionField_eq_zero_of_eq_genericPoint q hgen)
  convert h using 3
  exact (MMP.Mori.dominantFunctionFieldMap_eq_functionFieldMap q).symm

/-- A dominant, locally quasi-finite morphism of varieties preserves dimension: the function
fields have the same transcendence degree, the extension being finite. -/
private theorem topologicalKrullDim_eq_of_locallyQuasiFinite (k : Type u) [Field k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsIntegral Yₑ] (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀)
    [LocallyOfFiniteType s₀] [LocallyOfFiniteType (q ≫ s₀)] [IsDominant q]
    [LocallyQuasiFinite q] : topologicalKrullDim Yₑ = topologicalKrullDim Y₀ := by
  have : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q s₀
  letI := MMP.Mori.functionFieldAlgebra s₀
  letI := MMP.Mori.functionFieldAlgebra (q ≫ s₀)
  letI := MMP.Mori.functionFieldMapAlgebra q
  have := MMP.Mori.isScalarTower_functionFieldMap s₀ q
  have : Module.Finite Y₀.functionField Yₑ.functionField :=
    finite_functionField_of_locallyQuasiFinite q
  rw [← MMP.Mori.toENat_trdeg_functionField (sX := q ≫ s₀),
    ← MMP.Mori.toENat_trdeg_functionField (sX := s₀), ← trdeg_add_eq k Y₀.functionField,
    trdeg_eq_zero (R := Y₀.functionField) (A := Yₑ.functionField), add_zero]

end Dimension

/-! ### Canonical divisors pull back along étale morphisms -/

section CanonicalPullback

/-- An open morphism with nonempty source into an irreducible scheme is dominant. -/
private lemma isDominant_of_isOpenMap {X Y : Scheme.{u}} [IrreducibleSpace Y] [Nonempty X]
    (f : X ⟶ Y) (hf : IsOpenMap f) : IsDominant f :=
  ⟨hf.isOpen_range.dense (Set.range_nonempty _)⟩

/-- An étale morphism from a nonempty scheme to an irreducible scheme is dominant: it is open. -/
private theorem isDominant_of_etale' {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    [IrreducibleSpace X] [Nonempty Y] : IsDominant f :=
  have : UniversallyOpen f := UniversallyOpen.of_flat f
  isDominant_of_isOpenMap f f.isOpenMap

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sX : X ⟶ Spec (.of k)}

/-- The pull-back of a nonzero rational form along a dominant morphism of varieties of the same
dimension, in characteristic zero, is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero_of_topologicalKrullDim_eq
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] {d : ℕ}
    (hX : topologicalKrullDim X = d) (hY : topologicalKrullDim Y = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq sX f hX hY
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **Canonical divisors pull back along étale morphisms.** Let `f : Y ⟶ X` be an étale morphism
of normal varieties over a field of characteristic zero and `K` a `ℚ`-Cartier canonical divisor
of `X`. Then `f^* K` is a `ℚ`-Cartier canonical divisor of `Y`: writing `K = div(ω)`, it is
`div(f^* ω)`. -/
theorem _root_.MMP.Mori.Divisor.exists_isCanonicalDivisor_isPullback_of_etale
    (hX : IsNormalVariety k sX)
    (f : Y ⟶ X) [Etale f] (hY : IsNormalVariety k (f ≫ sX)) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (hKq : (Divisor.toQDivisor K).IsQCartier) :
    ∃ (hK' : ∀ Z : irreducibleComponents Y,
        f (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor K).supp) (Ke : Divisor Y),
      Ke.IsCanonicalDivisor (f ≫ sX) n ∧ (Divisor.toQDivisor Ke).IsQCartier ∧
        (Divisor.toQDivisor K).IsPullback f hK' (Divisor.toQDivisor Ke) := by
  classical
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : QuasiCompact (f ≫ sX) := hY.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsDominant f := isDominant_of_etale' f
  have hdX := hK.topologicalKrullDim_eq
  have hdY : topologicalKrullDim Y = n :=
    (topologicalKrullDim_eq_of_locallyQuasiFinite k sX f).trans hdX
  have hsupp : ∀ (D : Divisor X) (Z : irreducibleComponents Y),
      f (componentGenericPoint Y Z) ∉ D.supp :=
    MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp f
  refine ⟨fun Z => by simpa only [Divisor.supp_toQDivisor] using hsupp K Z, ?_⟩
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  set ωe := pullbackRationalPluriForms sX f ω
  have hωe0 : ωe ≠ 0 :=
    pullbackRationalPluriForms_ne_zero_of_topologicalKrullDim_eq f hdX hdY hω0
  -- The divisor `K_e = div(f^* ω)` has the coefficients of `K` at the images of prime divisors.
  have hcoeff : ∀ (E : MMP.Mori.PrimeDivisor Y) (P : MMP.Mori.PrimeDivisor X),
      P.genericPoint = f E.genericPoint → (divisorOfForm ωe).coeff E = K.coeff P := by
    intro E P hP
    rw [coeff_divisorOfForm, ordForm_pullbackRationalPluriForms_of_etale f hdX hdY E P hP.symm,
      hωK]
  -- `K_e` is canonical: it is linearly equivalent to a canonical divisor.
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor (f ≫ sX) hY hdY
  have hKe : (divisorOfForm ωe).IsCanonicalDivisor (f ≫ sX) n :=
    hK₀.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀ hωe0)
  -- Pull-backs of the Cartier multiples of `K`.
  have hpull : ∀ (m : ℤ) (D : Divisor X), D = m • K → D.IsCartier →
      ∃ hD, D.IsPullback f hD (m • divisorOfForm ωe) := by
    intro m D hD hDc
    obtain ⟨D', hD'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant f hDc
    refine ⟨hsupp D, ?_⟩
    convert hD' using 1
    ext E
    obtain ⟨P, hP⟩ := PrimeDivisor.exists_genericPoint_eq_of_etale f E
    rw [Divisor.IsPullback.coeff_eq_of_etale f hDc hD' E P hP, DivisorWithCoeffs.coeff_smul,
      hcoeff E P hP, hD, DivisorWithCoeffs.coeff_smul]
  refine ⟨divisorOfForm ωe, hKe, ?_, ?_⟩
  · obtain ⟨m, hm, D, hD, hDc⟩ := hKq.exists_pos
    have hDK : D = (m : ℤ) • K := Divisor.toQDivisor_injective (by rw [hD, map_zsmul])
    obtain ⟨hD', hp⟩ := hpull m D hDK hDc
    exact ⟨m, by exact_mod_cast hm.ne', (m : ℤ) • divisorOfForm ωe, by rw [map_zsmul],
      Divisor.IsPullback.isCartier hp hDc⟩
  · intro m hm D hD hDc
    have hDK : D = (m : ℤ) • K := Divisor.toQDivisor_injective (by rw [hD, map_zsmul])
    obtain ⟨hD', hp⟩ := hpull m D hDK hDc
    exact ⟨(m : ℤ) • divisorOfForm ωe, by rw [map_zsmul], hp⟩

end CanonicalPullback

/-! ### Lifting a divisorial valuation to an étale base change -/

section EtaleCentre

open CategoryTheory.Limits

open MMP.Mori MMP.Intersection IsLocalRing
open scoped WithZero

/-- The base change of `μ` along `q`, restricted over `q⁻¹(U)`, is a pullback of `μ ∣_ U`
along `q ∣_ U`. -/
private lemma isPullback_restrict {Y₀ Yₑ W : Scheme.{u}} (q : Yₑ ⟶ Y₀) (μ : W ⟶ Y₀)
    (U : Y₀.Opens) :
    ∃ v : ((pullback.snd μ q) ⁻¹ᵁ (q ⁻¹ᵁ U)).toScheme ⟶ (μ ⁻¹ᵁ U).toScheme,
      IsPullback (pullback.snd μ q ∣_ (q ⁻¹ᵁ U)) v (q ∣_ U) (μ ∣_ U) := by
  have h3 := isPullback_morphismRestrict μ U
  have hc : (pullback.snd μ q ∣_ (q ⁻¹ᵁ U) ≫ q ∣_ U) ≫ U.ι =
      (((pullback.snd μ q) ⁻¹ᵁ (q ⁻¹ᵁ U)).ι ≫ pullback.fst μ q) ≫ μ := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι,
      Category.assoc, Category.assoc, ← pullback.condition]
  refine ⟨h3.lift _ _ hc,
    IsPullback.of_bot (h₂₁ := μ ∣_ U) (v₂₁ := (μ ⁻¹ᵁ U).ι) (v₂₂ := U.ι) ?_ ?_ h3⟩
  · rw [h3.lift_snd, morphismRestrict_ι]
    exact (isPullback_morphismRestrict (pullback.snd μ q) (q ⁻¹ᵁ U)).paste_vert
      (IsPullback.of_hasPullback μ q).flip
  · exact (h3.lift_fst _ _ hc).symm

/-- The base change `μₑ : W ×_{Y₀} Yₑ ⟶ Yₑ` of a morphism `μ` which is an isomorphism over `U` is
an isomorphism over `q⁻¹(U)`. -/
private lemma isIso_pullback_snd_restrict {Y₀ Yₑ W : Scheme.{u}} (q : Yₑ ⟶ Y₀) (μ : W ⟶ Y₀)
    (U : Y₀.Opens) [IsIso (μ ∣_ U)] : IsIso (pullback.snd μ q ∣_ (q ⁻¹ᵁ U)) :=
  (isPullback_restrict q μ U).choose_spec.isIso_fst_of_isIso

/-- If `U` is a dense open of `Y₀` and `q : Yₑ ⟶ Y₀` is an open map with nonempty source, then
`q⁻¹(U)` is nonempty. -/
private lemma nonempty_preimage_of_dense {Y₀ Yₑ : Scheme.{u}} [Nonempty Yₑ] (q : Yₑ ⟶ Y₀)
    (hq : IsOpenMap q) {U : Y₀.Opens} (hU : Dense (U : Set Y₀)) :
    ((q ⁻¹ᵁ U : Yₑ.Opens) : Set Yₑ).Nonempty := by
  obtain ⟨x⟩ : Nonempty Yₑ := inferInstance
  obtain ⟨_, ⟨x', rfl⟩, hx'⟩ := hU.inter_open_nonempty _ hq.isOpen_range ⟨q x, x, rfl⟩
  exact ⟨x', hx'⟩

/-- A dominant morphism of integral schemes which is an isomorphism over a nonempty open induces
an isomorphism of function fields. -/
private lemma functionFieldMap_bijective_of_isIso {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] (U : X.Opens) (hU : (U : Set X).Nonempty)
    [IsIso (f ∣_ U)] : Function.Bijective (functionFieldMap f) := by
  obtain ⟨x, hx⟩ := hU
  have hne : ((f ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty :=
    ⟨_, ((inv (f ∣_ U)) ⟨x, hx⟩).2⟩
  have : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  exact MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion f _ hne

/-- A non-unit of the valuation ring of `v` has valuation `< 1`. -/
private lemma valuation_lt_one_of_mem_nonunits {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (r : v.valuationSubring) (hr : ¬ IsUnit r) : v (r : K) < 1 :=
  lt_of_le_of_ne ((v.mem_valuationSubring_iff _).1 r.2) fun h1 =>
    hr ((Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers v)
      (x := ⟨r, r.2⟩)).2 h1)

/-- **Existence of a centre along a proper birational morphism.** Let `f : X ⟶ Y` be a proper
dominant morphism of integral schemes inducing an isomorphism of function fields, and `w'` a
valuation of `k(X)` whose restriction `w` to `k(Y)` has a centre `y` on `Y`. Then `w'` has a
centre `x` on `X`. -/
private lemma exists_centre_of_isProper {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsProper f] (w : Valuation Y.functionField ℤᵐ⁰)
    (w' : Valuation X.functionField ℤᵐ⁰) (hw' : ∀ g, w' (functionFieldMap f g) = w g) (y : Y)
    (h1 : ∀ a : Y.presheaf.stalk y, w (algebraMap _ Y.functionField a) ≤ 1) :
    ∃ x : X, (∀ a : X.presheaf.stalk x, w' (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ maximalIdeal (X.presheaf.stalk x), w' (algebraMap _ X.functionField a) < 1 := by
  set R := w'.valuationSubring
  let φ : Y.presheaf.stalk y →+* R :=
    ((functionFieldMap f).comp (algebraMap (Y.presheaf.stalk y) Y.functionField)).codRestrict R
      fun a => (w'.mem_valuationSubring_iff _).2 (by simpa [hw'] using h1 a)
  have hy : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
  have hex : ValuativeCriterion.Existence f := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact h.1
  have hc : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap R X.functionField) =
      Y.presheaf.stalkSpecializes hy ≫ CommRingCat.ofHom (functionFieldMap f) := by
    ext a
    rfl
  have hsq : X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫
        (Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk y) := by
    rw [← functionFieldMap_fromSpecStalk, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hy,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hc]
    rfl
  let S : ValuativeCommSq f :=
    { R := R
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk y
      commSq := ⟨hsq⟩ }
  obtain ⟨l', hl₁', -⟩ := (hex S).exists_lift
  let l : Spec (.of R) ⟶ X := l'
  have hl₁ : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ l =
      X.fromSpecStalk (genericPoint X) := hl₁'
  clear_value l
  clear hl₁'
  set x' := l (IsLocalRing.closedPoint R)
  let ψ := Scheme.stalkClosedPointTo l
  have hψ : ∀ a, algebraMap R X.functionField (ψ.hom a) =
      algebraMap (X.presheaf.stalk x') X.functionField a := by
    intro a
    have hl : Spec.map ψ ≫ X.fromSpecStalk x' = l := Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
    have hgen : genericPoint X ⤳ x' := _root_.genericPoint_specializes _
    have key : Spec.map (ψ ≫ CommRingCat.ofHom (algebraMap R X.functionField)) ≫
        X.fromSpecStalk x' =
        Spec.map (X.presheaf.stalkSpecializes hgen) ≫ X.fromSpecStalk x' := by
      rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact (Spec.map_comp_assoc ψ _ _).trans (by rw [hl]; exact hl₁)
    exact congrArg (fun g => g.hom a) (Spec.map_injective ((cancel_mono _).1 key))
  refine ⟨x', fun a => ?_, fun a ha => ?_⟩
  · rw [← hψ]
    exact (w'.mem_valuationSubring_iff _).1 (ψ.hom a).2
  · rw [← hψ]
    refine valuation_lt_one_of_mem_nonunits w' _ fun hu => ?_
    exact (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit ψ.hom a hu)

/-- **Unramified extensions of a discrete valuation ring.** Let `A → B` be a local,
formally unramified, essentially finite type homomorphism of local rings, with `A` a discrete
valuation ring and `B` a Noetherian domain. If a uniformizer `ϖ` of `A` does not vanish in `B`,
then `B` is a discrete valuation ring with uniformizer the image of `ϖ`. -/
private lemma isDiscreteValuationRing_of_formallyUnramified {A B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] {ϖ : A} (hϖ : Irreducible ϖ)
    (h0 : algebraMap A B ϖ ≠ 0) :
    IsDiscreteValuationRing B ∧ Irreducible (algebraMap A B ϖ) := by
  have hmax : maximalIdeal B = Ideal.span {algebraMap A B ϖ} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A),
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  have hnf : ¬ IsField B := by
    rwa [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
  have : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnf).out 5 1).1 (⟨⟨_, hmax⟩⟩ : (maximalIdeal B).IsPrincipal)
  exact ⟨this, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax⟩

/-- `ℤᵐ⁰`: `exp (-1) ^ e = exp (-1)` forces `e = 1`. -/
private lemma eq_one_of_exp_pow {e : ℕ} (h : (WithZero.exp (-1 : ℤ)) ^ e = WithZero.exp (-1)) :
    e = 1 := by
  rw [← WithZero.exp_nsmul, WithZero.exp_inj] at h
  simpa using h

/-- The local ring of a normal locally Noetherian integral scheme at the generic point of a
prime divisor `E` is a discrete valuation ring, with a uniformizer of `ord_E`-value `exp (-1)`. -/
private lemma exists_irreducible_divisorialValuation_eq {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : MMP.Mori.PrimeDivisor X) {z : X}
    (hz : z = E.genericPoint) :
    IsDiscreteValuationRing (X.presheaf.stalk z) ∧ ∃ ϖ : X.presheaf.stalk z, Irreducible ϖ ∧
      E.divisorialValuation (algebraMap _ X.functionField ϖ) = WithZero.exp (-1) := by
  subst hz
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  exact ⟨this, ϖ, hϖ, E.divisorialValuation_algebraMap_of_irreducible hϖ⟩

/-- `ord_E` is centred at the generic point of `E`: it is `≤ 1` on `𝒪_{X,E}` and `< 1` on its
maximal ideal. -/
private lemma divisorialValuation_centre {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : MMP.Mori.PrimeDivisor X) {z : X}
    (hz : z = E.genericPoint) :
    (∀ a : X.presheaf.stalk z, E.divisorialValuation (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ maximalIdeal (X.presheaf.stalk z),
        E.divisorialValuation (algebraMap _ X.functionField a) < 1 := by
  subst hz
  exact ⟨fun a => (E.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩,
    fun a ha => (E.divisorialValuation_algebraMap_lt_one_iff a).2 ha⟩

/-- Let `p : P ⟶ W` be a formally unramified, locally finite type, dominant morphism of integral
schemes with `P` locally Noetherian. If the local ring of `W` at `p x` is a discrete valuation ring
with uniformizer `ϖ`, then so is the local ring of `P` at `x`, with uniformizer the image of
`ϖ`. -/
private lemma isDiscreteValuationRing_stalk_of_formallyUnramified {P W : Scheme.{u}}
    [IsIntegral P] [IsIntegral W] [IsLocallyNoetherian P] (p : P ⟶ W) [FormallyUnramified p]
    [LocallyOfFiniteType p] [IsDominant p] (x : P)
    [IsDiscreteValuationRing (W.presheaf.stalk (p x))] {ϖ : W.presheaf.stalk (p x)}
    (hϖ : Irreducible ϖ) :
    IsDiscreteValuationRing (P.presheaf.stalk x) ∧ Irreducible ((p.stalkMap x).hom ϖ) := by
  letI : Algebra (W.presheaf.stalk (p x)) (P.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
  have : Algebra.FormallyUnramified (W.presheaf.stalk (p x)) (P.presheaf.stalk x) :=
    AlgebraicGeometry.FormallyUnramified.stalkMap (f := p) x
  have : Algebra.EssFiniteType (W.presheaf.stalk (p x)) (P.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap (f := p) x
  have : IsLocalHom (algebraMap (W.presheaf.stalk (p x)) (P.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (p.stalkMap x).hom)
  refine isDiscreteValuationRing_of_formallyUnramified hϖ fun h0 => hϖ.ne_zero ?_
  have := MMP.Mori.functionFieldMap_algebraMap_stalk p x ϖ
  rwa [show (p.stalkMap x).hom ϖ = 0 from h0, map_zero, map_eq_zero_iff _ (RingHom.injective _),
    map_eq_zero_iff _ (IsFractionRing.injective _ _)] at this

/-- Let `Y₀` be separated over `k`, `q : Yₑ ⟶ Y₀` dominant étale, `μ : W ⟶ Y₀` proper from a
normal integral `W` and an isomorphism over a dense open `U`, `E` a prime divisor of `W`, and `w` a
normalized divisorial valuation of `k(Yₑ)` whose restriction to `k(Y₀)` is `(ord_E)^e` with
`e ≥ 1`. Then there is a prime divisor `E'` of `Wₑ = W ×_{Y₀} Yₑ` whose generic point lies over
that of `E`, with `w = ord_{E'}` and `e = 1`. -/
private theorem exists_primeDivisor_valuationOver_eq_of_etale_of_isProper {k : Type u} [Field k]
    {Y₀ Yₑ W : Scheme.{u}} (s : Y₀ ⟶ Spec (.of k)) [IsSeparated s] [IsIntegral Y₀] [IsIntegral Yₑ]
    (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    [IsIntegral W] [IsNormal W] [IsLocallyNoetherian W] (μ : W ⟶ Y₀) [IsProper μ]
    [IsDominant μ] {U : Y₀.Opens} (hU : Dense (U : Set Y₀)) (hμU : MMP.Mori.IsBiregular μ U)
    [IsIntegral (pullback μ q)] [IsNormal (pullback μ q)] [IsLocallyNoetherian (pullback μ q)]
    [IsDominant (pullback.snd μ q)]
    (E : MMP.Mori.PrimeDivisor W) {w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ))}
    (hw : IsNormalizedDivisorialValuation k (q ≫ s) w) {e : ℕ} (he : 1 ≤ e)
    (hwE : ∀ g, w (functionFieldMap q g) = E.valuationOver μ g ^ e) :
    ∃ E' : MMP.Mori.PrimeDivisor (pullback μ q),
      pullback.fst μ q E'.genericPoint = E.genericPoint ∧
        w = E'.valuationOver (pullback.snd μ q) ∧ e = 1 := by
  set P := pullback μ q
  set p := pullback.fst μ q
  set m := pullback.snd μ q
  -- Function fields: `μ` and `μₑ` are birational.
  have : IsIso (μ ∣_ U) := hμU
  have hμbij : Function.Bijective (functionFieldMap μ) :=
    functionFieldMap_bijective_of_isIso μ U hU.nonempty
  have : IsIso (m ∣_ (q ⁻¹ᵁ U)) := isIso_pullback_snd_restrict q μ U
  have hmbij : Function.Bijective (functionFieldMap m) :=
    functionFieldMap_bijective_of_isIso m _ (nonempty_preimage_of_dense q q.isOpenMap hU)
  have : UniversallyOpen p := UniversallyOpen.of_flat _
  have : IsDominant p := isDominant_of_isOpenMap p p.isOpenMap
  -- The valuation `w` transported to `k(Wₑ)`.
  let eψ := RingEquiv.ofBijective (functionFieldMap m) hmbij
  let w' : Valuation P.functionField ℤᵐ⁰ := w.comap eψ.symm.toRingHom
  have hw' : ∀ g, w' (functionFieldMap m g) = w g := fun g => by
    change w (eψ.symm (eψ g)) = w g
    rw [RingEquiv.symm_apply_apply]
  -- The centre of `w` on `Yₑ`.
  obtain ⟨D, hDp, rfl⟩ := hw
  have hcY := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl
  -- The centre `x` of `w'` on `Wₑ`.
  obtain ⟨x, hx1, hx2⟩ := exists_centre_of_isProper m D.valuation w' hw' _ hcY
  -- The restriction of `w'` to `k(W)` is `ord_E ^ e`.
  let wW : Valuation W.functionField ℤᵐ⁰ := w'.comap (functionFieldMap p)
  have hwW : ∀ h, wW h = E.divisorialValuation h ^ e := by
    intro h
    obtain ⟨g, rfl⟩ := hμbij.2 h
    change w' (functionFieldMap p (functionFieldMap μ g)) = _
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr pullback.condition,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, hw', hwE]
    rfl
  have hstalk : ∀ a : W.presheaf.stalk (p x),
      wW (algebraMap _ W.functionField a) =
        w' (algebraMap _ P.functionField ((p.stalkMap x).hom a)) := fun a => by
    change w' (functionFieldMap p _) = _
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
  -- `p(x) = η_E`, by uniqueness of centres on the separated scheme `W`.
  have hpx : p x = E.genericPoint := by
    refine MMP.Positivity.DivisorOver.eq_of_dominates (μ ≫ s) wW (fun a => ?_)
      (fun a ha => ?_) (fun a => ?_) (fun a ha => ?_)
    · rw [hstalk]; exact hx1 _
    · rw [hstalk]; exact hx2 _ (map_nonunit (p.stalkMap x).hom a ha)
    · rw [hwW]
      exact pow_le_one₀ zero_le' ((divisorialValuation_centre E rfl).1 a)
    · rw [hwW]
      exact pow_lt_one₀ zero_le' ((divisorialValuation_centre E rfl).2 a ha) (by omega)
  -- A uniformizer of `𝒪_{W,p(x)} = 𝒪_{W,E}`.
  obtain ⟨hAdvr, ϖ, hϖ, hϖv⟩ := exists_irreducible_divisorialValuation_eq E hpx
  -- `p` is étale, so `ϖ` stays a uniformizer of `𝒪_{Wₑ,x}`.
  obtain ⟨hBdvr, hirr⟩ := isDiscreteValuationRing_stalk_of_formallyUnramified p x hϖ
  have hco : Order.coheight x = 1 := by
    have h := IsDiscreteValuationRing.ringKrullDim_eq_one (P.presheaf.stalk x)
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  -- The prime divisor `E'` with generic point `x`.
  set E' : MMP.Mori.PrimeDivisor P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE' : E'.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have h3 : ∃ g, w' g = WithZero.exp (-1) := by
    obtain ⟨g, hg⟩ := MMP.Positivity.DivisorOver.exists_valuation_eq_exp_neg_one D
    exact ⟨_, (hw' g).trans hg⟩
  obtain ⟨hv1, hv2⟩ := divisorialValuation_centre E' hE'.symm
  obtain ⟨-, ϖ', -, hϖ'⟩ := exists_irreducible_divisorialValuation_eq E' rfl
  have hww : w' = E'.divisorialValuation :=
    MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing (R := P.presheaf.stalk x)
      hx1 hx2 h3 hv1 hv2 ⟨_, hϖ'⟩
  refine ⟨E', hE' ▸ hpx, ?_, ?_⟩
  · ext g
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, ← hww, hw']
  · apply eq_one_of_exp_pow
    have h1 := hstalk ϖ
    rwa [hwW, hϖv, MMP.Positivity.DivisorOver.valuation_algebraMap_of_irreducible w' hx1 hx2 h3
      hirr] at h1

/-- A morphism which is an isomorphism over a dense open `U` of its target is dominant: its
range contains `U`. -/
private lemma isDominant_of_isIso_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} (hU : Dense (U : Set Y)) [IsIso (f ∣_ U)] : IsDominant f := by
  refine ⟨hU.mono fun y hy => ?_⟩
  obtain ⟨z, hz⟩ := (f ∣_ U).homeomorph.surjective ⟨y, hy⟩
  exact ⟨z.1, by rw [← morphismRestrict_base_coe]; exact congrArg Subtype.val hz⟩

/-- A space with an open map to an irreducible space is irreducible as soon as the preimage
of some open set is irreducible: that preimage is dense. -/
private lemma irreducibleSpace_of_isIrreducible_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [IrreducibleSpace Y] {f : X → Y} (hf : IsOpenMap f) {O : Set Y}
    (hO : IsOpen O) (h : IsIrreducible (f ⁻¹' O)) : IrreducibleSpace X := by
  obtain ⟨x, hx⟩ := h.nonempty
  rw [irreducibleSpace_def]
  simpa [((hO.dense ⟨_, hx⟩).preimage hf).closure_eq] using h.closure

/-- **Étale base change of a birational morphism.** Let `q : Yₑ ⟶ Y₀` be étale with `Yₑ`
integral, and `μ : W ⟶ Y₀` an isomorphism over a dense open `U`, with `W` integral, normal and
locally Noetherian. Then `Wₑ = W ×_{Y₀} Yₑ` is integral, normal and locally Noetherian, and
`μₑ : Wₑ ⟶ Yₑ` is dominant. The projection `Wₑ ⟶ W` is étale, which gives normality (hence
reducedness) and local Noetherianity; `μₑ` is an isomorphism over `q⁻¹(U)`, so `μₑ⁻¹(q⁻¹(U))` is
irreducible, and it is the preimage of `μ⁻¹(U)` under the open projection `Wₑ ⟶ W`, so `Wₑ` is
irreducible. -/
private lemma isIntegral_isNormal_pullback_of_etale {Y₀ Yₑ W : Scheme.{u}} [IsIntegral Yₑ]
    (q : Yₑ ⟶ Y₀) [Etale q] [IsIntegral W] [IsNormal W] [IsLocallyNoetherian W] (μ : W ⟶ Y₀)
    {U : Y₀.Opens} (hU : Dense (U : Set Y₀)) (hμU : IsIso (μ ∣_ U)) :
    IsIntegral (pullback μ q) ∧ IsNormal (pullback μ q) ∧ IsLocallyNoetherian (pullback μ q) ∧
      IsDominant (pullback.snd μ q) := by
  have : Etale (pullback.fst μ q) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback μ q).flip ‹Etale q›
  have : UniversallyOpen q := UniversallyOpen.of_flat q
  have : UniversallyOpen (pullback.fst μ q) := UniversallyOpen.of_flat _
  have hN : IsNormal (pullback μ q) := isNormal_of_etale (pullback.fst μ q)
  -- `μₑ` is an isomorphism over `q⁻¹(U)`.
  have := isIso_pullback_snd_restrict q μ U
  set V := (pullback.snd μ q) ⁻¹ᵁ (q ⁻¹ᵁ U)
  obtain ⟨y, hy⟩ := nonempty_preimage_of_dense q q.isOpenMap hU
  have hqU : Dense ((q ⁻¹ᵁ U : Yₑ.Opens) : Set Yₑ) := (q ⁻¹ᵁ U).isOpen.dense ⟨y, hy⟩
  have : Nonempty (q ⁻¹ᵁ U).toScheme := ⟨⟨y, hy⟩⟩
  have : Nonempty V.toScheme := ⟨(inv (pullback.snd μ q ∣_ (q ⁻¹ᵁ U))) ⟨y, hy⟩⟩
  have : IsIntegral V.toScheme :=
    isIntegral_of_isOpenImmersion (pullback.snd μ q ∣_ (q ⁻¹ᵁ U))
  have hVirr : IsIrreducible (V : Set ↥(pullback μ q)) := by
    have := (IrreducibleSpace.isIrreducible_univ V.toScheme).image V.ι V.ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at this
  -- `V` is the preimage of `μ⁻¹(U)` under the open projection to `W`.
  have hVeq : (V : Set ↥(pullback μ q)) = pullback.fst μ q ⁻¹' (μ ⁻¹ᵁ U : Set W) := by
    ext x
    change q (pullback.snd μ q x) ∈ U ↔ μ (pullback.fst μ q x) ∈ U
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have : IrreducibleSpace ↥(pullback μ q) :=
    irreducibleSpace_of_isIrreducible_preimage (pullback.fst μ q).isOpenMap
      (μ ⁻¹ᵁ U).isOpen (hVeq ▸ hVirr)
  exact ⟨isIntegral_of_irreducibleSpace_of_isReduced _, hN, inferInstance,
    isDominant_of_isIso_morphismRestrict _ hqU⟩

end EtaleCentre

/-! ### Pull-back of forms along composites -/

section FormsComp

variable {k : Type u} [Field k] [CharZero k] {X Y Z : Scheme.{u}} [IsIntegral X]
  [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]

/-- **Pull-back of rational forms along a composite**: `g^*(f^*τ) = (f ∘ g)^*τ`, for dominant
morphisms of varieties of the same dimension in characteristic zero. -/
private theorem pullbackRationalPluriForms_comp (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f]
    [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] [LocallyOfFiniteType (g ≫ f ≫ sX)] {d : ℕ}
    (hX : topologicalKrullDim X = d) (hY : topologicalKrullDim Y = d)
    (hZ : topologicalKrullDim Z = d) {m : ℤ} (τ : RationalPluriForms sX d m) :
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
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq sX f hX hY
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq (f ≫ sX) g hY hZ
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap k X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- **Orders of pulled-back forms along a composite**: `ord_E(g^*(f^*τ)) = ord_E((f ∘ g)^*τ)`. -/
private theorem ordForm_pullbackRationalPluriForms_comp [IsLocallyNoetherian Z] (f : Y ⟶ X)
    (g : Z ⟶ Y) [IsDominant f] [IsDominant g] [LocallyOfFiniteType (f ≫ sX)]
    [LocallyOfFiniteType (g ≫ f ≫ sX)] {d : ℕ} (hX : topologicalKrullDim X = d)
    (hY : topologicalKrullDim Y = d) (hZ : topologicalKrullDim Z = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) (E : MMP.Mori.PrimeDivisor Z) :
    E.ordForm (pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ)) =
      E.ordForm (pullbackRationalPluriForms sX (g ≫ f) τ) := by
  rw [pullbackRationalPluriForms_comp f g hX hY hZ τ]
  rfl

omit [LocallyOfFiniteType sX] in
/-- The order of a pulled-back form only depends on the morphism. -/
private theorem ordForm_pullbackRationalPluriForms_congr [IsLocallyNoetherian Z]
    {g₁ g₂ : Z ⟶ X} (h : g₁ = g₂) [IsDominant g₁] [IsDominant g₂] (E : MMP.Mori.PrimeDivisor Z)
    {d : ℕ} {m : ℤ} (τ : RationalPluriForms sX d m) :
    E.ordForm (pullbackRationalPluriForms sX g₁ τ) =
      E.ordForm (pullbackRationalPluriForms sX g₂ τ) := by
  subst h
  rfl

end FormsComp

/-! ### Birational morphisms and exceptional divisors -/

section Birational

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open of the target
is a birational morphism. -/
private theorem isBirationalMorphism_of_isIso_morphismRestrict {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) {V : Y.Opens}
    (hV : (V : Set Y).Nonempty) [IsIso (f ∣_ V)] : IsBirationalMorphism f := by
  obtain ⟨y, hy⟩ := hV
  obtain ⟨x, hx⟩ := (f ∣_ V).homeomorph.surjective ⟨y, hy⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ V) V ⟨x.1, x.2⟩ ⟨y, hy⟩ le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- A proper birational morphism `μ : W ⟶ X` of integral schemes onto a normal scheme is an
isomorphism over a dense open of `X`: its finite-fibre locus. -/
private theorem exists_dense_isIso_of_isProper {X W : Scheme.{u}} [IsIntegral X] [IsIntegral W]
    [IsNormal X] [IsLocallyNoetherian X] (μ : W ⟶ X) [IsProper μ] (hμ : IsBirationalMorphism μ) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (μ ∣_ U) := by
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hμ
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso μ hb).1
    inferInstance
  exact ⟨⟨_, hU⟩, hU.dense ⟨_, MMP.Mori.map_genericPoint_mem_finiteFibreLocus μ hb⟩, hiso⟩

end Birational

/-! ### Exceptional divisors and log discrepancies over a variety -/

section Exceptional

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)}

/-- A divisor `(Y, f, E)` over a normal variety `X` is exceptional exactly when its center has
codimension at least two. -/
private theorem isExceptional_iff_two_le_codimension_center (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) : D.IsExceptional ↔ 2 ≤ codimension D.center := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have hsep : IsSeparated (X ↘ ⊤_ Scheme) := by
    have : (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) := Subsingleton.elim _ _
    rw [this]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := by
    refine Closeds.ext ?_
    rw [Closeds.coe_closure]
    exact D.coe_center.symm
  rw [hc]
  change 2 ≤ closedsCodimension (T := X) ⟨(D.center : Set X), D.center.isClosed⟩ ↔ _
  rw [closedsCodimension_coe]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- The codimension of the closure of a point is the coheight of the point. -/
private theorem codimension_closureSingleton (x : X) :
    codimension (IrreducibleCloseds.closureSingleton x) = Order.coheight x := by
  rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton x =
    (irreducibleSetEquivPoints (α := X)).symm x from rfl, Order.coheight_orderIso]

/-- A divisor `(Y, f, E)` over a normal variety `X` is exceptional exactly when `f(η_E)` has
codimension at least two. -/
private theorem isExceptional_iff_two_le_coheight (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) : D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  rw [isExceptional_iff_two_le_codimension_center hX, ← codimension_closureSingleton,
    show D.center = IrreducibleCloseds.closureSingleton (D.f D.E.genericPoint) from
      IrreducibleCloseds.ext D.center_eq_closure_genericPoint]

variable [IsAlgClosed k] [CharZero k]

/-- Adding an effective `ℚ`-Cartier boundary lowers log discrepancies: a log discrepancy `a` of a
divisor `D` over `(X, 0)` bounds above a log discrepancy of `D` over `(X, B)`. -/
private theorem exists_isLogDiscrepancy_le {B : QDivisor X} (hBe : B.IsEffective)
    (hB : B.IsQCartier) (hP : MMP.Mori.IsPair sX 0) {n : ℕ} {D : DivisorOver k sX} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor 0) D a) :
    ∃ a' : ℝ, a' ≤ a ∧
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a' := by
  obtain ⟨-, hf, -, -, ⟨K, hK, -⟩, -⟩ := id ha
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  obtain ⟨c', hle, hc'⟩ := MMP.Threefold.Mori.Helpers.exists_isDiscrepancy_add_le hBe hB hc
  rw [zero_add] at hc'
  refine ⟨1 + (c' : ℝ), ?_,
    MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc' hf⟩
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
  gcongr

end Exceptional

/-! ### Log discrepancies along an étale morphism -/

section EtaleDiscrepancy

open CategoryTheory.Limits

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sX : X ⟶ Spec (.of k)}

/-- **Log discrepancies along an étale morphism.** Let `f : Y ⟶ X` be an étale morphism of normal
varieties over a field of characteristic zero, with `X` `ℚ`-factorial. For every divisor `D`
over `Y` with log discrepancy `a = a(D; Y, 0)`, there is a divisor `D₀` over `X`, realizing the
restriction of the valuation of `D` to `k(X)`, with `a(D₀; X, 0) = a`, which is exceptional over
`X` when `D` is exceptional over `Y`. -/
private theorem exists_isLogDiscrepancy_of_etale (hX : IsNormalVariety k sX)
    (hQ : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier)
    (f : Y ⟶ X) [Etale f] (hY : IsNormalVariety k (f ≫ sX)) {n : ℕ}
    {D : DivisorOver k (f ≫ sX)} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy (f ≫ sX) n (QDivisor.toRDivisor 0) D a) :
    ∃ D₀ : DivisorOver k sX,
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor 0) D₀ a ∧
        (D.IsExceptional → D₀.IsExceptional) := by
  classical
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsSeparated sX := hX.1.toIsSeparated
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsDominant f := isDominant_of_etale' f
  obtain ⟨-, hDp, -, -, ⟨Ke₀, hKe₀, -⟩, -⟩ := id ha
  have hdY := hKe₀.topologicalKrullDim_eq
  have hdX : topologicalKrullDim X = n :=
    (topologicalKrullDim_eq_of_locallyQuasiFinite k sX f).symm.trans hdY
  -- A `ℚ`-Cartier canonical divisor `K` of `X` and its pull-back `K_e`.
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor sX hX hdX
  have hKq : (Divisor.toQDivisor K).IsQCartier := by
    obtain ⟨m, hm, hmK⟩ := hQ K
    exact ⟨m, by exact_mod_cast hm.ne', (m : ℤ) • K, by rw [map_zsmul], hmK⟩
  obtain ⟨hK', Ke, hKe, -, hpb⟩ :=
    Divisor.exists_isCanonicalDivisor_isPullback_of_etale hX f hY hK hKq
  -- The restriction of `ord_D` to `k(X)` is a power of `ord_{D₀}`, `D₀` on a proper model.
  obtain ⟨v, ⟨D₀, hD₀p, rfl⟩, e, he, hwe⟩ :=
    MMP.Fourfold.exists_isNormalizedDivisorialValuation_comap_eq_pow k sX f hX.1 hY.1
      D.valuation ⟨D, hDp, rfl⟩
  have := D₀.isIntegral
  have := D₀.isNormal
  have := D₀.isLocallyNoetherian
  have := D₀.isDominant
  have : IsProper D₀.f := hD₀p
  have : MMP.Mori.IsVariety k sX := hX.1
  have : MMP.Mori.IsVariety k (D₀.f ≫ sX) := D₀.isNormalVariety.1
  obtain ⟨U, hU, hμU⟩ := exists_dense_isIso_of_isProper D₀.f D₀.isBirationalMorphism
  obtain ⟨h1, h2, h3, h4⟩ := isIntegral_isNormal_pullback_of_etale f D₀.f hU hμU
  -- The base change `W_e = W ×_X Y` and the prime divisor `E'` over `E₀` with `ord_{E'} = ord_D`.
  obtain ⟨E', hE'gen, hwE', -⟩ := exists_primeDivisor_valuationOver_eq_of_etale_of_isProper sX f
    D₀.f hU hμU D₀.E ⟨D, hDp, rfl⟩ he hwe
  set p := pullback.fst D₀.f f
  set g := pullback.snd D₀.f f
  have hcond : g ≫ f = p ≫ D₀.f := pullback.condition.symm
  have : Etale p := MorphismProperty.of_isPullback (IsPullback.of_hasPullback D₀.f f).flip ‹_›
  have : IsDominant p := isDominant_of_etale' p
  have hgv : MMP.Mori.IsVariety k (g ≫ f ≫ sX) := by
    have : MMP.Mori.IsVariety k (f ≫ sX) := hY.1
    exact { toIsIntegral := h1 }
  have hgbir : IsBirationalMorphism g := by
    have : IsIso (g ∣_ (f ⁻¹ᵁ U)) := isIso_pullback_snd_restrict f D₀.f U
    exact isBirationalMorphism_of_isIso_morphismRestrict g
      (nonempty_preimage_of_dense f f.isOpenMap hU)
  let D' : DivisorOver k (f ≫ sX) :=
    { Y := pullback D₀.f f
      f := g
      isNormalVariety := ⟨hgv, h2⟩
      isBirationalMorphism := hgbir
      E := E' }
  have hv : D.valuation = D'.valuation := hwE'
  -- Dimensions.
  have hdW : topologicalKrullDim D₀.Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (D₀.f ≫ sX)
      D₀.isBirationalMorphism).symm.trans hdX
  have : LocallyOfFiniteType (D₀.f ≫ sX) := inferInstance
  have hdWe : topologicalKrullDim D'.Y = n :=
    (topologicalKrullDim_eq_of_locallyQuasiFinite k (D₀.f ≫ sX) p).trans hdW
  -- The Kollár–Mori discrepancy of `D₀` over `X` is that of `D'` over `Y`.
  have hP : MMP.Mori.IsPair sX 0 := ⟨hX, n, K, hK, by rwa [add_zero]⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D₀
  have hc' : MMP.Mori.IsDiscrepancy (f ≫ sX) n Ke 0 D' c := by
    obtain ⟨-, -, m₀, hm₀, hC, U₀, hU₀, τ, hτ, hτc⟩ := hc
    refine ⟨hY, hKe, m₀, hm₀, ?_, f ⁻¹ᵁ U₀, ?_, pullbackRationalPluriForms sX f τ, ?_, ?_⟩
    · obtain ⟨C, hCq, hCc⟩ := hC
      obtain ⟨C', hC'q, hC'pb⟩ := hpb m₀ hm₀ C (by rw [hCq, add_zero]) hCc
      exact ⟨C', by rw [hC'q, add_zero], Divisor.IsPullback.isCartier hC'pb hCc⟩
    · change f (g E'.genericPoint) ∈ U₀
      rw [← Scheme.Hom.comp_apply, hcond, Scheme.Hom.comp_apply]
      change D₀.f (p E'.genericPoint) ∈ U₀
      rwa [hE'gen]
    · refine ⟨pullbackRationalPluriForms_ne_zero_of_topologicalKrullDim_eq f hdX hdY hτ.1,
        fun Γ hΓ => ?_⟩
      have hη : f Γ.genericPoint ∈ U₀ := (Γ.genericPoint_mem_iff (f ⁻¹ᵁ U₀)).mpr hΓ
      obtain ⟨P, hP⟩ := PrimeDivisor.exists_genericPoint_eq_of_etale f Γ
      have h := hτ.2 P ((P.genericPoint_mem_iff U₀).mp (hP ▸ hη))
      rw [ordForm_pullbackRationalPluriForms_of_etale f hdX hdY Γ P hP.symm]
      simpa using h
    · rw [hτc]
      change D₀.E.ordForm (pullbackRationalPluriForms sX D₀.f τ) =
        (E'.ordForm (pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ)) :
          ℚ)
      congr 1
      rw [ordForm_pullbackRationalPluriForms_comp f g hdX hdY hdWe τ,
        ordForm_pullbackRationalPluriForms_congr hcond,
        ← ordForm_pullbackRationalPluriForms_comp D₀.f p hdX hdW hdWe τ,
        ordForm_pullbackRationalPluriForms_of_etale p hdW hdWe E' D₀.E hE'gen]
  have hla := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc'
    (show IsProper D'.f from inferInstanceAs (IsProper g))
  have haeq : a = 1 + (c : ℝ) :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hla hv
  refine ⟨D₀, ?_, fun hDex => ?_⟩
  · rw [haeq]
    exact MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy
      (by simpa using hc) hD₀p
  · rw [isExceptional_iff_two_le_coheight hY] at hDex
    rw [isExceptional_iff_two_le_coheight hX]
    have hcen : D.f D.E.genericPoint = D'.f D'.E.genericPoint :=
      MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hY hv
    have hμ : D₀.f D₀.E.genericPoint = f (g E'.genericPoint) := by
      rw [← hE'gen]
      change (p ≫ D₀.f) E'.genericPoint = (g ≫ f) E'.genericPoint
      rw [hcond]
    rw [hμ, coheight_eq_of_etale f]
    rwa [hcen] at hDex

/-- **Log discrepancies over an étale cover dominate those downstairs.** Let `f : Y ⟶ X` be an
étale morphism of normal varieties over an algebraically closed field of characteristic zero,
with `X` `ℚ`-factorial, and `B` an effective `ℚ`-Cartier divisor on `X`. Every log discrepancy
`a = a(D; Y, 0)` of a divisor `D` over `Y` bounds above a log discrepancy `a(D₀; X, B)` of a
divisor `D₀` over `X`, which is exceptional over `X` when `D` is exceptional over `Y`. -/
private theorem exists_isLogDiscrepancy_le_of_etale [IsAlgClosed k] (hX : IsNormalVariety k sX)
    (hQ : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier) (hP : MMP.Mori.IsPair sX 0)
    {B : QDivisor X} (hBe : B.IsEffective) (hB : B.IsQCartier) (f : Y ⟶ X) [Etale f]
    (hY : IsNormalVariety k (f ≫ sX)) {n : ℕ} {D : DivisorOver k (f ≫ sX)} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy (f ≫ sX) n (QDivisor.toRDivisor 0) D a) :
    ∃ (D₀ : DivisorOver k sX) (a' : ℝ), a' ≤ a ∧
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D₀ a' ∧
        (D.IsExceptional → D₀.IsExceptional) := by
  obtain ⟨D₀, ha₀, hex⟩ := exists_isLogDiscrepancy_of_etale hX hQ f hY ha
  obtain ⟨a', hle, ha'⟩ := exists_isLogDiscrepancy_le hBe hB hP ha₀
  exact ⟨D₀, a', hle, ha', hex⟩

end EtaleDiscrepancy

/-! ### The variety of a local étale datum -/

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- For a local étale datum `(Y_e, q, η', L̃)` of a local setting `(Y, Θ, T, π)`: every canonical
divisor `K_Y` of `Y` is `ℚ`-Cartier and its pull-back `q^* K_Y` is a `ℚ`-Cartier canonical
divisor of `Y_e`, and `Y_e` is a terminal variety. -/
@[mmp "lem_oai4_c2_etale_terminal"]
public theorem exists_isCanonicalDivisor_isPullback_and_isTerminalVariety
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) {b : ℕ}
    {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
    (E : LocalEtaleDatum sY T π L) [IsIntegral E.scheme] [IsLocallyNoetherian E.scheme]
    [IsNormal E.scheme] :
    (∀ (n : ℕ) (K : Divisor Y), K.IsCanonicalDivisor sY n →
      (Divisor.toQDivisor K).IsQCartier ∧
      ∃ (hK : ∀ Z : irreducibleComponents E.scheme,
          E.map (componentGenericPoint E.scheme Z) ∉ (Divisor.toQDivisor K).supp)
        (Ke : Divisor E.scheme),
        Ke.IsCanonicalDivisor (E.map ≫ sY) n ∧ (Divisor.toQDivisor Ke).IsQCartier ∧
          (Divisor.toQDivisor K).IsPullback E.map hK (Divisor.toQDivisor Ke)) ∧
    IsTerminalVariety (E.map ≫ sY) := by
  have hYn : IsNormalVariety ℂ sY := hY.isQFactorial.1
  have hYe : IsNormalVariety ℂ (E.map ≫ sY) := ⟨E.isQuasiProjectiveVariety.toIsVariety, ‹_›⟩
  have hqc : ∀ D : QDivisor Y, D.IsQCartier := isQCartier_of_isQFactorial sY hY.isQFactorial
  refine ⟨fun n K hK =>
    ⟨hqc _, Divisor.exists_isCanonicalDivisor_isPullback_of_etale hYn E.map hYe hK (hqc _)⟩, ?_⟩
  obtain ⟨⟨hΘ, hklt⟩, hterm⟩ := hY.isKltTerminalPair
  obtain ⟨-, n₀, K₀, hK₀, -⟩ := hΘ.isPair
  have hP₀ : MMP.Mori.IsPair sY 0 := ⟨hYn, n₀, K₀, hK₀, by rw [add_zero]; exact hqc _⟩
  obtain ⟨-, Ke, hKe, hKeq, -⟩ :=
    Divisor.exists_isCanonicalDivisor_isPullback_of_etale hYn E.map hYe hK₀ (hqc _)
  have hPe : MMP.Mori.IsPair (E.map ≫ sY) 0 := ⟨hYe, n₀, Ke, hKe, by rwa [add_zero]⟩
  refine ⟨⟨⟨inferInstance, inferInstance, hPe, fun _ => le_rfl⟩, fun n D a ha => ?_⟩,
    fun n D a hD ha => ?_⟩
  · obtain ⟨D₀, a', hle, ha', -⟩ :=
      exists_isLogDiscrepancy_le_of_etale hYn hY.isQFactorial.2 hP₀ hΘ.nonneg (hqc Θ) E.map hYe
        ha
    exact (hklt n D₀ a' ha').trans_le hle
  · obtain ⟨D₀, a', hle, ha', hex⟩ :=
      exists_isLogDiscrepancy_le_of_etale hYn hY.isQFactorial.2 hP₀ hΘ.nonneg (hqc Θ) E.map hYe
        ha
    exact (hterm n D₀ a' (hex hD) ha').trans_le hle

end

end MMP.Fourfold.LocalEtaleDatum
