module
public import MMP.AlgebraicGeometry.Resolution.Blowup
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction

/-!
# Floor sections under an effective exceptional comparison

Let `φ : X ⟶ Y` be a proper birational morphism of normal varieties over a field `k`, both lying
over a scheme `Z` by `g_X = φ ≫ g_Y`, and let `D_X`, `D_Y` be `ℚ`-Cartier `ℚ`-divisors with
`D_X = φ^*D_Y + E` for an effective `φ`-exceptional `ℚ`-divisor `E`. Then for every open
`V ⊆ Z` and every `m ≥ 0`, a rational function `g ∈ k(Y)` is a section of `𝒪_Y(⌊mD_Y⌋)` over
`g_Y⁻¹(V)` exactly when its pull-back `φ^*g ∈ k(X)` is a section of `𝒪_X(⌊mD_X⌋)` over
`g_X⁻¹(V)`. Since `φ^* : k(Y) → k(X)` is a ring isomorphism
(`MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective`), it identifies the relative
floor-section algebras `⊕_{m ≥ 0} g_{Y*}𝒪_Y(⌊mD_Y⌋)` and `⊕_{m ≥ 0} g_{X*}𝒪_X(⌊mD_X⌋)` over `Z`,
degree by degree and over every open of `Z`.

## Main results

* `MMP.Mori.mem_divisorialSubmodule_roundDown_iff_of_eq_pullback_add`

## Implementation notes

The degree-`m` piece of the floor-section algebra over `V ⊆ Z` is the submodule
`MMP.Mori.Divisor.divisorialSubmodule` of `⌊mD⌋` over the preimage of `V`, inside the rational
functions `MMP.Mori.rationalFunctionsPresheaf` over that open. A function `g ∈ k(Y)` is read there
as the restriction of the global rational function corresponding to `g`, and `φ^*g` is
`AlgebraicGeometry.functionFieldMap φ g`. Stating the comparison on each graded piece, for the
ring isomorphism `φ^*`, is the identification of the graded algebras: multiplication is the
product of rational functions on both sides.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

section RationalFunctionsAux

variable {X : Scheme.{u}} [IsIntegral X]

private theorem germ_eq_rationalFunctionsEquivFunctionField_symm (U : X.Opens) (s : Γ(X, U))
    (h : genericPoint X ∈ U) (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U) :
    (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s) Z =
      X.presheaf.germ U (componentGenericPoint X Z) hZ s := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  let D : Stacks.Chow.DenseOpen X := ⟨U, U.isOpen.dense ⟨_, h⟩⟩
  have key : (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s)
      = (Stacks.Chow.rationalFunctionsEquivStalks X).1 (Stacks.Chow.ofSection X D s) := by
    rw [RingEquiv.symm_apply_eq, ← (Stacks.Chow.rationalFunctionsEquivFunctionField X).2 D s h]
    change _ = (Stacks.Chow.rationalFunctionsEquivFunctionField X).1
      ((Stacks.Chow.rationalFunctionsEquivStalks X).1.symm _)
    rw [RingEquiv.symm_apply_apply]
  rw [key]
  exact (Stacks.Chow.rationalFunctionsEquivStalks X).2 D s Z hZ

private theorem componentGenericPoint_eq (Z : irreducibleComponents X) :
    componentGenericPoint X Z = genericPoint X := by
  have hZ : Z.1 = Set.univ := by
    simpa [irreducibleComponents_eq_singleton] using Z.2
  have h1 := isGenericPoint_componentGenericPoint X Z
  rw [hZ] at h1
  exact h1.eq (genericPoint_spec X)

private theorem stalkSpecializes_rationalFunctionsEquivFunctionField_symm
    (Z : irreducibleComponents X) (φ : X.functionField) :
    (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
        (Set.mem_univ (componentGenericPoint X Z)))).hom
      ((rationalFunctionsEquivFunctionField X).symm φ Z) = φ := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.germ_exist (x := genericPoint X) φ
  have hZ : componentGenericPoint X Z ∈ U := (componentGenericPoint_eq Z) ▸ hx
  rw [germ_eq_rationalFunctionsEquivFunctionField_symm U s hx Z hZ,
    TopCat.Presheaf.germ_stalkSpecializes_apply]

end RationalFunctionsAux

section ValuationAux

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

private theorem valuation_rationalFunctionsEquivFunctionField_symm (E : MMP.Mori.PrimeDivisor X)
    (φ : X.functionField) :
    E.valuation ((rationalFunctionsEquivFunctionField X).symm φ E.component) =
      X.ordHom E.genericPoint E.coheight_genericPoint φ := by
  set a := (rationalFunctionsEquivFunctionField X).symm φ E.component
  let ψ := (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
        (Set.mem_univ (componentGenericPoint X E.component)))).hom
  have hψ : ψ a = φ := stalkSpecializes_rationalFunctionsEquivFunctionField_symm _ φ
  letI := E.toComponent.hom.toAlgebra
  haveI := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  haveI : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  let alg1 := IsLocalization.algEquiv (nonZeroDivisors E.localRing)
    (X.presheaf.stalk (componentGenericPoint X E.component)) (FractionRing E.localRing)
  let Eq := (IsLocalization.algEquiv (nonZeroDivisors E.localRing) (FractionRing E.localRing)
    X.functionField).toRingEquiv
  have hEq : ∀ r : E.localRing, Eq (algebraMap E.localRing (FractionRing E.localRing) r) =
      algebraMap E.localRing X.functionField (RingEquiv.refl E.localRing r) := fun r =>
    (IsLocalization.algEquiv (nonZeroDivisors E.localRing) (FractionRing E.localRing)
      X.functionField).commutes r
  have hcomp : Eq (alg1 a) = φ := by
    rw [← hψ]
    have : (Eq.toRingHom.comp alg1.toRingEquiv.toRingHom) = ψ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors E.localRing) ?_
      ext r
      simp only [RingHom.comp_apply]
      change Eq (alg1 (algebraMap _ _ r)) = _
      rw [AlgEquiv.commutes, hEq]
      change _ = ψ ((X.presheaf.stalkSpecializes E.specializes_genericPoint).hom r)
      simp only [ψ]
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    exact congrArg (fun f => f a) this
  change Ring.ordFrac E.localRing (alg1 a) = Ring.ordFrac E.localRing φ
  rw [← hcomp]
  exact (Stacks.Chow.ordFrac_congr (RingEquiv.refl E.localRing) Eq hEq (alg1 a)).symm

private theorem ordGE_iff (E : MMP.Mori.PrimeDivisor X) (n : ℤ) (φ : X.functionField) :
    E.OrdGE n ((rationalFunctionsEquivFunctionField X).symm φ E.component) ↔
      φ = 0 ∨ n ≤ X.ord φ E.genericPoint := by
  unfold MMP.Mori.PrimeDivisor.OrdGE
  rw [valuation_rationalFunctionsEquivFunctionField_symm]
  have h0 : (rationalFunctionsEquivFunctionField X).symm φ E.component = 0 ↔ φ = 0 :=
    ⟨fun h => by
      rw [← stalkSpecializes_rationalFunctionsEquivFunctionField_symm E.component φ, h, map_zero],
     fun h => by simp [h]⟩
  rw [h0]
  by_cases hφ : φ = 0
  · simp [hφ]
  · simp only [hφ, false_or]
    rw [(Scheme.ord_eq_iff E.coheight_genericPoint hφ).mp rfl]
    exact WithZero.exp_le_exp

end ValuationAux

/-- On a normal integral scheme, a rational function `g` is a section of `𝒪_X(D)` over `U` exactly
when `ord_E g ≥ -d_E` for every prime divisor `E` meeting `U`. -/
private theorem mem_divisorialSubmodule_iff {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X) (U : X.Opens) (g : X.functionField) :
    (rationalFunctionsPresheaf X).map (homOfLE le_top : U ⟶ ⊤).op
        ((rationalFunctionsPresheafTopEquiv X).symm
          ((rationalFunctionsEquivFunctionField X).symm g))
        ∈ D.divisorialSubmodule U ↔
      ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ U).Nonempty →
        g = 0 ∨ -D.coeff E ≤ X.ord g E.genericPoint :=
  forall₂_congr fun E _ => ordGE_iff E _ g

/-- An element of the local ring at a point of codimension one has nonnegative order there. -/
private theorem ord_algebraMap_nonneg {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {x : X} (hx : Order.coheight x = 1) (a : X.presheaf.stalk x)
    (ha : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  rw [Scheme.le_ord_iff hx ha]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  change _ ≤ Ring.ordFrac (X.presheaf.stalk x) _
  rw [Ring.ordFrac_eq_ord _ ha0]
  have hnz : a ∈ nonZeroDivisors (X.presheaf.stalk x) := mem_nonZeroDivisors_of_ne_zero ha0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hnz, if_true,
    ← hn]
  simp only [ENat.recTopCoe_coe, WithZero.one_le_coe]
  exact WithZero.coe_le_coe.mpr (Multiplicative.ofAdd_le.mpr (by exact_mod_cast Nat.zero_le n))

/-- **Pull-back of a function regular near the image.** If `h ∈ k(Y)` has nonnegative order along
every prime divisor meeting an open `W ∋ φ(η_F)`, then `φ^*h` has nonnegative order along `F`:
by algebraic Hartogs `h` lies in `𝒪_{Y,φ(η_F)}`, so `φ^*h` lies in `𝒪_{X,η_F}`. -/
private theorem ord_functionFieldMap_nonneg {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (φ : X ⟶ Y) [IsDominant φ] (F : MMP.Mori.PrimeDivisor X) (W : Y.Opens)
    (hW : φ F.genericPoint ∈ W) (h : Y.functionField)
    (hpos : ∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ W).Nonempty →
      h = 0 ∨ 0 ≤ Y.ord h P.genericPoint) :
    functionFieldMap φ h = 0 ∨ 0 ≤ X.ord (functionFieldMap φ h) F.genericPoint := by
  have hsec := (mem_divisorialSubmodule_iff (0 : Divisor Y) W h).mpr fun P hP => by
    simpa only [DivisorWithCoeffs.coeff_zero, neg_zero] using hpos P hP
  obtain ⟨Z, hyZ⟩ := exists_mem_irreducibleComponents (φ F.genericPoint)
  obtain ⟨r, hr⟩ := MMP.Mori.Divisor.IsDivisorialSection.exists_stalk_eq hsec hW hyZ
  have hh : algebraMap (Y.presheaf.stalk (φ F.genericPoint)) Y.functionField r = h := by
    rw [← algebraMap_stalkSpecializes
      ((isGenericPoint_componentGenericPoint Y Z).specializes hyZ) r]
    change (Y.presheaf.stalkSpecializes _).hom ((stalkToRationalFunctions Y hyZ).hom r) = h
    rw [hr]
    exact stalkSpecializes_rationalFunctionsEquivFunctionField_symm Z h
  rw [← hh, functionFieldMap_algebraMap_stalk]
  by_cases h0 : algebraMap (X.presheaf.stalk F.genericPoint) X.functionField
      ((φ.stalkMap F.genericPoint).hom r) = 0
  · exact Or.inl h0
  · exact Or.inr (ord_algebraMap_nonneg F.coheight_genericPoint _ h0)

/-- The valuation along `F` of a nonzero element `c` of the stalk at the generic point is the
order along `F` of the rational function `c` represents. -/
private theorem valuation_eq_exp_ord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (F : MMP.Mori.PrimeDivisor X)
    (c : X.presheaf.stalk (componentGenericPoint X F.component)) (χ : X.functionField)
    (hc : (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
      (Set.mem_univ (componentGenericPoint X F.component)))).hom c = χ) (hχ : χ ≠ 0) :
    F.valuation c = WithZero.exp (X.ord χ F.genericPoint) := by
  letI := (RationalFunctions.isField_stalk X F.component).toField
  have hcχ : c = (rationalFunctionsEquivFunctionField X).symm χ F.component :=
    RingHom.injective (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
      (Set.mem_univ (componentGenericPoint X F.component)))).hom
      (hc.trans (stalkSpecializes_rationalFunctionsEquivFunctionField_symm _ χ).symm)
  rw [hcχ, valuation_rationalFunctionsEquivFunctionField_symm,
    (Scheme.ord_eq_iff F.coheight_genericPoint hχ).mp rfl]
  rfl

/-- The order of a unit of `K(Y)` along a prime divisor is that of the rational function. -/
private theorem ord_eq_ord_rationalFunctionsEquivFunctionField {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : MMP.Mori.PrimeDivisor Y)
    (ψ : (RationalFunctions Y)ˣ) :
    P.ord ψ = Y.ord (rationalFunctionsEquivFunctionField Y ψ) P.genericPoint := by
  have hψ : rationalFunctionsEquivFunctionField Y ψ ≠ 0 :=
    (ψ.isUnit.map (rationalFunctionsEquivFunctionField Y)).ne_zero
  have h := valuation_eq_exp_ord P ((ψ : RationalFunctions Y) P.component) _ (by
    have := stalkSpecializes_rationalFunctionsEquivFunctionField_symm P.component
      (rationalFunctionsEquivFunctionField Y ψ)
    rwa [RingEquiv.symm_apply_apply] at this) hψ
  rw [P.valuation_component] at h
  exact WithZero.exp_injective h

/-- The coefficient along `F` of the pull-back of a Cartier divisor with local equation `ψ` near
`φ(η_F)` is the order of `φ^*ψ` along `F`. -/
private theorem coeff_eq_ord_of_isPullback {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (φ : X ⟶ Y) [IsDominant φ] {B : Divisor Y}
    {hB : ∀ Z : irreducibleComponents X, φ (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback φ hB B') {U : Y.Opens} {ψ : (RationalFunctions Y)ˣ}
    (hψ : B.IsLocalEquation U ψ) (F : MMP.Mori.PrimeDivisor X) (hF : φ F.genericPoint ∈ U) :
    B'.coeff F =
      X.ord (functionFieldMap φ (rationalFunctionsEquivFunctionField Y ψ)) F.genericPoint := by
  have hFU : (F.support ∩ φ ⁻¹ᵁ U).Nonempty := (F.genericPoint_mem_iff (φ ⁻¹ᵁ U)).mp hF
  rw [h U ψ hψ F hFU]
  obtain ⟨W, hW⟩ := exists_mem_irreducibleComponents (φ (componentGenericPoint X F.component))
  have hmem := F.map_componentGenericPoint_mem φ hFU
  obtain ⟨a, ha⟩ := hψ.exists_unit_stalk hmem (hB _) hW
  rw [pullbackComponent_eq hB hψ hmem hW a ha]
  set χ := functionFieldMap φ (rationalFunctionsEquivFunctionField Y ψ)
  have hχ : χ ≠ 0 := (map_ne_zero_iff _ (functionFieldMap φ).injective).mpr
    (ψ.isUnit.map (rationalFunctionsEquivFunctionField Y)).ne_zero
  have h1 := F.valuation_eq_exp_ordUnit
    (Units.map (φ.stalkMap (componentGenericPoint X F.component)).hom.toMonoidHom a)
  rw [valuation_eq_exp_ord F _ χ ?_ hχ] at h1
  · exact (WithZero.exp_injective h1).symm
  change algebraMap (X.presheaf.stalk (componentGenericPoint X F.component)) X.functionField
    ((φ.stalkMap _).hom a) = χ
  rw [← functionFieldMap_algebraMap_stalk, ← algebraMap_stalkSpecializes
    ((isGenericPoint_componentGenericPoint Y W).specializes hW)]
  change functionFieldMap φ ((Y.presheaf.stalkSpecializes _).hom
    ((stalkToRationalFunctions Y hW).hom a)) = χ
  rw [ha]
  have := stalkSpecializes_rationalFunctionsEquivFunctionField_symm W
    (rationalFunctionsEquivFunctionField Y ψ)
  rw [RingEquiv.symm_apply_apply] at this
  rw [this]

/-- Proper birational morphisms of varieties preserve dimension. -/
private theorem topologicalKrullDim_eq_of_isBirationalMorphism
    {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (φ : X ⟶ Y) [IsDominant φ] (hφ : IsBirationalMorphism φ) (hφk : φ ≫ sY = sX) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  subst hφk
  rw [← toENat_trdeg_functionField (sX := φ ≫ sY), ← toENat_trdeg_functionField (sX := sY),
    trdeg_functionField_eq_of_bijective sY φ hφ.functionFieldMap_bijective]

/-- A prime divisor of `X` whose generic point maps to that of a prime divisor of `Y` is not in
the support of a `φ`-exceptional divisor. -/
private theorem coeff_eq_zero_of_isExceptionalDivisorFor
    {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (φ : X ⟶ Y) [IsDominant φ] (hφ : IsBirationalMorphism φ) (hφk : φ ≫ sY = sX)
    {E : QDivisor X} (hEx : MMP.Resolution.IsExceptionalDivisorFor φ E)
    (F : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor Y)
    (heq : φ F.genericPoint = P.genericPoint) :
    E F = 0 := by
  by_contra h
  have hlt := hEx F (Finsupp.mem_support_iff.mpr h)
  have himg : closure (φ.base '' F.support) = P.support := by
    have key : ∀ x : X, closure (φ.base '' closure {x}) = closure {φ x} := by
      intro x
      apply le_antisymm
      · refine closure_minimal
          ((image_closure_subset_closure_image φ.base.hom.continuous).trans ?_) isClosed_closure
        rw [Set.image_singleton]
      · exact closure_mono (by rw [← Set.image_singleton]; exact Set.image_mono subset_closure)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure, key]
    exact congrArg (fun y => closure {y}) heq
  rw [himg, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hlt
  have hX := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX F.genericPoint
  have hY := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hX
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
    ← topologicalKrullDim_eq_of_isBirationalMorphism sX sY φ hφ hφk, ← hX] at hY
  generalize topologicalKrullDim (closure {P.genericPoint} : Set Y) = a at hlt hY
  generalize topologicalKrullDim (closure {F.genericPoint} : Set X) = b at hlt hY
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => exact lt_irrefl _ hlt
    | coe b =>
      simp at hY
      exact absurd hY.symm WithBot.coe_ne_bot
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp at hlt
    | coe b =>
      have hY' : a + 1 = b + 1 := by exact_mod_cast hY
      have hlt' : a < b := by exact_mod_cast hlt
      exact hlt'.ne (WithTop.add_right_cancel ENat.one_ne_top hY')

private theorem natCast_mul_add_natCast_mul_nonneg_of_neg_floor_le {N m : ℕ} (hN : 0 < N)
    {q : ℚ} {a b : ℤ} (ha : -⌊(m : ℚ) * q⌋ ≤ a) (hb : (b : ℚ) = N * q) :
    0 ≤ (N : ℤ) * a + m * b := by
  have h1 : ((-a : ℤ) : ℚ) ≤ m * q := (Int.cast_le.mpr (neg_le.mp ha)).trans (Int.floor_le _)
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  have : (0 : ℚ) ≤ N * a + m * b := by
    push_cast at h1
    rw [hb]
    nlinarith
  exact_mod_cast this

private theorem neg_le_natCast_mul_add_of_nonneg {N m : ℕ} (hN : 0 < N) {a b : ℤ} {p e : ℚ}
    (he : 0 ≤ e) (hab : 0 ≤ (N : ℤ) * a + m * b) (hb : (b : ℚ) = N * p) :
    ((-a : ℤ) : ℚ) ≤ m * (p + e) := by
  have hq : (0 : ℚ) ≤ N * a + m * b := by exact_mod_cast hab
  rw [hb] at hq
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  have : (0 : ℚ) ≤ a + m * p := by nlinarith
  push_cast
  nlinarith [(m.cast_nonneg : (0 : ℚ) ≤ m)]

/-- Pull-back direction: a section of `𝒪_Y(⌊mD_Y⌋)` pulls back to one of `𝒪_X(⌊mD_X⌋)`. -/
private theorem mem_divisorialSubmodule_roundDown_of_eq_pullback_add
    {X Y Z : Scheme.{u}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (φ : X ⟶ Y) [IsDominant φ]
    {gX : X ⟶ Z} {gY : Y ⟶ Z} (hg : φ ≫ gY = gX)
    {DX : QDivisor X} {DY : QDivisor Y} (hDY : DY.IsQCartier)
    (hB : ∀ W : irreducibleComponents X, φ (componentGenericPoint X W) ∉ DY.supp)
    {E : QDivisor X} (hE : 0 ≤ E) (hD : DX = DY.pullback hDY hB + E)
    (V : Z.Opens) (m : ℕ) (g : Y.functionField)
    (h : (rationalFunctionsPresheaf Y).map (homOfLE le_top : gY ⁻¹ᵁ V ⟶ ⊤).op
        ((rationalFunctionsPresheafTopEquiv Y).symm
          ((rationalFunctionsEquivFunctionField Y).symm g))
        ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • DY)).divisorialSubmodule (gY ⁻¹ᵁ V)) :
      (rationalFunctionsPresheaf X).map (homOfLE le_top : gX ⁻¹ᵁ V ⟶ ⊤).op
          ((rationalFunctionsPresheafTopEquiv X).symm
            ((rationalFunctionsEquivFunctionField X).symm (functionFieldMap φ g)))
        ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • DX)).divisorialSubmodule (gX ⁻¹ᵁ V) := by
  rw [mem_divisorialSubmodule_iff] at h ⊢
  intro F hF
  by_cases hg0 : g = 0
  · exact Or.inl (by rw [hg0, map_zero])
  right
  have hN := QDivisor.cartierIndex_pos hDY
  set N := DY.cartierIndex hDY
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hDY
  obtain ⟨D', hD', hp⟩ := QDivisor.isPullback_pullback hDY hB N hN D₀ hD₀ hD₀c
  obtain ⟨U, hyU, ψ, hψ⟩ := hD₀c (φ F.genericPoint)
  have hyV : φ F.genericPoint ∈ gY ⁻¹ᵁ V := by
    subst hg
    exact (F.genericPoint_mem_iff _).mpr hF
  set ψf := rationalFunctionsEquivFunctionField Y ψ
  have hψf : ψf ≠ 0 := (ψ.isUnit.map (rationalFunctionsEquivFunctionField Y)).ne_zero
  have hgN : g ^ (N : ℤ) ≠ 0 := zpow_ne_zero _ hg0
  have hψm : ψf ^ (m : ℤ) ≠ 0 := zpow_ne_zero _ hψf
  have key := ord_functionFieldMap_nonneg φ F (U ⊓ gY ⁻¹ᵁ V) ⟨hyU, hyV⟩
    (g ^ (N : ℤ) * ψf ^ (m : ℤ)) fun P hP => by
      right
      have hψP := hψ P (hP.mono fun _ h => ⟨h.1, h.2.1⟩)
      rw [ord_eq_ord_rationalFunctionsEquivFunctionField] at hψP
      have hcP := congrArg (fun G : QDivisor Y => G P) hD₀
      simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at hcP
      rcases h P (hP.mono fun _ h => ⟨h.1, h.2.2⟩) with h0 | hle
      · exact absurd h0 hg0
      rw [Scheme.ord_mul hgN hψm, MMP.Mori.ord_zpow _ hg0, MMP.Mori.ord_zpow _ hψf]
      rw [DivisorWithCoeffs.coeff_roundDown] at hle
      simp only [DivisorWithCoeffs.coeff, Finsupp.smul_apply, smul_eq_mul] at hle
      have hψP' : ((D₀.coeff P : ℤ) : ℚ) = N * DY P := hcP
      rw [hψP] at hψP'
      exact natCast_mul_add_natCast_mul_nonneg_of_neg_floor_le hN hle hψP'
  rcases key with h0 | hle
  · exact absurd h0 (map_ne_zero _ |>.mpr (mul_ne_zero hgN hψm))
  rw [map_mul, map_zpow₀, map_zpow₀, Scheme.ord_mul (zpow_ne_zero _ ((map_ne_zero _).mpr hg0))
    (zpow_ne_zero _ ((map_ne_zero _).mpr hψf)), MMP.Mori.ord_zpow _ ((map_ne_zero _).mpr hg0),
    MMP.Mori.ord_zpow _ ((map_ne_zero _).mpr hψf),
    ← coeff_eq_ord_of_isPullback φ hp hψ F hyU] at hle
  have hcF := congrArg (fun G : QDivisor X => G F) hD'
  simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at hcF
  rw [DivisorWithCoeffs.coeff_roundDown, neg_le, Int.le_floor]
  simp only [DivisorWithCoeffs.coeff, Finsupp.smul_apply, smul_eq_mul, hD, Finsupp.add_apply]
  exact neg_le_natCast_mul_add_of_nonneg hN (hE F) hle hcF

/-- Push-forward direction: if `φ^*g` is a section of `𝒪_X(⌊mD_X⌋)` then `g` is a section of
`𝒪_Y(⌊mD_Y⌋)`. -/
private theorem mem_divisorialSubmodule_roundDown_of_functionFieldMap_mem
    {k : Type u} [Field k] {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    {φ : X ⟶ Y} [IsDominant φ] [IsProper φ] (hφ : IsBirationalMorphism φ) (hφk : φ ≫ sY = sX)
    {gX : X ⟶ Z} {gY : Y ⟶ Z} (hg : φ ≫ gY = gX)
    {DX : QDivisor X} {DY : QDivisor Y} (hDY : DY.IsQCartier)
    (hB : ∀ W : irreducibleComponents X, φ (componentGenericPoint X W) ∉ DY.supp)
    {E : QDivisor X} (hEx : MMP.Resolution.IsExceptionalDivisorFor φ E)
    (hD : DX = DY.pullback hDY hB + E)
    (V : Z.Opens) (m : ℕ) (g : Y.functionField)
    (h : (rationalFunctionsPresheaf X).map (homOfLE le_top : gX ⁻¹ᵁ V ⟶ ⊤).op
          ((rationalFunctionsPresheafTopEquiv X).symm
            ((rationalFunctionsEquivFunctionField X).symm (functionFieldMap φ g)))
        ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • DX)).divisorialSubmodule (gX ⁻¹ᵁ V)) :
    (rationalFunctionsPresheaf Y).map (homOfLE le_top : gY ⁻¹ᵁ V ⟶ ⊤).op
        ((rationalFunctionsPresheafTopEquiv Y).symm
          ((rationalFunctionsEquivFunctionField Y).symm g))
        ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • DY)).divisorialSubmodule (gY ⁻¹ᵁ V) := by
  have := hY.1
  have hX' : IsNormalVariety k (φ ≫ sY) := hφk ▸ hX
  have := hX.1
  rw [mem_divisorialSubmodule_iff] at h ⊢
  intro P hP
  obtain ⟨F, heq, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX' hφ P
  have hPV : P.genericPoint ∈ gY ⁻¹ᵁ V := (P.genericPoint_mem_iff _).mpr hP
  have hFV : (F.support ∩ gX ⁻¹ᵁ V).Nonempty := by
    refine (F.genericPoint_mem_iff _).mp ?_
    subst hg
    change gY (φ F.genericPoint) ∈ V
    rw [heq]
    exact hPV
  have hcoeff : DX F = DY P := by
    have h1 := MMP.Positivity.transformDivisor_of_isPullback hY hX' hφ hDY hB
      (MMP.Mori.QDivisor.isPullback_pullback hDY hB)
    have h2 := congrArg (fun D : QDivisor Y => D P) h1
    rw [htr (R := ℚ)] at h2
    rw [hD, Finsupp.add_apply, h2,
      coeff_eq_zero_of_isExceptionalDivisorFor sX sY φ hφ hφk hEx F P heq, add_zero]
  rcases h F hFV with h0 | hle
  · left
    exact (map_eq_zero_iff _ (functionFieldMap φ).injective).mp h0
  · right
    rw [MMP.Positivity.ord_functionFieldMap_of_isIso φ F P heq g] at hle
    rw [DivisorWithCoeffs.coeff_roundDown] at hle ⊢
    simpa only [DivisorWithCoeffs.coeff, Finsupp.smul_apply, smul_eq_mul, hcoeff] using hle

/-- **Floor sections under an effective exceptional comparison.** Let `φ : X ⟶ Y` be a proper
birational morphism of normal varieties over `k`, with `g_X = φ ≫ g_Y` over a scheme `Z`, and let
`D_X = φ^*D_Y + E` for `ℚ`-Cartier `D_X`, `D_Y` and an effective `φ`-exceptional `E`. For every
open `V ⊆ Z`, every `m ≥ 0` and every `g ∈ k(Y)`, `g` is a section of `𝒪_Y(⌊mD_Y⌋)` over
`g_Y⁻¹(V)` if and only if `φ^*g` is a section of `𝒪_X(⌊mD_X⌋)` over `g_X⁻¹(V)`. -/
@[mmp "lem_mmp_surface_floor_sections_under_contraction"]
public theorem mem_divisorialSubmodule_roundDown_iff_of_eq_pullback_add
    {k : Type u} [Field k] {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (φ : X ⟶ Y) [IsDominant φ] [IsProper φ] (hφ : IsBirationalMorphism φ) (hφk : φ ≫ sY = sX)
    (gX : X ⟶ Z) (gY : Y ⟶ Z) (hg : φ ≫ gY = gX)
    (DX : QDivisor X) (DY : QDivisor Y) (hDX : DX.IsQCartier) (hDY : DY.IsQCartier)
    (hB : ∀ W : irreducibleComponents X, φ (componentGenericPoint X W) ∉ DY.supp)
    (E : QDivisor X) (hE : 0 ≤ E) (hEx : MMP.Resolution.IsExceptionalDivisorFor φ E)
    (hD : DX = DY.pullback hDY hB + E)
    (V : Z.Opens) (m : ℕ) (g : Y.functionField) :
    (rationalFunctionsPresheaf Y).map (homOfLE le_top : gY ⁻¹ᵁ V ⟶ ⊤).op
        ((rationalFunctionsPresheafTopEquiv Y).symm
          ((rationalFunctionsEquivFunctionField Y).symm g))
        ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • DY)).divisorialSubmodule (gY ⁻¹ᵁ V) ↔
      (rationalFunctionsPresheaf X).map (homOfLE le_top : gX ⁻¹ᵁ V ⟶ ⊤).op
          ((rationalFunctionsPresheafTopEquiv X).symm
            ((rationalFunctionsEquivFunctionField X).symm (functionFieldMap φ g)))
        ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • DX)).divisorialSubmodule (gX ⁻¹ᵁ V) :=
  ⟨mem_divisorialSubmodule_roundDown_of_eq_pullback_add φ hg hDY hB hE hD V m g,
    mem_divisorialSubmodule_roundDown_of_functionFieldMap_mem hX hY hφ hφk hg hDY hB hEx hD V m g⟩

end MMP.Mori

end
