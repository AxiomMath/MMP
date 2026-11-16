module
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison

/-!
# Crepant boundaries and push-forwards along proper birational morphisms

Let `f : Y ⟶ X` be a proper birational morphism of normal varieties over a perfect field `k`.
This file compares divisorial data on `Y` with divisorial data on `X` along `f`.

Let `(X, Δ)` be a pair, `ω ≠ 0` a rational top form on `X` and `K_X = div(ω)`, and put
`K_Y = div(f^*ω)`. A `ℚ`-divisor `Δ_Y` on `Y` is the crepant boundary of `(X, Δ)` on `Y` if and
only if `f^*(K_X + Δ) = K_Y + Δ_Y` as `ℚ`-divisors: comparing the discrepancy `a(F, X, Δ)` of a
prime divisor `F` of `Y` with the log discrepancy `1 + coeff_F(K_Y - f^*(K_X + Δ))` gives
`a(F, X, Δ) = coeff_F(K_Y) - coeff_F(f^*(K_X + Δ))`.

Let `D_Y` be a divisor on `Y` and `D = f_* D_Y` its birational transform. Identifying the
function fields `k(X) ≅ k(Y)` by `f^*`, the sheaves `f_* ω_Y(D_Y)` and `f_* 𝒪_Y(D_Y)` become
subsheaves of the constant sheaves `Ω^n_{k(X)}` and `k(X)`, and then `f_* ω_Y(D_Y) ⊆ ω_X(D)` and
`f_* 𝒪_Y(D_Y) ⊆ 𝒪_X(D)`. If `D_Y` is effective and `f`-exceptional, then `D = 0` and
`f_* 𝒪_Y(D_Y) = 𝒪_X`. Both follow from the existence, for every prime divisor `P` of `X`, of a
strict transform `E` on `Y` with `f(η_E) = η_P` at which `f^♯ : 𝒪_{X,P} ⟶ 𝒪_{Y,E}` is an
isomorphism.

## Main results

* `MMP.Mori.isCrepantBoundary_iff_isPullback_topFormDivisor_add`: `Δ_Y` is the crepant boundary
  if and only if `f^*(K_X + Δ) = K_Y + Δ_Y`.
* `MMP.Mori.pushforward_divisorialSheaf_le`: `f_* ω_Y(D_Y) ⊆ ω_X(f_* D_Y)`,
  `f_* 𝒪_Y(D_Y) ⊆ 𝒪_X(f_* D_Y)`, and `f_* 𝒪_Y(D_Y) = 𝒪_X` for `D_Y` effective and
  `f`-exceptional.

## Implementation notes

The canonical divisor `K_X` is `MMP.Mori.topFormDivisor sX ω`, and `K_Y` is the divisor
`MMP.Mori.divisorOfForm` of the pull-back `MMP.Mori.pullbackRationalPluriForms sX f ω` of `ω`,
regarded as a `1`-canonical form, along the extension of function fields `f^* : k(X) → k(Y)`.
The pull-back of the `ℚ`-Cartier `ℚ`-divisor `K_X + Δ` is expressed by the characterising
predicate `MMP.Mori.QDivisor.IsPullback`; its condition `(∗)`, that `f` maps the generic point of
`Y` outside `Supp(K_X + Δ)`, holds since `f` is dominant, and the right-hand side is stated for
every proof of it.

The sheaf inclusions are stated section by section, over every open `U ⊆ X`, inside the rational
forms and rational functions of `X`. A rational `n`-form `τ` on `X` is a section of
`f_* ω_Y(D_Y)` over `U` when its pull-back `f^*τ` is a section of `ω_Y(D_Y)` over `f⁻¹(U)`, and
a rational function `ψ ∈ k(X)` is a section of `f_* 𝒪_Y(D_Y)` over `U` when `f^*ψ` is a section
of `𝒪_Y(D_Y)` over `f⁻¹(U)`. Since `f^*` is an isomorphism of function fields, every section of
`f_* ω_Y(D_Y)` and of `f_* 𝒪_Y(D_Y)` is of this form. The sections of `ω_X(D)`
(`MMP.Mori.twistedCanonicalSheaf`) over `U` are `MMP.Mori.pluricanonicalSections sX n 1 D U`,
and those of `𝒪_X(D)` (`MMP.Mori.Divisor.divisorialSheaf`) are the `φ` with
`D.IsDivisorialSection U φ`. The structure sheaf `𝒪_X` is `𝒪_X(0)` inside `𝒦_X`, by algebraic
Hartogs (`MMP.Mori.Divisor.IsDivisorialSection.exists_eq`).

The base field is perfect; the source works in characteristic zero. Then a normal variety is
smooth at the generic point of every prime divisor, so the order of a form along a prime divisor
is multiplicative. Over an imperfect field `Ω_{k(X)/k}` may have rank larger than `dim X` (for
`k = 𝔽_p(t)` and `X = 𝔸^1_{k(t^{1/p})}` it has rank `2`), the sheaf of top forms is then not
invertible at the generic point, and the first inclusion fails.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.25, 2.26,
  5.30, 5.36, 5.48, 5.51
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-! ### The crepant boundary and rational top forms -/

/-- A nonzero rational top form is nonzero as a `1`-canonical form. -/
private theorem toPluriForms_ne_zero {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {ω : RationalTopForms sX n} (hω : ω ≠ 0) :
    ω.toPluriForms sX ≠ 0 := by
  letI := functionFieldAlgebra sX
  intro h
  apply hω
  have h' : (PiTensorProduct.tprod X.functionField
      fun _ : Fin 1 => (ω : ⋀[X.functionField]^n Ω[X.functionField⁄k])) = 0 := h
  have h'' := congrArg (PiTensorProduct.subsingletonEquiv (0 : Fin 1)) h'
  rwa [PiTensorProduct.subsingletonEquiv_apply_tprod, map_zero] at h''

/-- The divisor of a nonzero rational top form is linearly equivalent to every canonical
divisor. -/
private theorem linearlyEquivalent_topFormDivisor {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {ω : RationalTopForms sX n} (hω : ω ≠ 0) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) : (topFormDivisor sX ω).LinearlyEquivalent K := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  obtain ⟨ω₀, hω₀0, hω₀⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hω0 := toPluriForms_ne_zero hω
  set c := (ZTensorPower.basis b 1).repr (ω.toPluriForms sX) () with hc_def
  set c₀ := (ZTensorPower.basis b 1).repr ω₀ () with hc₀_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hc₀ : c₀ ≠ 0 := repr_ne_zero_of_ne_zero b hω₀0
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero hc (inv_ne_zero hc₀))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 _ hω0
  have e2 := hN 1 ω₀ hω₀0
  rw [← hc_def] at e1
  rw [← hc₀_def, hω₀ Γ] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul hc (inv_ne_zero hc₀), ← zpow_neg_one, ord_zpow _ hc₀, coeff_topFormDivisor]
  omega

/-- **The discrepancy is read off the pull-back.** If `a` is the discrepancy of a prime divisor
`F` of `Y` over `(X, Δ)`, computed with `K_X = div(ω)`, and `B'` is the pull-back of `K_X + Δ`,
then `a = coeff_F(K_Y) - coeff_F(B')` for `K_Y = div(f^*ω)`. -/
private theorem isDiscrepancy_eq_coeff_sub {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {Δ : QDivisor X} {n : ℕ} {ω : RationalTopForms sX n}
    (hω : ω ≠ 0) {f : Y ⟶ X} [IsProper f] [IsDominant f] {hY : IsNormalVariety k (f ≫ sX)}
    {hf : IsBirationalMorphism f} {F : MMP.Mori.PrimeDivisor Y} {a : ℚ}
    (ha : IsDiscrepancy sX n (topFormDivisor sX ω) Δ ⟨Y, f, hY, hf, F⟩ a)
    {hB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor (topFormDivisor sX ω) + Δ).supp}
    {B' : QDivisor Y} (hB' : (Divisor.toQDivisor (topFormDivisor sX ω) + Δ).IsPullback f hB B') :
    a = (divisorOfForm (pullbackRationalPluriForms sX f (ω.toPluriForms sX))).coeff F -
      B'.coeff F := by
  obtain ⟨hX, hK, m, hm, ⟨M, hM, hMc⟩, -⟩ := id ha
  obtain ⟨M', hM'B, hM'⟩ := hB' m hm M hM hMc
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  let D : DivisorOver k sX := ⟨Y, f, hY, hf, F⟩
  have hb : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) D
      (1 + (D.ordPullback (ω.toPluriForms sX) : ℝ) -
        ∑ _i : Fin 1, (1 / (m : ℝ)) * (M'.coeff F : ℝ)) := by
    refine ⟨hX, ‹IsProper f›, ω.toPluriForms sX, toPluriForms_ne_zero hω,
      ⟨_, hK, fun Γ => rfl⟩, 1, fun _ => 1 / (m : ℝ), fun _ => M, fun _ => M', fun _ => hMc,
      fun Γ => ?_, fun _ => ⟨_, hM'⟩, rfl⟩
    have hMΓ : (M.coeff Γ : ℝ) = m * ((Γ.ordForm (ω.toPluriForms sX) : ℝ) + Δ.coeff Γ) := by
      have := congrArg (fun G : QDivisor X => G.coeff Γ) hM
      simp at this
      exact_mod_cast (by linear_combination this :
        (M.coeff Γ : ℚ) = m * ((Γ.ordForm (ω.toPluriForms sX) : ℚ) + Δ.coeff Γ))
    rw [QDivisor.coeff_toRDivisor, Fin.sum_univ_one, hMΓ]
    field_simp
  have e := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha hb
  have hM'F : (M'.coeff F : ℝ) = m * (B'.coeff F : ℝ) := by
    have := congrArg (fun G : QDivisor Y => G.coeff F) hM'B
    simp at this
    exact_mod_cast (by linear_combination this : (M'.coeff F : ℚ) = m * B'.coeff F)
  have hP : D.ordPullback (ω.toPluriForms sX) =
      (divisorOfForm (pullbackRationalPluriForms sX f (ω.toPluriForms sX))).coeff F := rfl
  rw [Fin.sum_univ_one, hM'F, hP] at e
  field_simp at e
  have : (a : ℝ) = (((divisorOfForm (pullbackRationalPluriForms sX f (ω.toPluriForms sX))).coeff F
      : ℚ) : ℝ) - (B'.coeff F : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

/-- **The crepant boundary and rational forms.** Let `(X, Δ)` be a pair over a perfect field `k`,
`ω ≠ 0` a rational top form on `X` (of degree `n = dim X`), and `K_X = div(ω)`. Let `f : Y ⟶ X`
be a proper birational morphism from a normal variety `Y` and `K_Y = div(f^*ω)`. Then a
`ℚ`-divisor `Δ_Y` on `Y` is the crepant boundary of `(X, Δ)` on `Y` with respect to `K_X`
(`MMP.Mori.IsCrepantBoundary`) if and only if `f^*(K_X + Δ) = K_Y + Δ_Y` as `ℚ`-divisors. -/
@[mmp "lem_km5b_crepant_boundary_of_form"]
public theorem isCrepantBoundary_iff_isPullback_topFormDivisor_add {k : Type u} [Field k]
    [PerfectField k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {Δ : QDivisor X} (hΔ : IsPair sX Δ) {n : ℕ} (hn : topologicalKrullDim X = n)
    (ω : RationalTopForms sX n) (hω : ω ≠ 0)
    (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (ΔY : QDivisor Y) :
    haveI := hf.isDominant
    IsCrepantBoundary sX n (topFormDivisor sX ω) Δ f hY hf ΔY ↔
      ∀ hB : ∀ Z : irreducibleComponents Y,
          f (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor (topFormDivisor sX ω) + Δ).supp,
        (Divisor.toQDivisor (topFormDivisor sX ω) + Δ).IsPullback f hB
          (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX f (ω.toPluriForms sX)))
            + ΔY) := by
  haveI := hf.isDominant
  obtain ⟨hX, n', K₀, hK₀, hQ⟩ := hΔ
  obtain rfl : n' = n := by exact_mod_cast hK₀.topologicalKrullDim_eq.symm.trans hn
  have hlin := linearlyEquivalent_topFormDivisor hX hn hω hK₀
  have hK : (topFormDivisor sX ω).IsCanonicalDivisor sX n' := hK₀.of_linearlyEquivalent hlin
  have hQK : (Divisor.toQDivisor (topFormDivisor sX ω) + Δ).IsQCartier :=
    hQ.add_of_linearlyEquivalent hlin.symm
  refine ⟨fun hC hB => ?_, fun h F => ?_⟩
  · have hpb := QDivisor.isPullback_pullback hQK hB
    have heq : (Divisor.toQDivisor (topFormDivisor sX ω) + Δ).pullback hQK hB =
        Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX f (ω.toPluriForms sX)))
          + ΔY := by
      ext F
      have e := isDiscrepancy_eq_coeff_sub hω (hC F) hpb
      simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor]
      linarith
    rwa [heq] at hpb
  · have hB : ∀ Z : irreducibleComponents Y,
        f (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor (topFormDivisor sX ω) + Δ).supp := by
      intro Z hZ
      rw [MMP.Threefold.Mori.CanonUniq.componentGenericPoint_eq,
        map_genericPoint_of_isDominant] at hZ
      obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
      exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support E hE
    obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy ⟨hX, n', K₀, hK₀, hQ⟩ hK
      ⟨Y, f, hY, hf, F⟩
    have e := isDiscrepancy_eq_coeff_sub hω ha (h hB)
    convert ha using 1
    rw [e]
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor]
    ring

/-! ### Push-forward of divisorial sheaves -/

section Pushforward

open TopologicalSpace Opposite

section RationalFunctions

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

private theorem componentGenericPoint_eq_genericPoint (Z : irreducibleComponents X) :
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
  have hZ : componentGenericPoint X Z ∈ U := (componentGenericPoint_eq_genericPoint Z) ▸ hx
  rw [germ_eq_rationalFunctionsEquivFunctionField_symm U s hx Z hZ,
    TopCat.Presheaf.germ_stalkSpecializes_apply]

end RationalFunctions

section Valuation

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
  let e := (IsLocalization.algEquiv (nonZeroDivisors E.localRing) (FractionRing E.localRing)
    X.functionField).toRingEquiv
  have he : ∀ r : E.localRing, e (algebraMap E.localRing (FractionRing E.localRing) r) =
      algebraMap E.localRing X.functionField (RingEquiv.refl E.localRing r) := fun r =>
    (IsLocalization.algEquiv (nonZeroDivisors E.localRing) (FractionRing E.localRing)
      X.functionField).commutes r
  have hcomp : e (alg1 a) = φ := by
    rw [← hψ]
    have : (e.toRingHom.comp alg1.toRingEquiv.toRingHom) = ψ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors E.localRing) ?_
      ext r
      simp only [RingHom.comp_apply]
      change e (alg1 (algebraMap _ _ r)) = _
      rw [AlgEquiv.commutes, he]
      change _ = ψ ((X.presheaf.stalkSpecializes E.specializes_genericPoint).hom r)
      simp only [ψ]
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    exact congrArg (fun f => f a) this
  change Ring.ordFrac E.localRing (alg1 a) = Ring.ordFrac E.localRing φ
  rw [← hcomp]
  exact (Stacks.Chow.ordFrac_congr (RingEquiv.refl E.localRing) e he (alg1 a)).symm

private theorem ordGE_rationalFunctionsEquivFunctionField_symm_iff (E : MMP.Mori.PrimeDivisor X)
    (n : ℤ) (φ : X.functionField) :
    E.OrdGE n ((rationalFunctionsEquivFunctionField X).symm φ E.component) ↔
      φ = 0 ∨ n ≤ X.ord φ E.genericPoint := by
  unfold MMP.Mori.PrimeDivisor.OrdGE
  rw [valuation_rationalFunctionsEquivFunctionField_symm]
  have h0 : (rationalFunctionsEquivFunctionField X).symm φ E.component = 0 ↔ φ = 0 := by
    constructor
    · intro h
      rw [← stalkSpecializes_rationalFunctionsEquivFunctionField_symm E.component φ, h, map_zero]
    · rintro rfl
      rw [map_zero]
      rfl
  rw [h0]
  by_cases hφ : φ = 0
  · simp [hφ]
  · simp only [hφ, false_or]
    rw [(Scheme.ord_eq_iff E.coheight_genericPoint hφ).mp rfl]
    exact WithZero.exp_le_exp

/-- A rational function `φ` is a section of `𝒪_X(D)` over `U` exactly when
`ord_E(φ) ≥ -d_E` for every prime divisor `E` whose generic point lies in `U`. -/
private theorem isDivisorialSection_res_iff (D : Divisor X) (U : X.Opens) (φ : X.functionField) :
    D.IsDivisorialSection U ((rationalFunctionsPresheaf X).map (homOfLE le_top : U ⟶ ⊤).op
        ((rationalFunctionsPresheafTopEquiv X).symm
          ((rationalFunctionsEquivFunctionField X).symm φ))) ↔
      ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ U →
        (φ = 0 ∨ -D.coeff E ≤ X.ord φ E.genericPoint) := by
  refine forall_congr' fun E => ?_
  rw [← ordGE_rationalFunctionsEquivFunctionField_symm_iff]
  exact ⟨fun h hU => h ⟨E.genericPoint,
    MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E, hU⟩,
    fun h hne => h (E.genericPoint_mem_of_nonempty hne)⟩

end Valuation

/-- A rational function regular at the generic point of a prime divisor has nonnegative order
along it. -/
private theorem ord_algebraMap_nonneg {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (P : PrimeDivisor S) (J : P.localRing) :
    0 ≤ S.ord (algebraMap P.localRing S.functionField J) P.genericPoint := by
  by_cases hJ : J = 0
  · simp [hJ]
  have hz := P.coheight_genericPoint
  rw [Scheme.le_ord_iff hz
    ((map_ne_zero_iff _ (IsFractionRing.injective P.localRing S.functionField)).mpr hJ), ofAdd_zero]
  have : Ring.KrullDimLE 1 P.localRing := krullDimLE_of_coheight_le hz.le
  exact Ring.ordFrac_ge_one_of_ne_zero hJ

/-- The pull-back of a nonzero form along a dominant morphism inducing an isomorphism of
function fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := pullbackForms_eq hω m τ ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- A prime divisor of `Y` whose generic point maps to the generic point of a prime divisor of
`X` is not `f`-exceptional: the closure of its image has codimension one. -/
private theorem not_isExceptional_of_map_genericPoint_eq {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsSeparated (X ↘ Limits.terminal Scheme)]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X)
    {E : PrimeDivisor Y} {P : PrimeDivisor X} (heq : f E.genericPoint = P.genericPoint) :
    ¬ RationalMap.IsExceptional f.toRationalMap E := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  intro h
  have hsub : (IrreducibleCloseds.closureSingleton (f E.genericPoint) : Set X) ⊆
      (Closeds.closure (f '' (E.idealSheaf.support : Set Y)) : Set X) := by
    rw [IrreducibleCloseds.coe_closureSingleton, Closeds.coe_closure]
    exact closure_mono
      (Set.singleton_subset_iff.mpr
        ⟨E.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E, rfl⟩)
  have hle := le_closedsCodimension_iff.mp h _ hsub
  rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton (f E.genericPoint) =
    (irreducibleSetEquivPoints (α := X)).symm (f E.genericPoint) from rfl,
    Order.coheight_orderIso, heq, P.coheight_genericPoint] at hle
  exact absurd hle (by decide)

/-- Hartogs along a dominant morphism: the pull-back of a rational function regular on `U` has
nonnegative order along every prime divisor of `Y` whose generic point maps into `U`. -/
private theorem ord_functionFieldMap_nonneg {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) (ψ : X.functionField)
    (h : (0 : Divisor X).IsDivisorialSection U ((rationalFunctionsPresheaf X).map
      (homOfLE le_top : U ⟶ ⊤).op ((rationalFunctionsPresheafTopEquiv X).symm
        ((rationalFunctionsEquivFunctionField X).symm ψ))))
    (E : PrimeDivisor Y) (hx : f E.genericPoint ∈ U) :
    0 ≤ Y.ord (functionFieldMap f ψ) E.genericPoint := by
  obtain ⟨s, hs⟩ := Divisor.IsDivisorialSection.exists_eq h
  have hg : genericPoint X ∈ U :=
    ((genericPoint_spec X).specializes trivial).mem_open U.isOpen hx
  have hψ : ψ = algebraMap (X.presheaf.stalk (f E.genericPoint)) X.functionField
      (X.presheaf.germ U _ hx s) := by
    have h1 : algebraMap (X.presheaf.stalk (f E.genericPoint)) X.functionField
        (X.presheaf.germ U _ hx s) = X.presheaf.germ U (genericPoint X) hg s := by
      change (X.presheaf.germ U _ hx ≫ X.presheaf.stalkSpecializes _).hom s = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
    rw [h1]
    apply (rationalFunctionsEquivFunctionField X).symm.injective
    funext Z
    have hZ : componentGenericPoint X Z ∈ U := (componentGenericPoint_eq_genericPoint Z) ▸ hg
    rw [germ_eq_rationalFunctionsEquivFunctionField_symm U s hg Z hZ]
    exact (congrFun hs ⟨Z, hZ⟩).symm
  rw [hψ, functionFieldMap_algebraMap_stalk]
  exact ord_algebraMap_nonneg E _

/-- **Push-forward of divisorial sheaves.** Let `f : Y ⟶ X` be a proper birational morphism of
normal varieties of dimension `n` over a perfect field `k`, `D_Y` a divisor on `Y` and
`D = f_* D_Y` (`MMP.Mori.RationalMap.transformDivisor`) its birational transform. Then, over
every open `U ⊆ X`:
* a rational `n`-form `τ` on `X` whose pull-back `f^*τ` is a section of `ω_Y(D_Y)` over `f⁻¹(U)`
  is a section of `ω_X(D)` over `U`, that is, `f_* ω_Y(D_Y) ⊆ ω_X(D)`;
* a rational function `ψ ∈ k(X)` such that `f^*ψ` is a section of `𝒪_Y(D_Y)` over `f⁻¹(U)` is a
  section of `𝒪_X(D)` over `U`, that is, `f_* 𝒪_Y(D_Y) ⊆ 𝒪_X(D)`;
* if `D_Y` is effective and `f`-exceptional, then `f^*ψ` is a section of `𝒪_Y(D_Y)` over
  `f⁻¹(U)` if and only if `ψ` is a section of `𝒪_X(0) = 𝒪_X` over `U`, that is,
  `f_* 𝒪_Y(D_Y) = 𝒪_X`. -/
@[mmp "lem_km5b_pushforward_effective_exceptional"]
public theorem pushforward_divisorialSheaf_le {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {n : ℕ}
    (hn : topologicalKrullDim X = n) (D_Y : Divisor Y) :
    haveI := hf.isDominant
    let res : ∀ (Z : Scheme.{u}) [IsIntegral Z] (V : Z.Opens), Z.functionField →
        ToType ((rationalFunctionsPresheaf Z).obj (op V)) := fun Z _ V ψ =>
      (rationalFunctionsPresheaf Z).map (homOfLE le_top).op
        ((rationalFunctionsPresheafTopEquiv Z).symm
          ((rationalFunctionsEquivFunctionField Z).symm ψ))
    let D : Divisor X := RationalMap.transformDivisor f.toRationalMap D_Y
    (∀ (U : X.Opens) (τ : RationalPluriForms sX n 1),
        pullbackRationalPluriForms sX f τ ∈ pluricanonicalSections (f ≫ sX) n 1 D_Y (f ⁻¹ᵁ U) →
          τ ∈ pluricanonicalSections sX n 1 D U) ∧
    (∀ (U : X.Opens) (ψ : X.functionField),
        D_Y.IsDivisorialSection (f ⁻¹ᵁ U) (res Y (f ⁻¹ᵁ U) (functionFieldMap f ψ)) →
          D.IsDivisorialSection U (res X U ψ)) ∧
    (D_Y.IsEffective → (∀ E : PrimeDivisor Y, D_Y.coeff E ≠ 0 →
        RationalMap.IsExceptional f.toRationalMap E) →
      ∀ (U : X.Opens) (ψ : X.functionField),
        D_Y.IsDivisorialSection (f ⁻¹ᵁ U) (res Y (f ⁻¹ᵁ U) (functionFieldMap f ψ)) ↔
          (0 : Divisor X).IsDivisorialSection U (res X U ψ)) := by
  haveI := hf.isDominant
  intro res D
  have := hX.1
  have hbij := hf.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hsep : IsSeparated (X ↘ Limits.terminal Scheme) := by
    rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have key (P : PrimeDivisor X) : ∃ E : PrimeDivisor Y, f E.genericPoint = P.genericPoint ∧
      IsIso (f.stalkMap E.genericPoint) ∧ D.coeff P = D_Y.coeff E := by
    obtain ⟨E, heq, hiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hf P
    exact ⟨E, heq, hiso, htr D_Y⟩
  have part2 : ∀ (U : X.Opens) (ψ : X.functionField),
      D_Y.IsDivisorialSection (f ⁻¹ᵁ U) (res Y (f ⁻¹ᵁ U) (functionFieldMap f ψ)) →
        D.IsDivisorialSection U (res X U ψ) := by
    intro U ψ h
    rw [isDivisorialSection_res_iff] at h ⊢
    intro P hP
    obtain ⟨E, heq, _, hc⟩ := key P
    rcases h E (show f E.genericPoint ∈ U from heq ▸ hP) with h0 | h1
    · exact Or.inl ((map_eq_zero_iff _ (functionFieldMap f).injective).mp h0)
    · rw [hc, ← MMP.Positivity.ord_functionFieldMap_of_isIso f E P heq ψ]
      exact Or.inr h1
  refine ⟨fun U τ h => ⟨fun hU => ?_, fun P hP hτ => ?_⟩, part2, fun heff hexc U ψ => ?_⟩
  · by_contra hτ
    exact pullbackRationalPluriForms_ne_zero f hbij hd hτ (h.1 (by rw [hU]; rfl))
  · obtain ⟨E, heq, _, hc⟩ := key P
    have hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty :=
      ⟨E.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E,
      show f E.genericPoint ∈ U from heq ▸ P.genericPoint_mem_of_nonempty hP⟩
    have h2 := h.2 E hE (pullbackRationalPluriForms_ne_zero f hbij hd hτ)
    rwa [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hbij hd E P heq τ, ← hc]
      at h2
  · have hD0 : D = 0 := Finsupp.ext fun P => by
      obtain ⟨E, heq, -, hc⟩ := key P
      change D.coeff P = 0
      rw [hc]
      by_contra hne
      exact not_isExceptional_of_map_genericPoint_eq f heq (hexc E hne)
    refine ⟨fun h => hD0 ▸ part2 U ψ h, fun h => ?_⟩
    rw [isDivisorialSection_res_iff]
    exact fun E hE => Or.inr ((neg_nonpos.mpr (heff E)).trans
      (ord_functionFieldMap_nonneg f U ψ h E hE))

end Pushforward

end MMP.Mori
