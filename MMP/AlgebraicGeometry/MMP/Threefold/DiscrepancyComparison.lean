module

public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Divisor.Pullback

/-!
# Auxiliary results for discrepancies

Algebraic Hartogs with non-negative orders, and the comparison of two discrepancies of the same
divisor over `X` when one boundary dominates the other.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Threefold.Mori.Helpers

section Aux

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- Algebraic Hartogs: a nonzero rational function `g` whose order is nonnegative along every
prime divisor through `x` lies in the image of the stalk at `x`. -/
theorem exists_algebraMap_stalk_eq_of_forall_ord_nonneg (x : X) {g : X.functionField}
    (hg : g ≠ 0) (h : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support → 0 ≤ X.ord g Γ.genericPoint) :
    ∃ r : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField r = g := by
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  refine Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
    X.functionField fun q hq => ?_
  have hξ1 : Order.coheight (X.fromSpecStalk x q) = 1 :=
    (Stacks.Chow.coheight_fromSpecStalk_eq_height x q).trans hq
  set E : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hξ1 with hEdef
  have hEξ : E.genericPoint = X.fromSpecStalk x q :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hξ1
  have hspec : E.genericPoint ⤳ x := hEξ ▸ Stacks.Chow.specializes_fromSpecStalk x q
  have hxE : x ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hspec
  have hv : E.divisorialValuation g ≤ 1 := by
    rw [E.divisorialValuation_eq_exp_neg_ord hg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    have := h E hxE
    omega
  obtain ⟨b, hb⟩ := (E.divisorialValuation_le_one_iff g).mp hv
  let := (X.presheaf.stalkSpecializes hspec).hom.toAlgebra
  have hloc := Stacks.Chow.isLocalization_stalk_of_specializes hspec q hEξ.symm
  obtain ⟨⟨a, s⟩, hab⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl b
  change IsLocalization.mk' E.localRing a s = b at hab
  refine ⟨a, s, s.2, ?_⟩
  have hspec' := IsLocalization.mk'_spec E.localRing a s
  rw [hab] at hspec'
  have h2 := congrArg (algebraMap E.localRing X.functionField) hspec'
  rw [map_mul, hb] at h2
  change g * algebraMap E.localRing X.functionField ((X.presheaf.stalkSpecializes hspec).hom s) =
    algebraMap E.localRing X.functionField ((X.presheaf.stalkSpecializes hspec).hom a) at h2
  rwa [algebraMap_stalkSpecializes, algebraMap_stalkSpecializes] at h2

omit [IsNormal X] in
/-- If a nonzero rational function `h` comes from the stalk at the centre `D.f D.E.genericPoint`
of a divisor `D` over `X`, then the order of its pullback along `D.E` is nonnegative. -/
theorem ord_functionFieldMap_nonneg {sX : X ⟶ Spec (.of k)} (D : DivisorOver k sX)
    {h : X.functionField} (hh : h ≠ 0) (r : X.presheaf.stalk (D.f D.E.genericPoint))
    (hr : algebraMap (X.presheaf.stalk (D.f D.E.genericPoint)) X.functionField r = h) :
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    0 ≤ D.Y.ord (functionFieldMap D.f h) D.E.genericPoint := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have hne : functionFieldMap D.f h ≠ 0 := (map_ne_zero _).mpr hh
  have h1 : D.E.divisorialValuation (functionFieldMap D.f h) ≤ 1 := by
    rw [D.E.divisorialValuation_le_one_iff]
    refine ⟨(D.f.stalkMap D.E.genericPoint).hom r, ?_⟩
    rw [← hr, functionFieldMap_algebraMap_stalk]
  rw [D.E.divisorialValuation_eq_exp_neg_ord hne, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

/-- If `a` is a discrepancy of `D` with respect to `Δ` and `a'` one with respect to `Δ + Δ'`,
where `Δ'` is effective, then `a' ≤ a`. -/
theorem isDiscrepancy_le_of_effective [PerfectField k] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
    {Δ Δ' : QDivisor X} (hΔ'e : Δ'.IsEffective) {D : DivisorOver k sX} {a a' : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) (ha' : IsDiscrepancy sX n K (Δ + Δ') D a') : a' ≤ a := by
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  obtain ⟨-, -, m', hm', -, U', hU', τ', hτ', hτa'⟩ := ha'
  let := functionFieldAlgebra sX
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set c := (ZTensorPower.basis b m).repr τ () with hc_def
  set c' := (ZTensorPower.basis b m').repr τ' () with hc'_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ.1
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ'.1
  set g : X.functionField := c ^ (m' : ℤ) * c' ^ (-(m : ℤ)) with hg_def
  have hg : g ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc')
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      0 ≤ X.ord g Γ.genericPoint := by
    intro Γ hΓ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have e2 := hτ'.2 Γ ⟨_, hΓ, hU'⟩
    have f1 : (Γ.ordForm τ : ℚ) = (X.ord c Γ.genericPoint : ℚ) + m * NΓ := by
      exact_mod_cast hNΓ m τ hτ.1
    have f2 : (Γ.ordForm τ' : ℚ) = (X.ord c' Γ.genericPoint : ℚ) + m' * NΓ := by
      exact_mod_cast hNΓ m' τ' hτ'.1
    rw [hg_def, Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'), ord_zpow _ hc,
      ord_zpow _ hc']
    have hco : (0 : ℚ) ≤ Δ'.coeff Γ := hΔ'e Γ
    rw [DivisorWithCoeffs.coeff_add] at e2
    have : ((m' : ℚ) * X.ord c Γ.genericPoint + -(m : ℚ) * X.ord c' Γ.genericPoint) =
        (m : ℚ) * m' * Δ'.coeff Γ := by
      linear_combination (m' : ℚ) * hτ.2 Γ ⟨_, hΓ, hU⟩ - (m : ℚ) * e2 - (m' : ℚ) * f1 + (m : ℚ) * f2
    have h0 : (0 : ℚ) ≤ ((m' : ℚ) * X.ord c Γ.genericPoint + -(m : ℚ) * X.ord c' Γ.genericPoint) := by
      rw [this]
      positivity
    exact_mod_cast h0
  obtain ⟨r, hr⟩ := exists_algebraMap_stalk_eq_of_forall_ord_nonneg _ hg hord
  have hY0 := ord_functionFieldMap_nonneg D hg r hr
  have hfc : functionFieldMap D.f c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap D.f c' ≠ 0 := (map_ne_zero _).mpr hc'
  rw [hg_def, map_mul, map_zpow₀, map_zpow₀,
    Scheme.ord_mul (zpow_ne_zero _ hfc) (zpow_ne_zero _ hfc'), ord_zpow _ hfc, ord_zpow _ hfc']
    at hY0
  have hY0' : (0 : ℚ) ≤ ((m' : ℚ) * D.Y.ord (functionFieldMap D.f c) D.E.genericPoint +
      -(m : ℚ) * D.Y.ord (functionFieldMap D.f c') D.E.genericPoint) := by
    exact_mod_cast hY0
  have h1 : (D.ordPullback τ : ℚ) =
      (D.Y.ord (functionFieldMap D.f c) D.E.genericPoint : ℚ) + m * N := by
    exact_mod_cast hN m τ hτ.1
  have h2 : (D.ordPullback τ' : ℚ) =
      (D.Y.ord (functionFieldMap D.f c') D.E.genericPoint : ℚ) + m' * N := by
    exact_mod_cast hN m' τ' hτ'.1
  have key : (m : ℚ) * m' * (a - a') =
      ((m' : ℚ) * D.Y.ord (functionFieldMap D.f c) D.E.genericPoint +
      -(m : ℚ) * D.Y.ord (functionFieldMap D.f c') D.E.genericPoint) := by
    linear_combination (m' : ℚ) * hτa - (m : ℚ) * hτa' + (m' : ℚ) * h1 - (m : ℚ) * h2
  have hm0 : (0 : ℚ) < (m : ℚ) * m' := by positivity
  nlinarith

/-! ### Orders of rational functions -/

/-- The valuation of the prime divisor `Γ` on an element `s` of the stalk at the generic point of
its component is `Ring.ordFrac` of the local ring of `Γ` at the image of `s` in the function
field. -/
theorem valuation_eq_ordFrac (Γ : MMP.Mori.PrimeDivisor X)
    (s : X.presheaf.stalk (componentGenericPoint X Γ.component)) :
    letI := Γ.toComponent.hom.toAlgebra
    haveI := isFractionRing_stalkToRationalFunctions Γ.genericPoint_mem_component
    haveI : Ring.KrullDimLE 1 Γ.localRing := krullDimLE_of_coheight_le Γ.coheight_genericPoint.le
    Γ.valuation s = Ring.ordFrac Γ.localRing (K := X.functionField)
      ((X.presheaf.stalkSpecializes
        (((genericPoint_spec X).specializes trivial :
           genericPoint X ⤳ componentGenericPoint X Γ.component))).hom s) := by
  letI := Γ.toComponent.hom.toAlgebra
  haveI := isFractionRing_stalkToRationalFunctions Γ.genericPoint_mem_component
  haveI : Ring.KrullDimLE 1 Γ.localRing := krullDimLE_of_coheight_le Γ.coheight_genericPoint.le
  set g := (X.presheaf.stalkSpecializes
        (((genericPoint_spec X).specializes trivial :
           genericPoint X ⤳ componentGenericPoint X Γ.component))).hom with hg
  have hmap : ∀ a : Γ.localRing,
      g (Γ.toComponent.hom a) = algebraMap Γ.localRing X.functionField a :=
    algebraMap_stalkSpecializes (X := X)
      ((isGenericPoint_componentGenericPoint X Γ.component).specializes
        Γ.genericPoint_mem_component)
  have key : ∀ a : Γ.localRing, Γ.valuation (Γ.toComponent.hom a) =
      Ring.ordFrac Γ.localRing (K := X.functionField) (g (Γ.toComponent.hom a)) := by
    intro a
    rw [hmap]
    by_cases ha : a = 0
    · simp [ha]
    · rw [Ring.ordFrac_eq_ord Γ.localRing ha]
      change Ring.ordFrac Γ.localRing (IsLocalization.algEquiv (nonZeroDivisors Γ.localRing) _
        (FractionRing Γ.localRing) (algebraMap Γ.localRing _ a)) = _
      rw [AlgEquiv.commutes, Ring.ordFrac_eq_ord Γ.localRing ha]
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors Γ.localRing) s
  change s * Γ.toComponent.hom b = Γ.toComponent.hom a at hab
  have hgb : g (Γ.toComponent.hom b) ≠ 0 := by
    rw [hmap]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have e1 := congrArg Γ.valuation hab
  have e2 := congrArg (fun t => Ring.ordFrac Γ.localRing (K := X.functionField) (g t)) hab
  simp only [map_mul] at e1 e2
  rw [key a, key b] at e1
  exact mul_right_cancel₀ ((map_ne_zero _).mpr hgb) (e1.trans e2.symm)

/-- The ring map from rational functions on `X` to the function field of `X`, through the
irreducible component `Z`. -/
def evalFF (Z : irreducibleComponents X) : RationalFunctions X →+* X.functionField :=
  (X.presheaf.stalkSpecializes
    (((genericPoint_spec X).specializes trivial :
      genericPoint X ⤳ componentGenericPoint X Z))).hom.comp (RationalFunctions.component X Z)

/-- The order along `Γ` of a unit rational function `φ` is the order at the generic point of `Γ`
of its image `evalFF Γ.component φ` in the function field. -/
theorem ord_eq_scheme_ord (Γ : MMP.Mori.PrimeDivisor X) (φ : (RationalFunctions X)ˣ) :
    Γ.ord φ = X.ord (evalFF Γ.component (φ : RationalFunctions X)) Γ.genericPoint := by
  symm
  rw [Scheme.ord_eq_iff Γ.coheight_genericPoint (φ.isUnit.map (evalFF Γ.component)).ne_zero]
  have : Ring.KrullDimLE 1 Γ.localRing := krullDimLE_of_coheight_le Γ.coheight_genericPoint.le
  have h := Γ.valuation_component φ
  rw [valuation_eq_ordFrac] at h
  change Ring.ordFrac Γ.localRing (K := X.functionField) _ = _ at h
  unfold Scheme.ordHom
  convert h using 1 <;> rfl

/-! ### Adding an effective `ℚ`-Cartier divisor -/

section Existence

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- If `m • (K + Δ)` and `m1 • Δ'` are Cartier, then so is `(m * m1) • (K + (Δ + Δ'))`. -/
theorem isCartierDivisor_mul_smul_add {K : Divisor X} {Δ Δ' : QDivisor X} {m m1 : ℕ}
    (h1 : ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor)
    (h2 : ((m1 : ℤ) • Δ').IsCartierDivisor) :
    (((m * m1 : ℕ) : ℤ) • (Divisor.toQDivisor K + (Δ + Δ'))).IsCartierDivisor := by
  obtain ⟨C, hC, cC⟩ := h1
  obtain ⟨D', hD', cD'⟩ := h2
  refine ⟨(m1 : ℤ) • C + (m : ℤ) • D', ?_, (cC.zsmul _).add (cD'.zsmul _)⟩
  rw [map_add, map_zsmul, map_zsmul, hC, hD']
  simp only [Nat.cast_mul, mul_smul, smul_add]
  rw [smul_comm (m1 : ℤ) (m : ℤ) (Divisor.toQDivisor K), smul_comm (m1 : ℤ) (m : ℤ) Δ]
  abel

/-- An integral scheme has exactly one irreducible component. -/
theorem subsingleton_irreducibleComponents : Subsingleton (irreducibleComponents X) := by
  refine ⟨fun Z Z' => Subtype.ext ?_⟩
  have h : irreducibleComponents X = {Set.univ} := irreducibleComponents_eq_singleton
  have h1 : Z.1 ∈ ({Set.univ} : Set (Set X)) := h ▸ Z.2
  have h2 : Z'.1 ∈ ({Set.univ} : Set (Set X)) := h ▸ Z'.2
  rw [Set.mem_singleton_iff] at h1 h2
  rw [h1, h2]

/-- If `D` has discrepancy `a` with respect to `Δ` and `Δ'` is `ℚ`-Cartier, then `D` has a
discrepancy with respect to `Δ + Δ'`. -/
theorem exists_isDiscrepancy_add [PerfectField k] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
    {Δ Δ' : QDivisor X} (hΔ'q : Δ'.IsQCartier) {D : DivisorOver k sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) : ∃ a' : ℚ, IsDiscrepancy sX n K (Δ + Δ') D a' := by
  obtain ⟨hX, hK, m, hm, hmC, U, hU, τ, hτ, hτa⟩ := ha
  obtain ⟨m1, hm1, hΔ1⟩ := hΔ'q.exists_pos
  obtain ⟨D', hD', cD'⟩ := hΔ1
  obtain ⟨U1, hxU1, ψ, hψ⟩ := cD' (D.f D.E.genericPoint)
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N, -⟩ := D.exists_ordPullback_eq hX hn
  have hsub := subsingleton_irreducibleComponents (X := X)
  let Z0 : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]
    simp⟩
  set c := (ZTensorPower.basis b m).repr τ () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ.1
  set g := evalFF Z0 (ψ : RationalFunctions X) with hg_def
  have hg : g ≠ 0 := (ψ.isUnit.map (evalFF Z0)).ne_zero
  set c'' : X.functionField := c ^ (m1 : ℤ) * g ^ (-(m : ℤ)) with hc''_def
  have hc'' : c'' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hg)
  let τ'' : RationalPluriForms sX n ((m * m1 : ℕ) : ℤ) :=
    (ZTensorPower.basis b ((m * m1 : ℕ) : ℤ)).repr.symm (Finsupp.single () c'')
  have hτ'' : (ZTensorPower.basis b ((m * m1 : ℕ) : ℤ)).repr τ'' () = c'' := by
    simp [τ'']
  have hτ''0 : τ'' ≠ 0 := by
    intro h0
    rw [h0] at hτ''
    simp at hτ''
    exact hc'' hτ''.symm
  have hD'c : ∀ Γ : MMP.Mori.PrimeDivisor X, (D'.coeff Γ : ℚ) = m1 * Δ'.coeff Γ :=
    fun Γ => by simpa using congrArg (fun F => DivisorWithCoeffs.coeff F Γ) hD'
  have hgen : GeneratesOn (Δ + Δ') (m * m1) (U ⊓ U1) τ'' := by
    refine ⟨hτ''0, fun Γ ⟨pt, hptΓ, hptU⟩ => ?_⟩
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have f1 : (Γ.ordForm τ : ℚ) = (X.ord c Γ.genericPoint : ℚ) + m * NΓ := by
      exact_mod_cast hNΓ m τ hτ.1
    have f2 : (Γ.ordForm τ'' : ℚ) = (X.ord c'' Γ.genericPoint : ℚ) + (m * m1 : ℕ) * NΓ := by
      exact_mod_cast hNΓ _ τ'' hτ''0 |>.trans (by rw [hτ''])
    have hog : X.ord g Γ.genericPoint = D'.coeff Γ := by
      rw [hψ Γ ⟨pt, hptΓ, hptU.2⟩, ord_eq_scheme_ord, Subsingleton.elim Γ.component Z0]
    have hoc : (X.ord c'' Γ.genericPoint : ℚ) =
        m1 * X.ord c Γ.genericPoint - m * X.ord g Γ.genericPoint := by
      rw [hc''_def, Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hg), ord_zpow _ hc,
        ord_zpow _ hg]
      push_cast
      ring
    have hog' : (X.ord g Γ.genericPoint : ℚ) = D'.coeff Γ := by exact_mod_cast hog
    rw [DivisorWithCoeffs.coeff_add]
    push_cast at f2 ⊢
    linear_combination f2 + hoc - (m : ℚ) * hog' - (m : ℚ) * hD'c Γ +
      (m1 : ℚ) * hτ.2 Γ ⟨pt, hptΓ, hptU.1⟩ - (m1 : ℚ) * f1
  refine ⟨(D.ordPullback τ'' : ℚ) / ((m * m1 : ℕ) : ℚ), hX, hK, m * m1, Nat.mul_pos hm hm1,
    isCartierDivisor_mul_smul_add hmC (hD' ▸ ⟨D', rfl, cD'⟩), U ⊓ U1, ⟨hU, hxU1⟩, τ'', hgen, ?_⟩
  have : ((m * m1 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp

/-- If `D` has discrepancy `a` with respect to `Δ` and `Δ'` is effective and `ℚ`-Cartier, then
`D` has a discrepancy `a' ≤ a` with respect to `Δ + Δ'`. -/
theorem exists_isDiscrepancy_add_le [PerfectField k] {sX : X ⟶ Spec (.of k)} {n : ℕ}
    {K : Divisor X} {Δ Δ' : QDivisor X} (hΔ'e : Δ'.IsEffective) (hΔ'q : Δ'.IsQCartier)
    {D : DivisorOver k sX} {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) :
    ∃ a' : ℚ, a' ≤ a ∧ IsDiscrepancy sX n K (Δ + Δ') D a' := by
  obtain ⟨a', ha'⟩ := exists_isDiscrepancy_add hΔ'q ha
  exact ⟨a', isDiscrepancy_le_of_effective hΔ'e ha ha', ha'⟩

/-- Adding an effective `ℚ`-Cartier divisor `Δ'` to the boundary does not increase the
discrepancy: `discrep sX n K (Δ + Δ') ≤ discrep sX n K Δ`. -/
theorem discrep_add_le [PerfectField k] {sX : X ⟶ Spec (.of k)} {n : ℕ}
    {K : Divisor X} {Δ Δ' : QDivisor X} (hΔ'e : Δ'.IsEffective) (hΔ'q : Δ'.IsQCartier) :
    discrep sX n K (Δ + Δ') ≤ discrep sX n K Δ := by
  refine le_discrep_iff.mpr fun D a hD ha => ?_
  obtain ⟨a', hle, ha'⟩ := exists_isDiscrepancy_add_le hΔ'e hΔ'q ha
  exact (discrep_le hD ha').trans (by exact_mod_cast hle)

end Existence

end Aux

/-! ### Transport of orders of forms along isomorphisms -/

section

variable {k : Type*} [CommRing k] {d : ℕ}
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra k A] [Algebra k B] [Algebra k C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower k A B] [IsScalarTower k B C]
  [IsScalarTower k A C] [IsScalarTower A B C]

/-- For a tower `A → B → C` of `k`-algebras, the maps on Kähler differentials compose:
`Ω[B⁄k] → Ω[C⁄k]` after `Ω[A⁄k] → Ω[B⁄k]` is `Ω[A⁄k] → Ω[C⁄k]`. -/
theorem kaehler_map_comp' (w : Ω[A⁄k]) :
    KaehlerDifferential.map k k B C (KaehlerDifferential.map k k A B w) =
      KaehlerDifferential.map k k A C w := by
  have hw : w ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    simp [KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smul, ← algebraMap_smul B a (KaehlerDifferential.map k k A B x), map_smul,
      algebraMap_smul, hx, map_smul]

/-- For a tower `A → B → C` of `k`-algebras, the maps `topFormsMap` on `d`-th exterior powers of
Kähler differentials compose. -/
theorem topFormsMap_comp (x : ⋀[A]^d Ω[A⁄k]) :
    topFormsMap k B C d (topFormsMap k A B d x) = topFormsMap k A C d x := by
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A d (M := Ω[A⁄k]))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨v, rfl⟩ := hw
    simp only [topFormsMap_ιMulti, kaehler_map_comp']
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smul, ← algebraMap_smul B a (topFormsMap k A B d x), map_smul,
      algebraMap_smul, hx, map_smul]

end

section Transport

variable {k : Type*} [CommRing k] {d : ℕ} {m : ℤ}
variable {K K' : Type*} [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K']
variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]
  [Algebra A' K'] [IsScalarTower k A' K'] [IsFractionRing A' K']
  [Algebra A A'] [IsScalarTower k A A'] [Algebra A K'] [IsScalarTower A A' K'] [IsScalarTower A K K']
  [IsScalarTower k A K']

/-- Let `A → A'` be bijective, and `v`, `v'` additive orders on `K`, `K'` vanishing on units of
`A`, `A'` with `v' ∘ algebraMap K K' = v`. Then the order `ordAt A' v'` of the pullback of a
pluri-form `τ` to `K'` equals `ordAt A v τ`. -/
theorem ordAt_pullbackForms_eq (hbij : Function.Bijective (algebraMap A A'))
    {v : K → ℤ} {v' : K' → ℤ}
    (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (hmul' : ∀ x y : K', x ≠ 0 → y ≠ 0 → v' (x * y) = v' x + v' y)
    (hunit' : ∀ a : A', IsUnit a → v' (algebraMap A' K' a) = 0)
    (hvv : ∀ x, v' (algebraMap K K' x) = v x)
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (hω : IsPullbackGenerator K' (topFormsMap k A K d σ)) (τ : PluriForms k K d m) :
    ordAt A' v' (pullbackForms (K' := K') m τ) = ordAt A v τ := by
  have h0 : topFormsMap k A K d σ ≠ 0 := hω.ne_zero
  letI : IsLocalization (⊥ : Submonoid A) A' := by
    let e : A ≃ₐ[A] A' := AlgEquiv.ofBijective (Algebra.ofId A A') hbij
    exact (IsLocalization.isLocalization_iff_of_algEquiv (⊥ : Submonoid A) e).mp
      (IsLocalization.self (R := A) (M := ⊥) (fun x hx => by
        rw [Submonoid.mem_bot.mp hx]; exact isUnit_one))
  have hσ'' : Submodule.span A' {topFormsMap k A A' d σ} = ⊤ :=
    span_singleton_topFormsMap (⊥ : Submonoid A) hσ
  have h0'' : topFormsMap k A' K' d (topFormsMap k A A' d σ) ≠ 0 := by
    rw [topFormsMap_comp, ← topFormsMap_comp (B := K) (C := K')]
    exact hω.2.2
  rw [ordAt_eq hmul' hunit' hσ'' h0'', ordAt_eq hmul hunit hσ h0, pullbackForms_eq hω]
  have hb1 : topFormsBasis A' hσ'' h0'' () = (1 : K') • basisOfSpanSingleton hω.2.1 hω.2.2 () := by
    rw [topFormsBasis_apply, basisOfSpanSingleton_apply, one_smul, topFormsMap_comp,
      ← topFormsMap_comp (B := K) (C := K')]
  have hb2 : topFormsBasis A hσ h0 () = (1 : K) • basisOfSpanSingleton hω.1 hω.ne_zero () := by
    simp
  have hbas : ZTensorPower.basis (topFormsBasis A' hσ'' h0'') m () =
      ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m () := by
    rw [ZTensorPower.basis_apply_of_eq_smul hb1, one_zpow, one_smul]
  have : formCoeff A' hσ'' h0'' (pullbackFormsAlong hω m τ) = algebraMap K K' (formCoeff A hσ h0 τ) := by
    unfold formCoeff pullbackFormsAlong
    rw [← hbas, ZTensorPower.basis_repr_of_eq_smul hb2]
    simp [Algebra.smul_def]
  rw [this, hvv]

end Transport

section C1

variable {k : Type*} [CommRing k] {d : ℕ} {m : ℤ}
variable {K K' K'' : Type*} [Field K] [Field K'] [Field K''] [Algebra k K] [Algebra k K'] [Algebra k K'']
  [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower k K K'] [IsScalarTower k K' K'']
  [IsScalarTower k K K''] [IsScalarTower K K' K'']

/-- Any nonzero spanning vector is a pullback generator once one is. -/
theorem IsPullbackGenerator.of_span {ω ω' : ⋀[K]^d Ω[K⁄k]} (h : IsPullbackGenerator K' ω)
    (hω' : Submodule.span K {ω'} = ⊤) (h0 : ω' ≠ 0) : IsPullbackGenerator K' ω' := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hω' ▸ Submodule.mem_top (x := ω))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact h.ne_zero (by rw [← hc, zero_smul])
  have h1 : topFormsMap k K K' d ω = algebraMap K K' c • topFormsMap k K K' d ω' := by
    rw [← hc, map_smul, algebraMap_smul]
  have h2 : topFormsMap k K K' d ω' = algebraMap K K' c⁻¹ • topFormsMap k K K' d ω := by
    rw [h1, smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
  have hc' : algebraMap K K' c⁻¹ ≠ 0 := (map_ne_zero _).mpr (inv_ne_zero hc0)
  refine ⟨hω', ?_, ?_⟩ <;> rw [h2]
  · rw [Submodule.span_singleton_smul_eq hc'.isUnit]
    exact h.2.1
  · exact smul_ne_zero hc' h.2.2

/-- Pulling back pluri-forms from `K` to `K'` and then to `K''` is pulling back from `K` to
`K''`. -/
theorem pullbackForms_comp {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω)
    (hω' : IsPullbackGenerator K'' (topFormsMap k K K' d ω)) (τ : PluriForms k K d m) :
    pullbackForms (K' := K'') m (pullbackForms (K' := K') m τ) =
      pullbackForms (K' := K'') m τ := by
  have hcomp : topFormsMap k K' K'' d (topFormsMap k K K' d ω) = topFormsMap k K K'' d ω :=
    topFormsMap_comp ω
  have hω3 : IsPullbackGenerator K'' ω := ⟨hω.1, hcomp ▸ hω'.2.1, hcomp ▸ hω'.2.2⟩
  have hB : ZTensorPower.basis (basisOfSpanSingleton hω'.1 hω'.ne_zero) m () =
      ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m () := by
    have : basisOfSpanSingleton hω'.1 hω'.ne_zero () = (1 : K') • basisOfSpanSingleton hω.2.1 hω.2.2 () := by
      simp
    rw [ZTensorPower.basis_apply_of_eq_smul this, one_zpow, one_smul]
  have hB2 : ZTensorPower.basis (basisOfSpanSingleton hω'.2.1 hω'.2.2) m () =
      ZTensorPower.basis (basisOfSpanSingleton hω3.2.1 hω3.2.2) m () := by
    have : basisOfSpanSingleton hω'.2.1 hω'.2.2 () = (1 : K'') • basisOfSpanSingleton hω3.2.1 hω3.2.2 () := by
      simp [hcomp]
    rw [ZTensorPower.basis_apply_of_eq_smul this, one_zpow, one_smul]
  rw [pullbackForms_eq hω, pullbackForms_eq hω', pullbackForms_eq hω3]
  unfold pullbackFormsAlong
  rw [← hB]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]
  rw [hB2, ← IsScalarTower.algebraMap_apply K K' K'']

end C1

end MMP.Threefold.Mori.Helpers
