module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical

/-!
# The log discrepancy and the Kollár–Mori discrepancy

Let `X` be a normal variety of dimension `n` over a field `k`, `Δ` a `ℚ`-divisor on `X` such
that `(X, Δ)` is a pair (`m(K_X + Δ)` is Cartier for some `m > 0`), and `(Y, f, E)` a prime
divisor over `X` with `f` proper. Kollár and Mori define the discrepancy `a(E, X, Δ)` through a
local generator `τ` of `𝒪_X(m(K_X + Δ))` near the centre of `E`: `m · a(E, X, Δ) = ord_E(f^*τ)`.
The log discrepancy `A(E, X, Δ) = 1 + coeff_E(K_Y - f^*(K_X + Δ))` is defined with `K_X = div(ω)`
and `K_Y = div(f^*ω)` for one nonzero rational top form `ω`. The two are related by
`A(E, X, Δ) = 1 + a(E, X, Δ)`: a local generator divided by `ω^{⊗m}` is a local equation of
`m(K_X + Δ)`, and its order along `E` is `m` times the coefficient of `f^*(K_X + Δ) - K_Y`.

Consequently the log discrepancy of a divisor over `X` depends only on its valuation, and not on
the model realizing it, on the form `ω`, on the presentation of `K_X + B` as a combination of
Cartier divisors, or on the index `n` at which it is computed.

## Main results

* `MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy`: for a divisor `(Y, f, E)` over a
  pair `(X, Δ)` with discrepancy `a = a(E, X, Δ)`, a real number `b` is the log discrepancy of
  `E` with respect to `(X, Δ)` if and only if `f` is proper and `b = 1 + a`.
* `MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq`: two log discrepancies of divisors
  over `X` with the same valuation, at any indices, coincide.
* `MMP.Threefold.Bridges.IsLogDiscrepancy.unique`: the log discrepancy of a divisor over `X` is
  unique.

## Implementation notes

* The canonical divisors are chosen by one rational top form inside
  `MMP.Intersection.IsLogDiscrepancy`, which quantifies over the form `ω` with `K_X = div(ω)` and
  takes `K_Y = div(f^*ω)`. The Kollár–Mori discrepancy `MMP.Mori.IsDiscrepancy` depends on its
  canonical divisor `K` only through the condition that `m(K + Δ)` be Cartier, which depends on
  the linear equivalence class of `K` only; so any canonical divisor `K` may be used on the
  Kollár–Mori side.
* The background log discrepancy is defined for divisors `(Y, f, E)` over `X` with `f` proper,
  as in its source; the Kollár–Mori discrepancy for every divisor over `X`. The dictionary
  therefore states that the log discrepancy exists exactly when `f` is proper, and then equals
  `1 + a(E, X, Δ)`.
* The pair `(X, Δ)` has a `ℚ`-boundary `Δ`, regarded as an `ℝ`-divisor on the log discrepancy
  side. That `(X, Δ)` is a pair is implied by the existence of a discrepancy
  (`MMP.Mori.IsDiscrepancy.isPair`). No effectivity of `Δ` is assumed.
* The source works over a field of characteristic zero. The results are stated over a perfect
  field, which is what the comparison of canonical divisors and of orders of forms along a
  valuation uses.
* The independence statements are stated for an arbitrary `ℝ`-boundary `B`, which the dictionary
  covers only when `B` is rational; for a rational boundary they follow from the dictionary and
  the model independence of the Kollár–Mori discrepancy
  (`MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq_of_isPair`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.22, 2.25
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Threefold.Bridges

open MMP.Mori (Divisor QDivisor RDivisor DivisorOver)

/-- A linear form `L` with integer coefficients vanishing on the integer solutions of a system of
integer linear equations `A e = 0` vanishes on its rational solutions (clear denominators). -/
theorem sum_rat_eq_zero_of_int {ι p : Type*} [Fintype p] (A : ι → p → ℤ) (L : p → ℤ)
    (h : ∀ e : p → ℤ, (∀ i, ∑ j, A i j * e j = 0) → ∑ j, L j * e j = 0)
    (e : p → ℚ) (he : ∀ i, ∑ j, (A i j : ℚ) * e j = 0) : ∑ j, (L j : ℚ) * e j = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) (S := ℚ)
    Finset.univ e
  choose c hc using fun j => hb j (Finset.mem_univ j)
  have hc' : ∀ j, (c j : ℚ) = (b : ℤ) * e j := fun j => by
    simpa only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] using hc j
  have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have key := h c fun i => by
    have : ((∑ j, A i j * c j : ℤ) : ℚ) = 0 := by
      push_cast
      simp_rw [hc', mul_left_comm _ ((b : ℤ) : ℚ), ← Finset.mul_sum, he i, mul_zero]
    exact_mod_cast this
  have : ((∑ j, L j * c j : ℤ) : ℚ) = 0 := by exact_mod_cast key
  push_cast at this
  simp_rw [hc', mul_left_comm _ ((b : ℤ) : ℚ), ← Finset.mul_sum] at this
  exact (mul_eq_zero.mp this).resolve_left hb0

/-- A linear form `L` with integer coefficients vanishing on the integer solutions of a system of
integer linear equations `A e = 0` vanishes on its real solutions: every `ℚ`-linear functional
`ℝ → ℚ` carries a real solution to a rational one, and these functionals separate points. -/
theorem sum_real_eq_zero_of_int {ι p : Type*} [Fintype p] (A : ι → p → ℤ) (L : p → ℤ)
    (h : ∀ e : p → ℤ, (∀ i, ∑ j, A i j * e j = 0) → ∑ j, L j * e j = 0)
    (s : p → ℝ) (hs : ∀ i, ∑ j, (A i j : ℝ) * s j = 0) : ∑ j, (L j : ℝ) * s j = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff ℚ _).mp fun φ => ?_
  have hφ : ∀ (z : ℤ) (x : ℝ), φ ((z : ℝ) * x) = (z : ℚ) * φ x := fun z x => by
    have : ((z : ℝ) * x) = (z : ℚ) • x := by
      rw [← Rat.cast_smul_eq_qsmul ℝ]
      simp
    rw [this, map_rat_smul, smul_eq_mul]
  have := sum_rat_eq_zero_of_int A L h (fun j => φ (s j)) fun i => by
    have := congrArg φ (hs i)
    rw [map_sum, map_zero] at this
    simpa [hφ] using this
  rw [map_sum]
  simpa [hφ] using this

section Hartogs

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} [IsDominant f]

omit [IsNormal X] in
/-- The order at `z` of a finite product `∏ j ∈ s, g j ^ e j` of integer powers of nonzero
rational functions is `∑ j ∈ s, e j * X.ord (g j) z`. -/
theorem ord_prod_zpow {p : Type*} (z : X) (s : Finset p) (g : p → X.functionField)
    (hg : ∀ j, g j ≠ 0) (e : p → ℤ) :
    X.ord (∏ j ∈ s, g j ^ e j) z = ∑ j ∈ s, e j * X.ord (g j) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    have := Scheme.ord_mul (X := X) (x := z) (one_ne_zero (α := X.functionField))
      one_ne_zero
    rw [mul_one] at this
    omega
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      Scheme.ord_mul (zpow_ne_zero _ (hg j)) (Finset.prod_ne_zero_iff.mpr fun i _ =>
        zpow_ne_zero _ (hg i)), MMP.Mori.ord_zpow _ (hg j), ih]

omit [IsNormal Y] in
/-- **Real Hartogs along a divisor.** If an `ℝ`-combination of the orders of finitely many
nonzero rational functions `g_j` vanishes along every prime divisor through `f(η_E)`, the same
combination of the orders of the `f^*g_j` along `E` vanishes. -/
theorem sum_ord_functionFieldMap_eq_zero (E : MMP.Mori.PrimeDivisor Y) {p : Type*} [Fintype p]
    (g : p → X.functionField) (hg : ∀ j, g j ≠ 0) (s : p → ℝ)
    (hs : ∀ Γ : MMP.Mori.PrimeDivisor X, f E.genericPoint ∈ Γ.support →
      ∑ j, (X.ord (g j) Γ.genericPoint : ℝ) * s j = 0) :
    ∑ j, (Y.ord (functionFieldMap f (g j)) E.genericPoint : ℝ) * s j = 0 := by
  refine sum_real_eq_zero_of_int
    (ι := {Γ : MMP.Mori.PrimeDivisor X // f E.genericPoint ∈ Γ.support})
    (fun Γ j => X.ord (g j) Γ.1.genericPoint) _ (fun e he => ?_) s (fun Γ => hs Γ.1 Γ.2)
  set G : X.functionField := ∏ j, g j ^ e j
  have hG : G ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hg i)
  obtain ⟨t, ht, htG⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
    (f E.genericPoint) hG fun Γ hΓ => by
      rw [ord_prod_zpow _ _ _ hg]
      simpa [mul_comm] using he ⟨Γ, hΓ⟩
  have hY0 : Y.ord (functionFieldMap f G) E.genericPoint = 0 := by
    rw [← htG, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact E.ord_algebraMap_of_isUnit (ht.map _)
  have hfg : ∀ j, functionFieldMap f (g j) ≠ 0 := fun j => (map_ne_zero _).mpr (hg j)
  rw [map_prod] at hY0
  simp_rw [map_zpow₀] at hY0
  rw [ord_prod_zpow _ _ _ hfg] at hY0
  simpa [mul_comm] using hY0

omit [IsNormal X] [IsLocallyNoetherian X] in
/-- The order along `E` of the pull-back of a rational function depends only on the valuation
`v_E ∘ f^*`. -/
theorem ord_functionFieldMap_eq_of_valuationOver_eq {Y' : Scheme.{u}} [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] {f' : Y' ⟶ X} [IsDominant f']
    (E : MMP.Mori.PrimeDivisor Y)
    (E' : MMP.Mori.PrimeDivisor Y') (hv : E.valuationOver f = E'.valuationOver f')
    {g : X.functionField} (hg : g ≠ 0) :
    Y'.ord (functionFieldMap f' g) E'.genericPoint =
      Y.ord (functionFieldMap f g) E.genericPoint := by
  have h := congrArg (fun v => v g) hv
  simp only [MMP.Mori.PrimeDivisor.valuationOver_apply] at h
  rw [E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hg),
    E'.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hg)] at h
  exact neg_inj.mp (WithZero.exp_injective h).symm

end Hartogs

section Pullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} [IsDominant f]

/-- **The coefficient of a pull-back is the order of the pulled-back local equation**: if `φ` is
a local equation of the Cartier divisor `C` near `f(η_E)`, then `coeff_E(f^*C) = v_E(f^*φ)`. -/
theorem coeff_isPullback_eq_ord_evalFF {C : MMP.Mori.Divisor X}
    {hC : ∀ Z : irreducibleComponents Y, f (MMP.Mori.componentGenericPoint Y Z) ∉ C.supp}
    {C' : MMP.Mori.Divisor Y} (h : C.IsPullback f hC C') {U : X.Opens}
    {φ : (MMP.Mori.RationalFunctions X)ˣ} (hφ : C.IsLocalEquation U φ) (E : MMP.Mori.PrimeDivisor Y)
    (hU : f E.genericPoint ∈ U) (Z : irreducibleComponents X) :
    C'.coeff E = Y.ord (functionFieldMap f
      (MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions X))) E.genericPoint := by
  classical
  have hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hU
  rw [h U φ hφ E hE]
  have hZp := E.map_componentGenericPoint_mem f hE
  have hW := MMP.Mori.mem_pointComponent (f (MMP.Mori.componentGenericPoint Y E.component))
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZp (hC _) hW
  rw [MMP.Mori.pullbackComponent_eq hC hφ hZp hW a ha]
  set u := Units.map (f.stalkMap (MMP.Mori.componentGenericPoint Y E.component)).hom.toMonoidHom a
  let ψ : (MMP.Mori.RationalFunctions Y)ˣ :=
    (MMP.Mori.RationalFunctions.unitsEquiv Y).symm (Function.update 1 E.component u)
  have hψZ : (ψ : MMP.Mori.RationalFunctions Y) E.component = u := by
    simp [ψ, MMP.Mori.RationalFunctions.unitsEquiv]
  have h1 : E.ordUnit u = E.ord ψ := by
    rw [MMP.Mori.PrimeDivisor.ord_eq_ordUnit]
    congr 1
    exact (Units.ext hψZ).symm
  rw [h1, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  congr 1
  obtain rfl : Z = MMP.Mori.pointComponent (f (MMP.Mori.componentGenericPoint Y E.component)) :=
    Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
  change (Y.presheaf.stalkSpecializes _).hom ((ψ : MMP.Mori.RationalFunctions Y) E.component) =
    functionFieldMap f ((X.presheaf.stalkSpecializes _).hom
      ((φ : MMP.Mori.RationalFunctions X) _))
  rw [hψZ, ← ha]
  change _ = functionFieldMap f ((MMP.Mori.stalkToRationalFunctions X hW ≫
    X.presheaf.stalkSpecializes _).hom a)
  rw [MMP.Mori.stalkToRationalFunctions, TopCat.Presheaf.stalkSpecializes_comp]
  exact (MMP.Mori.functionFieldMap_algebraMap_stalk f
    (MMP.Mori.componentGenericPoint Y E.component) a.val).symm

end Pullback

section DominantPullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]

/-- A dominant morphism of integral schemes maps the generic point of `Y` outside the support of
every divisor on `X`. -/
theorem map_componentGenericPoint_notMem_supp (C : MMP.Mori.Divisor X)
    (Z : irreducibleComponents Y) : f (MMP.Mori.componentGenericPoint Y Z) ∉ C.supp := by
  rw [MMP.Threefold.Mori.CanonUniq.componentGenericPoint_eq, map_genericPoint_of_isDominant]
  intro h
  obtain ⟨E, -, hE⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mp h
  exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support E hE

/-- **The pull-back of a Cartier divisor along a dominant morphism exists**, for `Y`
quasi-compact. -/
theorem exists_isPullback_of_isDominant [CompactSpace Y] {C : MMP.Mori.Divisor X}
    (hC : C.IsCartier) :
    ∃ C' : MMP.Mori.Divisor Y,
      C.IsPullback f (map_componentGenericPoint_notMem_supp f C) C' :=
  hC.exists_isPullback _

end DominantPullback

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The value of a log discrepancy, against a Kollár–Mori discrepancy.** A log discrepancy `b`
of `(Y, f, E)` with respect to `(X, Δ)` is `1 + a(E, X, Δ)`: with `τ` the local generator and `ω`
the form, `τ / ω^{⊗m}` and the local equations of the Cartier divisors `Cᵢ` near `f(η_E)` satisfy
an `ℝ`-linear relation among their orders along every prime divisor through `f(η_E)`, which
pulls back to `E`. -/
theorem eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} {a : ℚ} (ha : MMP.Mori.IsDiscrepancy sX n K Δ D a) {b : ℝ}
    (hb : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) D b) :
    b = 1 + (a : ℝ) := by
  classical
  obtain ⟨hX, -, ω, hω0, -, m', r, C, C', hCc, hsum, hpb, rfl⟩ := hb
  obtain ⟨-, hK, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have hn := hK.topologicalKrullDim_eq
  let := MMP.Mori.functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨β, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set x := D.f D.E.genericPoint with hx
  choose V hV φ hφ using fun i => hCc i x
  let Z0 := MMP.Mori.pointComponent x
  let g : Fin m' → X.functionField := fun i =>
    MMP.Threefold.Mori.Helpers.evalFF Z0 ((φ i : MMP.Mori.RationalFunctions X))
  have hg : ∀ i, g i ≠ 0 := fun i => ((φ i).isUnit.map _).ne_zero
  set cω := (MMP.Mori.ZTensorPower.basis β 1).repr ω () with hcω
  set cτ := (MMP.Mori.ZTensorPower.basis β m).repr τ () with hcτ
  have hcω0 : cω ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero β hω0
  have hcτ0 : cτ ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero β hτ.1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  let G : Option (Option (Fin m')) → X.functionField := fun j =>
    Option.elim j cω fun j => Option.elim j cτ g
  let w : Option (Option (Fin m')) → ℝ := fun j =>
    Option.elim j (-1) fun j => Option.elim j (1 / (m : ℝ)) r
  have hG : ∀ j, G j ≠ 0 := by
    rintro (_ | _ | i)
    exacts [hcω0, hcτ0, hg i]
  have hgΓ : ∀ (Γ : MMP.Mori.PrimeDivisor X) (i : Fin m'), x ∈ Γ.support →
      X.ord (g i) Γ.genericPoint = (C i).coeff Γ := by
    intro Γ i hΓ
    have hZ : Γ.component = Z0 := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
    rw [hφ i Γ ⟨x, hΓ, hV i⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
  have key := sum_ord_functionFieldMap_eq_zero (f := D.f) D.E G hG w fun Γ hΓ => by
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd β
    have e1 : (Γ.ordForm ω : ℝ) = X.ord cω Γ.genericPoint + NΓ := by
      exact_mod_cast (by simpa using hNΓ 1 ω hω0)
    have e2 : (Γ.ordForm τ : ℝ) = X.ord cτ Γ.genericPoint + m * NΓ := by
      exact_mod_cast hNΓ m τ hτ.1
    have e3 : (Γ.ordForm τ : ℝ) + m * (Δ.coeff Γ : ℝ) = 0 := by
      exact_mod_cast hτ.2 Γ ⟨x, hΓ, hU⟩
    have e4 := hsum Γ
    rw [QDivisor.coeff_toRDivisor] at e4
    simp only [Fintype.sum_option, G, w, Option.elim]
    simp_rw [hgΓ Γ _ hΓ]
    have e5 : ∑ i, ((C i).coeff Γ : ℝ) * r i = ∑ i, r i * ((C i).coeff Γ : ℝ) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    field_simp
    linear_combination (m : ℝ) * e1 - e2 + e3 - (m : ℝ) * e4 + (m : ℝ) * e5
  have hcoeff : ∀ i, ((C' i).coeff D.E : ℝ) =
      D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint := by
    intro i
    obtain ⟨hC, hCp⟩ := hpb i
    exact_mod_cast coeff_isPullback_eq_ord_evalFF hCp (hφ i) D.E (hV i) Z0
  have h1 : (D.ordPullback ω : ℝ) =
      D.Y.ord (functionFieldMap D.f cω) D.E.genericPoint + N := by
    exact_mod_cast (by simpa using hN 1 ω hω0)
  have h2 : (D.ordPullback τ : ℝ) =
      D.Y.ord (functionFieldMap D.f cτ) D.E.genericPoint + m * N := by
    exact_mod_cast hN m τ hτ.1
  have h3 : (m : ℝ) * a = D.ordPullback τ := by exact_mod_cast hτa
  simp only [Fintype.sum_option, G, w, Option.elim] at key
  simp_rw [hcoeff]
  field_simp at key
  have e5 : ∑ i, r i * (D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint : ℝ) =
      ∑ i, (D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint : ℝ) * r i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e5]
  have e6 : (m : ℝ) * (D.ordPullback ω -
      ∑ i, (D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint : ℝ) * r i) = m * a := by
    linear_combination (m : ℝ) * h1 - key - h2 - h3
  have := mul_left_cancel₀ hm0 e6
  linarith

/-- **The log discrepancy is one plus the Kollár–Mori discrepancy.** Let `(X, Δ)` be a pair with
canonical divisor `K` of dimension `n` and `(Y, f, E)` a prime divisor over `X` whose
Kollár–Mori discrepancy is `a = a(E, X, Δ)`. With the canonical divisors of `X` and `Y` cut out by
one rational top form, a real number `b` is the log discrepancy `A(E, X, Δ)` if and only if `f`
is proper and `b = 1 + a`. -/
@[mmp "lem_mmp_km_log_discrepancy_dictionary"]
theorem isLogDiscrepancy_iff_of_isDiscrepancy {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} {a : ℚ} (ha : MMP.Mori.IsDiscrepancy sX n K Δ D a) (b : ℝ) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) D b ↔
      IsProper D.f ∧ b = 1 + (a : ℝ) := by
  refine ⟨fun hb => ⟨hb.2.1, eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha hb⟩, ?_⟩
  rintro ⟨hf, rfl⟩
  obtain ⟨hX, hK, m, hm, ⟨M, hM, hMc⟩, -⟩ := id ha
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨M', hM'⟩ := exists_isPullback_of_isDominant D.f hMc
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hb : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) D
      (1 + (D.ordPullback ω : ℝ) - ∑ _i : Fin 1, (1 / (m : ℝ)) * (M'.coeff D.E : ℝ)) := by
    refine ⟨hX, hf, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, 1, fun _ => 1 / (m : ℝ),
      fun _ => M, fun _ => M', fun _ => hMc, fun Γ => ?_, fun _ => ⟨_, hM'⟩, rfl⟩
    have hMΓ : (M.coeff Γ : ℚ) = m * (K.coeff Γ + Δ.coeff Γ) := by
      have := congrArg (fun G : QDivisor X => G.coeff Γ) hM
      simp at this
      linear_combination this
    have hMΓ' : (M.coeff Γ : ℝ) = m * (K.coeff Γ + Δ.coeff Γ) := by exact_mod_cast hMΓ
    rw [QDivisor.coeff_toRDivisor, Fin.sum_univ_one, hMΓ', hω Γ]
    field_simp
  rw [← eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha hb]
  exact hb

/-- A divisor `(Y, f, E)` over a pair `(X, Δ)`, with `f` proper and Kollár–Mori discrepancy `a`,
has log discrepancy `1 + a`. -/
theorem isLogDiscrepancy_one_add_of_isDiscrepancy {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} {a : ℚ} (ha : MMP.Mori.IsDiscrepancy sX n K Δ D a)
    (hf : IsProper D.f) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) D (1 + (a : ℝ)) :=
  (isLogDiscrepancy_iff_of_isDiscrepancy ha _).mpr ⟨hf, rfl⟩

omit [PerfectField k] in
/-- A log discrepancy at index `n` forces `n = dim X`. -/
theorem IsLogDiscrepancy.topologicalKrullDim_eq {n : ℕ} {B : RDivisor X} {D : DivisorOver k sX}
    {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) : topologicalKrullDim X = n := by
  obtain ⟨-, -, -, -, ⟨K, hK, -⟩, -⟩ := h
  exact hK.topologicalKrullDim_eq

/-- **The log discrepancy depends only on the valuation.** Two divisors `D`, `D'` over `X` with
the same valuation have the same log discrepancy with respect to `(X, B)`, whatever the models
realizing them, the rational top forms, the presentations of `K_X + B` by Cartier divisors and
the indices `n`, `n'` used to compute them. -/
theorem IsLogDiscrepancy.eq_of_valuation_eq {n n' : ℕ} {B : RDivisor X}
    {D D' : DivisorOver k sX} {a a' : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a)
    (h' : MMP.Intersection.IsLogDiscrepancy sX n' B D' a') (hv : D.valuation = D'.valuation) :
    a = a' := by
  classical
  have hn' := (IsLogDiscrepancy.topologicalKrullDim_eq h').symm.trans
    (IsLogDiscrepancy.topologicalKrullDim_eq h)
  obtain rfl : n' = n := by exact_mod_cast hn'
  obtain ⟨hX, -, ω, hω0, ⟨K, hK, -⟩, m, r, C, C', hCc, hsum, hpb, rfl⟩ := h
  obtain ⟨-, -, ω', hω0', -, m₂, r₂, C₂, C₂', hCc₂, hsum₂, hpb₂, rfl⟩ := h'
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isLocallyNoetherian
  have := D'.isNormal
  have := D'.isDominant
  have hn := hK.topologicalKrullDim_eq
  let := MMP.Mori.functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨β, N, hN⟩ := D.exists_ordPullback_eq hX hn
  have hcen := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hv
  have hω' := MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv ω'
  set x := D.f D.E.genericPoint with hx
  choose V hV φ hφ using fun i => hCc i x
  choose V₂ hV₂ φ₂ hφ₂ using fun j => hCc₂ j x
  let Z0 := MMP.Mori.pointComponent x
  let g : Fin m → X.functionField := fun i =>
    MMP.Threefold.Mori.Helpers.evalFF Z0 ((φ i : MMP.Mori.RationalFunctions X))
  let g₂ : Fin m₂ → X.functionField := fun j =>
    MMP.Threefold.Mori.Helpers.evalFF Z0 ((φ₂ j : MMP.Mori.RationalFunctions X))
  have hg : ∀ i, g i ≠ 0 := fun i => ((φ i).isUnit.map _).ne_zero
  have hg₂ : ∀ j, g₂ j ≠ 0 := fun j => ((φ₂ j).isUnit.map _).ne_zero
  set cω := (MMP.Mori.ZTensorPower.basis β 1).repr ω () with hcω
  set cω' := (MMP.Mori.ZTensorPower.basis β 1).repr ω' () with hcω'
  have hcω0 : cω ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero β hω0
  have hcω0' : cω' ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero β hω0'
  let G : Option (Option (Fin m ⊕ Fin m₂)) → X.functionField := fun j =>
    Option.elim j cω fun j => Option.elim j cω' fun j => Sum.elim g g₂ j
  let w : Option (Option (Fin m ⊕ Fin m₂)) → ℝ := fun j =>
    Option.elim j 1 fun j => Option.elim j (-1) fun j => Sum.elim (fun i => -r i) r₂ j
  have hG : ∀ j, G j ≠ 0 := by
    rintro (_ | _ | i | j)
    exacts [hcω0, hcω0', hg i, hg₂ j]
  have hZ : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.component = Z0 := fun Γ => Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  have hgΓ : ∀ (Γ : MMP.Mori.PrimeDivisor X) (i : Fin m), x ∈ Γ.support →
      X.ord (g i) Γ.genericPoint = (C i).coeff Γ := by
    intro Γ i hΓ
    rw [hφ i Γ ⟨x, hΓ, hV i⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
  have hgΓ₂ : ∀ (Γ : MMP.Mori.PrimeDivisor X) (j : Fin m₂), x ∈ Γ.support →
      X.ord (g₂ j) Γ.genericPoint = (C₂ j).coeff Γ := by
    intro Γ j hΓ
    rw [hφ₂ j Γ ⟨x, hΓ, hV₂ j⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
  have key := sum_ord_functionFieldMap_eq_zero (f := D.f) D.E G hG w fun Γ hΓ => by
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd β
    have e1 : (Γ.ordForm ω : ℝ) = X.ord cω Γ.genericPoint + NΓ := by
      exact_mod_cast (by simpa using hNΓ 1 ω hω0)
    have e2 : (Γ.ordForm ω' : ℝ) = X.ord cω' Γ.genericPoint + NΓ := by
      exact_mod_cast (by simpa using hNΓ 1 ω' hω0')
    have e3 := hsum Γ
    have e4 := hsum₂ Γ
    simp only [Fintype.sum_option, Fintype.sum_sum_type, G, w, Option.elim, Sum.elim_inl,
      Sum.elim_inr]
    simp_rw [hgΓ Γ _ hΓ, hgΓ₂ Γ _ hΓ]
    have e5 : ∑ i, ((C i).coeff Γ : ℝ) * -r i = -∑ i, r i * ((C i).coeff Γ : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e6 : ∑ j, ((C₂ j).coeff Γ : ℝ) * r₂ j = ∑ j, r₂ j * ((C₂ j).coeff Γ : ℝ) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e5, e6]
    linear_combination e3 - e4 - e1 + e2
  have hcoeff : ∀ i, ((C' i).coeff D.E : ℝ) =
      D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint := by
    intro i
    obtain ⟨hC, hCp⟩ := hpb i
    exact_mod_cast coeff_isPullback_eq_ord_evalFF hCp (hφ i) D.E (hV i) Z0
  have hcoeff₂ : ∀ j, ((C₂' j).coeff D'.E : ℝ) =
      D.Y.ord (functionFieldMap D.f (g₂ j)) D.E.genericPoint := by
    intro j
    obtain ⟨hC, hCp⟩ := hpb₂ j
    rw [coeff_isPullback_eq_ord_evalFF hCp (hφ₂ j) D'.E (hcen ▸ hV₂ j) Z0,
      ord_functionFieldMap_eq_of_valuationOver_eq D.E D'.E hv (hg₂ j)]
  have h1 : (D.ordPullback ω : ℝ) =
      D.Y.ord (functionFieldMap D.f cω) D.E.genericPoint + N := by
    exact_mod_cast (by simpa using hN 1 ω hω0)
  have h2 : (D'.ordPullback ω' : ℝ) =
      D.Y.ord (functionFieldMap D.f cω') D.E.genericPoint + N := by
    rw [← hω']
    exact_mod_cast (by simpa using hN 1 ω' hω0')
  simp only [Fintype.sum_option, Fintype.sum_sum_type, G, w, Option.elim, Sum.elim_inl,
    Sum.elim_inr] at key
  simp_rw [hcoeff, hcoeff₂]
  have e5 : ∑ i, (D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint : ℝ) * -r i =
      -∑ i, r i * (D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e6 : ∑ j, (D.Y.ord (functionFieldMap D.f (g₂ j)) D.E.genericPoint : ℝ) * r₂ j =
      ∑ j, r₂ j * (D.Y.ord (functionFieldMap D.f (g₂ j)) D.E.genericPoint : ℝ) :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e5, e6] at key
  linear_combination h1 - h2 + key

/-- **The log discrepancy is unique**: it does not depend on the rational top form, on the
presentation of `K_X + B` by Cartier divisors, nor on the index at which it is computed. -/
theorem IsLogDiscrepancy.unique {n n' : ℕ} {B : RDivisor X} {D : DivisorOver k sX} {a a' : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a)
    (h' : MMP.Intersection.IsLogDiscrepancy sX n' B D a') : a = a' :=
  IsLogDiscrepancy.eq_of_valuation_eq h h' rfl

/-- For a pair `(X, Δ)` with `ℚ`-boundary, the independence of the log discrepancy from the
model follows from the dictionary `isLogDiscrepancy_iff_of_isDiscrepancy` and the model
independence of the Kollár–Mori discrepancy. -/
theorem IsLogDiscrepancy.eq_of_valuation_eq_of_isPair {n n' : ℕ} {Δ : QDivisor X}
    (hP : MMP.Mori.IsPair sX Δ) {D D' : DivisorOver k sX} {a a' : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) D a)
    (h' : MMP.Intersection.IsLogDiscrepancy sX n' (QDivisor.toRDivisor Δ) D' a')
    (hv : D.valuation = D'.valuation) : a = a' := by
  obtain ⟨-, -, -, -, ⟨K, hK, -⟩, -⟩ := id h
  obtain rfl : n' = n := by
    exact_mod_cast (IsLogDiscrepancy.topologicalKrullDim_eq h').symm.trans
      (IsLogDiscrepancy.topologicalKrullDim_eq h)
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D'
  have hcc : c = c' :=
    MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hv
      (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hP.1 hv) hc hc'
  rw [((isLogDiscrepancy_iff_of_isDiscrepancy hc a).mp h).2,
    ((isLogDiscrepancy_iff_of_isDiscrepancy hc' a').mp h').2, hcc]

end MMP.Threefold.Bridges
