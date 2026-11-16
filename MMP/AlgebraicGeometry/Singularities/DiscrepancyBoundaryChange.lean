module
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold

/-!
# Discrepancies under a change of boundary, and on a common model

Two comparisons of discrepancies over a perfect field `k`.

*Changing the boundary.* Let `(X, Δ)` be a pair with canonical divisor `K` of dimension `n`,
`Δ'` a `ℚ`-Cartier `ℚ`-divisor on `X` and `(Y, f, E)` a divisor over `X`. Then `(X, Δ + Δ')` is a
pair, and `a(E, X, Δ + tΔ') = a(E, X, Δ) - t · coeff_E(f^*Δ')` for every `t ∈ ℚ`. If
`a = a(E, X, Δ)` and `a' = a(E, X, Δ + tΔ')` are computed by generators `τ` of `𝒪_X(m(K + Δ))` and
`τ'` of `𝒪_X(m'(K + Δ + tΔ'))` near `x = f(η_E)`, write `τ = c · b^{⊗m}`, `τ' = c' · b^{⊗m'}`
along a basis `b`. With `t = p/q` and `ψ` a local equation of the Cartier divisor `MΔ'` at `x`,
the rational function `G = (c^{m'} c'^{-m})^{qM} ψ^{-mm'p}` has order zero along every prime
divisor through `x`, so by algebraic Hartogs it is a unit at `x` and `v_E(f^*G) = 0`; since
`v_E(f^*ψ) = coeff_E(f^*(MΔ'))`, this reads `a - a' = t · coeff_E(f^*Δ')`.

*Comparison on a common model.* Let `f : X ⟶ Y`, `f' : X' ⟶ Y` be proper birational morphisms of
normal varieties, `Δ`, `Δ'` `ℚ`-divisors with `f_*Δ = f'_*Δ'`, `-(K_X + Δ)` `ℚ`-Cartier and
`f`-nef, `K_{X'} + Δ'` `ℚ`-Cartier and `f'`-nef, and `g : Z ⟶ X`, `g' : Z ⟶ X'` proper birational
morphisms from a normal variety with `g ≫ f = g' ≫ f' = h`. Then
`H = ∑_F (a(F, X, Δ) - a(F, X', Δ')) F` is `ℚ`-Cartier and `h`-nef, and vanishes along every prime
divisor of `Z` that is not `h`-exceptional. Indeed `H = Δ'_Z - Δ_Z` for the crepant boundaries,
`H ∼_ℚ g'^*(K_{X'} + Δ') - g^*(K_X + Δ)`, whose degree on an `h`-contracted curve is non-negative
by the projection formula, and at a non-exceptional `F` both discrepancies equal minus the
coefficient of `h(F)` in `f_*Δ = f'_*Δ'`.

## Main results

* `MMP.Mori.IsPairWith.isDiscrepancy_add_smul_iff`: `(X, Δ + Δ')` is a pair, and for every
  `t ∈ ℚ`, `a` is the discrepancy `a(E, X, Δ)` if and only if `a - t · coeff_E(f^*Δ')` is the
  discrepancy `a(E, X, Δ + tΔ')`.
* `MMP.Mori.isRelativelyNef_of_isDiscrepancy_sub`: `H` is `ℚ`-Cartier, `h`-nef, and supported on
  the `h`-exceptional prime divisors.

## Implementation notes

As in `MMP.Mori.IsDiscrepancy`, "`a` is the discrepancy `a(E, X, Δ)`" is a predicate on `a`, so
the equation of discrepancies is stated as an equivalence of these predicates, which also
transports existence in both directions; likewise `H` is any `ℚ`-divisor on `Z` whose coefficient
at `F` is `a - a'` whenever `a`, `a'` are the discrepancies of `F` over `(X, Δ)` and `(X', Δ')`.
The pull-back `f^*Δ'` is `MMP.Mori.QDivisor.IsPullback`; its condition (no generic point of `Y`
maps into `Supp Δ'`) holds since `f` is birational, and is asserted rather than assumed. The
push-forward `f_*Δ` is `MMP.Mori.RationalMap.transformDivisor`, and relative nefness
`MMP.Mori.QDivisor.IsRelativelyNef` includes being `ℚ`-Cartier. The structure morphisms of `X`,
`X'` lie over that of `Y`, and `Z` carries the structure morphism `g ≫ s_X`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Lemma 2.27 and
  the proof of 3.38
-/

@[expose] public section

open CategoryTheory

universe u

namespace MMP.Mori

section BoundaryChange

open AlgebraicGeometry

private theorem coe_irreducibleComponent_eq_univ {X : Scheme.{u}} [IsIntegral X]
    (Z : irreducibleComponents X) : Z.1 = Set.univ := by
  simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using Z.2

/-- On an integral scheme, a dominant morphism maps every generic point of a component outside the
support of a `ℚ`-divisor. -/
private theorem map_componentGenericPoint_notMem_supp {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (D : QDivisor X) (Z : irreducibleComponents Y) : f (componentGenericPoint Y Z) ∉ D.supp := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
  exact MMP.Fourfold.genericPoint_notMem_supp D

private theorem ord_zpow_mul_zpow {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y)
    {a b : Y.functionField} (ha : a ≠ 0) (hb : b ≠ 0) (i j : ℤ) :
    Y.ord (a ^ i * b ^ j) z = i * Y.ord a z + j * Y.ord b z := by
  rw [Scheme.ord_mul (zpow_ne_zero _ ha) (zpow_ne_zero _ hb), ord_zpow _ ha, ord_zpow _ hb]

/-- The order of `(c^{m'} c'^{-m})^{qM} ψ^{-mm'p}` at a point where `c`, `c'` and `ψ` have orders
`m α - m N`, `m' α' - m' N` and `M β`, with `q t = p`. -/
private theorem ord_boundaryChange_eq {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (z : Y) {c c' ψ : Y.functionField} (hc : c ≠ 0) (hc' : c' ≠ 0) (hψ : ψ ≠ 0)
    {m m' M q : ℕ} {p : ℤ} {t α α' β N : ℚ} (htpq : (q : ℚ) * t = p)
    (h₁ : (Y.ord c z : ℚ) + m * N = m * α) (h₂ : (Y.ord c' z : ℚ) + m' * N = m' * α')
    (hψz : (Y.ord ψ z : ℚ) = M * β) :
    (Y.ord ((c ^ (m' : ℤ) * c' ^ (-(m : ℤ))) ^ ((q * M : ℕ) : ℤ) *
      ψ ^ (-((m * m' : ℕ) * p : ℤ))) z : ℚ) = q * M * m * m' * (α - α' - t * β) := by
  rw [ord_zpow_mul_zpow z (mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc')) hψ,
    ord_zpow_mul_zpow z hc hc']
  push_cast
  linear_combination (q * M * m' : ℚ) * h₁ - (q * M * m : ℚ) * h₂ - (m * m' * p : ℚ) * hψz +
    (m * m' * M * β : ℚ) * htpq

/-- If `(c^{m'} c'^{-m})^{qM} ψ^{-mm'p}` has order zero in the situation of
`ord_boundaryChange_eq`, then `α - α' = t β`. -/
private theorem sub_eq_mul_of_ord_eq_zero {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (z : Y) {c c' ψ : Y.functionField} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hψ : ψ ≠ 0) {m m' M q : ℕ} (hm : 0 < m) (hm' : 0 < m') (hM : 0 < M) (hq : 0 < q) {p : ℤ}
    {t α α' β N : ℚ} (htpq : (q : ℚ) * t = p) (h₁ : (Y.ord c z : ℚ) + m * N = m * α)
    (h₂ : (Y.ord c' z : ℚ) + m' * N = m' * α') (hψz : (Y.ord ψ z : ℚ) = M * β)
    (h0 : Y.ord ((c ^ (m' : ℤ) * c' ^ (-(m : ℤ))) ^ ((q * M : ℕ) : ℤ) *
      ψ ^ (-((m * m' : ℕ) * p : ℤ))) z = 0) :
    α - α' = t * β := by
  have h := ord_boundaryChange_eq z hc hc' hψ htpq h₁ h₂ hψz
  rw [h0, Int.cast_zero, eq_comm, mul_eq_zero, sub_eq_zero] at h
  exact h.resolve_left (by positivity)

private theorem ordUnit_eq_ord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (Γ : MMP.Mori.PrimeDivisor X)
    (u : (X.presheaf.stalk (componentGenericPoint X Γ.component))ˣ) :
    Γ.ordUnit u = X.ord (algebraMap (X.presheaf.stalk (componentGenericPoint X Γ.component))
      X.functionField u) Γ.genericPoint := by
  have hne : algebraMap (X.presheaf.stalk (componentGenericPoint X Γ.component))
      X.functionField (u : X.presheaf.stalk _) ≠ 0 := (u.isUnit.map _).ne_zero
  symm
  rw [Scheme.ord_eq_iff Γ.coheight_genericPoint hne]
  have : Ring.KrullDimLE 1 Γ.localRing := krullDimLE_of_coheight_le Γ.coheight_genericPoint.le
  have h := Γ.valuation_eq_exp_ordUnit u
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac] at h
  unfold Scheme.ordHom
  convert h using 1 <;> rfl

private theorem ord_functionFieldMap_eq_coeff {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] {B : Divisor X}
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp}
    {B' : Divisor Y} (h : B.IsPullback f hB B') {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : B.IsLocalEquation U ψ) (E : MMP.Mori.PrimeDivisor Y) (hE : f E.genericPoint ∈ U)
    (W : irreducibleComponents X) :
    Y.ord (functionFieldMap f (algebraMap (X.presheaf.stalk (componentGenericPoint X W))
      X.functionField ((ψ : RationalFunctions X) W))) E.genericPoint = B'.coeff E := by
  have hE' : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hE
  rw [h U ψ hψ E hE']
  have hW : f (componentGenericPoint Y E.component) ∈ W.1 := by
    rw [coe_irreducibleComponent_eq_univ W]; trivial
  have hsp : f (componentGenericPoint Y E.component) ⤳ componentGenericPoint X W := by
    apply specializes_of_eq
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint,
      MMP.Fourfold.componentGenericPoint_eq_genericPoint,
      map_genericPoint_of_isDominant]
  let a : (X.presheaf.stalk (f (componentGenericPoint Y E.component)))ˣ :=
    Units.map (X.presheaf.stalkSpecializes hsp).hom.toMonoidHom
      (Units.map (RationalFunctions.component X W).toMonoidHom ψ)
  have ha : (stalkToRationalFunctions X hW).hom a = (ψ : RationalFunctions X) W := by
    change (X.presheaf.stalkSpecializes hsp ≫ X.presheaf.stalkSpecializes _).hom _ = _
    rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  rw [pullbackComponent_eq hB hψ _ hW a ha, ordUnit_eq_ord]
  congr 1
  change functionFieldMap f _ = algebraMap _ _ ((f.stalkMap _).hom a.val)
  rw [← functionFieldMap_algebraMap_stalk]
  congr 1
  exact (algebraMap_stalkSpecializes hsp ((ψ : RationalFunctions X) W)).symm

private theorem ord_algebraMap_component_eq_ord {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (Γ : MMP.Mori.PrimeDivisor X)
    (ψ : (RationalFunctions X)ˣ) (W : irreducibleComponents X) :
    X.ord (algebraMap (X.presheaf.stalk (componentGenericPoint X W)) X.functionField
      ((ψ : RationalFunctions X) W)) Γ.genericPoint = Γ.ord ψ := by
  have := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)
  obtain rfl : W = Γ.component := Subsingleton.elim _ _
  rw [Γ.ord_eq_ordUnit, ordUnit_eq_ord]
  rfl

private theorem sub_eq_mul_coeff_of_isDiscrepancy {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ Δ' : QDivisor X}
    (hΔ' : Δ'.IsQCartier) (E : DivisorOver k sX) (t : ℚ) {a a' : ℚ}
    (ha : IsDiscrepancy sX n K Δ E a) (ha' : IsDiscrepancy sX n K (Δ + t • Δ') E a') :
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    ∀ (hB : ∀ Z : irreducibleComponents E.Y, E.f (componentGenericPoint E.Y Z) ∉ Δ'.supp)
      (B' : QDivisor E.Y), Δ'.IsPullback E.f hB B' → a - a' = t * B'.coeff E.E := by
  intro hB B' hpb
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  obtain ⟨-, -, m', hm', -, U', hU', τ', hτ', hτa'⟩ := ha'
  let := functionFieldAlgebra sX
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N, hN⟩ := E.exists_ordPullback_eq hX hn
  set x := E.f E.E.genericPoint with hx
  obtain ⟨M, hM, D', hD', cD'⟩ := hΔ'.exists_pos
  obtain ⟨U1, hxU1, ψ, hψ⟩ := cD' x
  set W : irreducibleComponents X := pointComponent x
  set c := (ZTensorPower.basis b m).repr τ () with hc_def
  set c' := (ZTensorPower.basis b m').repr τ' () with hc'_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ.1
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ'.1
  set ψv : X.functionField := algebraMap (X.presheaf.stalk (componentGenericPoint X W))
    X.functionField ((ψ : RationalFunctions X) W) with hψv_def
  have hψv : ψv ≠ 0 := ((ψ.isUnit.map (RationalFunctions.component X W)).map _).ne_zero
  set p := t.num
  set q : ℕ := t.den
  have htpq : (q : ℚ) * t = p := by
    rw [mul_comm]; exact_mod_cast Rat.mul_den_eq_num t
  set g : X.functionField := c ^ (m' : ℤ) * c' ^ (-(m : ℤ)) with hg_def
  have hg : g ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc')
  set G : X.functionField := g ^ ((q * M : ℕ) : ℤ) * ψv ^ (-((m * m' : ℕ) * p : ℤ)) with hG_def
  have hG : G ≠ 0 := mul_ne_zero (zpow_ne_zero _ hg) (zpow_ne_zero _ hψv)
  have hD'c : ∀ Γ : MMP.Mori.PrimeDivisor X, (D'.coeff Γ : ℚ) = M * Δ'.coeff Γ := fun Γ => by
    simpa using congrArg (fun F => DivisorWithCoeffs.coeff F Γ) hD'
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support → X.ord G Γ.genericPoint = 0 := by
    intro Γ hΓ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have e1 := hτ.2 Γ ⟨_, hΓ, hU⟩
    have e2 := hτ'.2 Γ ⟨_, hΓ, hU'⟩
    have f1 : (Γ.ordForm τ : ℚ) = (X.ord c Γ.genericPoint : ℚ) + m * NΓ := by
      exact_mod_cast hNΓ m τ hτ.1
    have f2 : (Γ.ordForm τ' : ℚ) = (X.ord c' Γ.genericPoint : ℚ) + m' * NΓ := by
      exact_mod_cast hNΓ m' τ' hτ'.1
    have e3 : (X.ord ψv Γ.genericPoint : ℚ) = M * Δ'.coeff Γ := by
      rw [hψv_def, ord_algebraMap_component_eq_ord, ← hψ Γ ⟨_, hΓ, hxU1⟩, hD'c]
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at e2
    have h := ord_boundaryChange_eq Γ.genericPoint hc hc' hψv htpq (m := m) (m' := m') (M := M)
      (N := NΓ) (α := -Δ.coeff Γ) (α' := -(Δ.coeff Γ + t * Δ'.coeff Γ)) (β := Δ'.coeff Γ)
      (by linear_combination e1 - f1) (by linear_combination e2 - f2) e3
    rw [hG_def, hg_def, ← Int.cast_inj (α := ℚ), h, Int.cast_zero]
    ring
  obtain ⟨u, hu, hug⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero _ hG hord
  have hY0 : E.Y.ord (functionFieldMap E.f G) E.E.genericPoint = 0 := by
    rw [← hug, functionFieldMap_algebraMap_stalk]
    exact E.E.ord_algebraMap_of_isUnit (hu.map _)
  obtain ⟨DY, hDY, hpbY⟩ := hpb M hM D' hD' cD'
  have hψY := ord_functionFieldMap_eq_coeff E.f hpbY hψ E.E hxU1 W
  rw [← hψv_def] at hψY
  have hDYc : (DY.coeff E.E : ℚ) = M * B'.coeff E.E := by
    simpa using congrArg (fun F => DivisorWithCoeffs.coeff F E.E) hDY
  have hfc : functionFieldMap E.f c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap E.f c' ≠ 0 := (map_ne_zero _).mpr hc'
  have hfψ : functionFieldMap E.f ψv ≠ 0 := (map_ne_zero _).mpr hψv
  rw [hG_def, hg_def] at hY0
  simp only [map_mul, map_zpow₀] at hY0
  have h1 : (E.ordPullback τ : ℚ) =
      (E.Y.ord (functionFieldMap E.f c) E.E.genericPoint : ℚ) + m * N := by
    exact_mod_cast hN m τ hτ.1
  have h2 : (E.ordPullback τ' : ℚ) =
      (E.Y.ord (functionFieldMap E.f c') E.E.genericPoint : ℚ) + m' * N := by
    exact_mod_cast hN m' τ' hτ'.1
  exact sub_eq_mul_of_ord_eq_zero E.E.genericPoint hfc hfc' hfψ hm hm' hM t.den_pos htpq
    (N := N) (α := a) (α' := a') (β := B'.coeff E.E) (by linear_combination -h1 - hτa)
    (by linear_combination -h2 - hτa') (by rw [hψY, hDYc]) hY0

private theorem isQCartier_smul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {Δ' : QDivisor X} (hΔ' : Δ'.IsQCartier) (t : ℚ) : (t • Δ').IsQCartier := by
  obtain ⟨M, hM, D', hD', cD'⟩ := hΔ'.exists_pos
  refine ⟨(t.den * M : ℕ), by exact_mod_cast (Nat.mul_pos t.den_pos hM).ne',
    t.num • D', ?_, cD'.zsmul _⟩
  rw [map_zsmul, hD', ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
    ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
  congr 1
  push_cast
  rw [← Rat.mul_den_eq_num t]
  ring

end BoundaryChange

namespace IsPairWith

open AlgebraicGeometry

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
  {Δ : QDivisor X}

/-- **Discrepancies under a change of boundary** (Kollár–Mori, the formula behind Lemma 2.27).
Let `(X, Δ)` be a pair with canonical divisor `K` of dimension `n` over a perfect field, `Δ'` a
`ℚ`-Cartier `ℚ`-divisor and `(Y, f, E)` a divisor over `X`. Then `(X, Δ + Δ')` is a pair, and for
the pull-back `f^*Δ'`, `a(E, X, Δ + Δ') = a(E, X, Δ) - coeff_E(f^*Δ')`, and more generally
`a(E, X, Δ + tΔ') = a(E, X, Δ) - t · coeff_E(f^*Δ')` for every `t ∈ ℚ`. -/
@[mmp "lem_km2b_discrepancy_sub_boundary_formula"]
public theorem isDiscrepancy_add_smul_iff (hP : IsPairWith sX n K Δ) {Δ' : QDivisor X}
    (hΔ' : Δ'.IsQCartier) (E : DivisorOver k sX) :
    IsPairWith sX n K (Δ + Δ') ∧
      haveI := E.isLocallyNoetherian
      haveI := E.isNormal
      ∃ hB : ∀ Z : irreducibleComponents E.Y, E.f (componentGenericPoint E.Y Z) ∉ Δ'.supp,
        ∀ B' : QDivisor E.Y, Δ'.IsPullback E.f hB B' →
          (∀ a : ℚ, IsDiscrepancy sX n K (Δ + Δ') E (a - B'.coeff E.E) ↔
            IsDiscrepancy sX n K Δ E a) ∧
          ∀ t : ℚ, ∀ a : ℚ, IsDiscrepancy sX n K (Δ + t • Δ') E (a - t * B'.coeff E.E) ↔
            IsDiscrepancy sX n K Δ E a := by
  have hpair : ∀ t : ℚ, IsPairWith sX n K (Δ + t • Δ') := fun t => by
    refine ⟨hP.1, hP.2.1, ?_⟩
    obtain ⟨m, hm, h1⟩ := hP.2.2.exists_pos
    obtain ⟨m1, hm1, h2⟩ := (isQCartier_smul hΔ' t).exists_pos
    exact QDivisor.isQCartier_iff_exists_pos.mpr ⟨m * m1, Nat.mul_pos hm hm1,
      MMP.Threefold.Mori.Helpers.isCartierDivisor_mul_smul_add h1 h2⟩
  have := E.isIntegral
  have := E.isDominant
  have hB := map_componentGenericPoint_notMem_supp E.f Δ'
  refine ⟨by simpa using hpair 1, hB, fun B' hpb => ?_⟩
  have key : ∀ t a : ℚ, IsDiscrepancy sX n K (Δ + t • Δ') E (a - t * B'.coeff E.E) ↔
      IsDiscrepancy sX n K Δ E a := by
    intro t a
    refine ⟨fun ha' => ?_, fun ha => ?_⟩
    · obtain ⟨a0, ha0⟩ := MMP.Threefold.Mori.Helpers.exists_isDiscrepancy_add
        (isQCartier_smul hΔ' (-t)) ha'
      rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero] at ha0
      have h := sub_eq_mul_coeff_of_isDiscrepancy hΔ' E t ha0 ha' hB B' hpb
      exact (show a0 = a by linarith) ▸ ha0
    · obtain ⟨a', ha'⟩ := MMP.Threefold.Mori.Helpers.exists_isDiscrepancy_add
        (isQCartier_smul hΔ' t) ha
      have h := sub_eq_mul_coeff_of_isDiscrepancy hΔ' E t ha ha' hB B' hpb
      exact (show a' = a - t * B'.coeff E.E by linarith) ▸ ha'
  exact ⟨fun a => by simpa using key 1 a, key⟩

end IsPairWith

section CommonModel

open AlgebraicGeometry hiding PrimeDivisor

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- If `-(K + Δ)` is `ℚ`-Cartier for a canonical divisor `K`, then `(X, Δ)` is a pair. -/
private theorem isPair_of_isQCartier_neg {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ}
    (hX : IsNormalVariety k sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {Δ : QDivisor X} (h : (-(Divisor.toQDivisor K + Δ)).IsQCartier) : IsPair sX Δ := by
  obtain ⟨m, hm, hC⟩ := h
  exact ⟨hX, n, K, hK, -m, neg_ne_zero.mpr hm, by rwa [neg_smul, ← smul_neg]⟩

section Crepancy

/-- The order of `c ^ m * g⁻¹` along a point, for nonzero rational functions `c` and `g`. -/
private theorem ord_zpow_mul_inv {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y)
    {c g : Y.functionField} (hc : c ≠ 0) (hg : g ≠ 0) (m : ℤ) :
    Y.ord (c ^ m * g⁻¹) z = m * Y.ord c z - Y.ord g z := by
  rw [Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg), MMP.Mori.ord_zpow _ hc,
    ← zpow_neg_one, MMP.Mori.ord_zpow _ hg]
  ring

variable {k : Type u} [Field k] [PerfectField k] {X U : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]

omit [CompactSpace X] in
/-- The form `c ^ m g⁻¹ • e^m`, built from a canonical form `ω = c • e` and a local equation `g`
of `E = m (K + B)` on `V`, generates `m (K + B)` on `V`. -/
private theorem generatesOn_smul_basis {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {n : ℕ}
    {K : Divisor X} {B : QDivisor X}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]))
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0)
    (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ) {m : ℕ} {E : Divisor X}
    (hE : Divisor.toQDivisor E = (m : ℤ) • (Divisor.toQDivisor K + B)) {V : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : E.IsLocalEquation V φ) (Z0 : irreducibleComponents X) :
    letI := functionFieldAlgebra sX
    GeneratesOn B m V (((ZTensorPower.basis b 1).repr ω () ^ (m : ℤ) *
      (MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X))⁻¹) •
        ZTensorPower.basis b (m : ℤ) ()) := by
  let := functionFieldAlgebra sX
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X)
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set τ : RationalPluriForms sX n m := (c ^ (m : ℤ) * g⁻¹) • ZTensorPower.basis b (m : ℤ) ()
    with hτ
  have hτr : (ZTensorPower.basis b (m : ℤ)).repr τ () = c ^ (m : ℤ) * g⁻¹ := by simp [τ]
  have hτ0 : τ ≠ 0 := smul_ne_zero (mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg))
    ((ZTensorPower.basis b (m : ℤ)).ne_zero ())
  refine ⟨hτ0, fun Γ hΓ => ?_⟩
  obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have h1 : (K.coeff Γ : ℤ) = X.ord c Γ.genericPoint + NΓ := by
    rw [← hωK Γ, hNΓ 1 ω hω0]
    simp [hc_def]
  have h2 : (Γ.ordForm τ : ℤ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint + m * NΓ := by
    rw [hNΓ _ τ hτ0, hτr, ord_zpow_mul_inv _ hc hg]
  have h3 : X.ord g Γ.genericPoint = E.coeff Γ := by
    rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents)
        Γ.component Z0]
  have hCq : (E.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by
    rw [mul_add]
    simpa [zsmul_eq_mul] using congrArg (fun D : QDivisor X => D.coeff Γ) hE
  qify at h1 h2 h3
  linear_combination h2 - hCq - h3 - (m : ℚ) * h1

omit [CompactSpace X] in
/-- Coefficientwise crepancy: along a prime divisor `F` of `U`, the pull-back of a Cartier
multiple `E = m (K + B)` has coefficient `m (ord_F div(p^*ω) + Δ_F)` when `K = div(ω)`. -/
private theorem coeff_pullback_eq {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {p : U ⟶ X}
    [IsDominant p] [LocallyOfFiniteType (p ≫ sX)]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {n n' : ℕ} {K : Divisor X}
    (hK' : K.IsCanonicalDivisor sX n') {B : QDivisor X} {Δ : QDivisor U}
    (hcrep : IsCrepantBoundary sX n K B p hY hp Δ) {m : ℕ} (hm0 : 0 < m) {E : Divisor X}
    (hE : Divisor.toQDivisor E = (m : ℤ) • (Divisor.toQDivisor K + B)) (hEc : E.IsCartier)
    {hB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ E.supp}
    {Dp : Divisor U} (hDp : E.IsPullback p hB Dp) {ω : RationalPluriForms sX n' 1}
    (hω0 : ω ≠ 0) (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    (F : MMP.Mori.PrimeDivisor U) :
    (Dp.coeff F : ℚ) =
      m * ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F + Δ.coeff F) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hK := (hcrep F).2.1
  obtain rfl : n = n' := by exact_mod_cast hK.1.symm.trans hK'.1
  have hn := hK.topologicalKrullDim_eq
  set D : DivisorOver k sX := ⟨U, p, hY, hp, F⟩ with hD
  obtain ⟨b, N', hb0⟩ := D.exists_ordPullback_eq hX hn
  have hb : ∀ (m : ℤ) (τ : RationalPluriForms sX n m), τ ≠ 0 → D.ordPullback τ =
      U.ord (functionFieldMap p ((ZTensorPower.basis b m).repr τ ())) F.genericPoint + m * N' :=
    hb0
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨V, hxV, φ, hφ⟩ := hEc (p F.genericPoint)
  let Z0 : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; simp⟩
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X) with hg_def
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set c'' : X.functionField := c ^ (m : ℤ) * g⁻¹ with hc''_def
  have hc'' : c'' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg)
  let τ : RationalPluriForms sX n m := c'' • ZTensorPower.basis b (m : ℤ) ()
  have hτr : (ZTensorPower.basis b (m : ℤ)).repr τ () = c'' := by simp [τ]
  have hτ0 : τ ≠ 0 := smul_ne_zero hc'' ((ZTensorPower.basis b (m : ℤ)).ne_zero ())
  have hgen : GeneratesOn B m V τ := generatesOn_smul_basis hd b hω0 hωK hE hφ Z0
  have hKY : (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F =
      U.ord (functionFieldMap p c) F.genericPoint + N' := by
    have h := hb 1 ω hω0
    have e : D.ordPullback ω = (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F := by
      rw [coeff_divisorOfForm]
      rfl
    rw [← e, h]
    simp [hc_def]
  have hcoeff : Dp.coeff F = U.ord (functionFieldMap p g) F.genericPoint :=
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hDp hφ F hxV Z0
  have hgY : functionFieldMap p g ≠ 0 := (map_ne_zero _).mpr hg
  have hcY : functionFieldMap p c ≠ 0 := (map_ne_zero _).mpr hc
  have hordτ : D.ordPullback τ = m * U.ord (functionFieldMap p c) F.genericPoint
      - U.ord (functionFieldMap p g) F.genericPoint + m * N' := by
    rw [hb _ τ hτ0, hτr, hc''_def, map_mul, map_zpow₀, map_inv₀, ord_zpow_mul_inv _ hcY hgY]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hdisc : IsDiscrepancy sX n K B D
      ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F - Dp.coeff F / m) := by
    refine ⟨hX, hK, m, hm0, ⟨E, hE, hEc⟩, V, hxV, τ, hgen, ?_⟩
    qify at hordτ hKY hcoeff
    rw [hordτ, hKY, hcoeff]
    field_simp
    ring
  have heq := IsDiscrepancy.eq (hcrep F) hdisc
  field_simp at heq
  linear_combination heq

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace U]
    [IsLocallyNoetherian U] [IsNormal U] in
/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

omit [CompactSpace X] in
/-- **Crepancy as a pull-back.** If `Δ` is the crepant boundary of `(X, B)` on `U` and
`K = div(ω)`, then `div(p^*ω) + Δ = p^*(K + B)`. -/
private theorem isPullback_divisorOfForm_add {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] [LocallyOfFiniteType (p ≫ sX)]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {n n' : ℕ} {K : Divisor X}
    (hK' : K.IsCanonicalDivisor sX n') {B : QDivisor X} {Δ : QDivisor U}
    (hcrep : IsCrepantBoundary sX n K B p hY hp Δ) {ω : RationalPluriForms sX n' 1}
    (hω0 : ω ≠ 0) (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    (hLB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉
      (Divisor.toQDivisor K + B).supp) :
    (Divisor.toQDivisor K + B).IsPullback p hLB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX p ω)) + Δ) := by
  intro m hm D hD hDc
  have hB' : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ D.supp :=
    fun Z hZ => hLB Z (by
      rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at hZ)
  refine ⟨D.pullback hDc hB', ?_, Divisor.isPullback_pullback hDc hB'⟩
  ext F
  have h := coeff_pullback_eq hX hY hp hK' hcrep hm hD hDc
    (Divisor.isPullback_pullback hDc hB') hω0 hωK F
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, Int.cast_natCast]
  exact h

end Crepancy

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Intersection numbers of `K + Δ` along a curve depend on `K` only up to linear equivalence. -/
private theorem intersectionNumber_add_eq_of_linearlyEquivalent [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
    {C : Scheme.{u}} (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {K₁ K₂ : Divisor X}
    (h : K₁.LinearlyEquivalent K₂) (Δ : QDivisor X) (h₁ : (Divisor.toQDivisor K₁ + Δ).IsQCartier)
    (h₂ : (Divisor.toQDivisor K₂ + Δ).IsQCartier) :
    (Divisor.toQDivisor K₁ + Δ).intersectionNumber k sX i hdim h₁ =
      (Divisor.toQDivisor K₂ + Δ).intersectionNumber k sX i hdim h₂ := by
  obtain ⟨D', hD', hD'c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul h₂
  set m := (Divisor.toQDivisor K₂ + Δ).cartierIndex h₂
  have hm := QDivisor.cartierIndex_pos h₂
  obtain ⟨φ, hφ⟩ := h
  set a : Additive (RationalFunctions X)ˣ := (m : ℤ) • Additive.ofMul φ with ha
  set G := D' + principalDivisorHom a with hG_def
  have hGc : G.IsCartier := hD'c.add (Divisor.isCartier_principalDivisor _)
  have hG : Divisor.toQDivisor G = (m : ℤ) • (Divisor.toQDivisor K₁ + Δ) := by
    have e : principalDivisorHom a = (m : ℤ) • (K₁ - K₂) := by
      rw [ha, map_zsmul, principalDivisorHom_apply, toMul_ofMul, hφ]
    rw [hG_def, e, map_add, hD', map_zsmul, map_sub, ← smul_add]
    congr 1
    abel
  have hGD : G.LinearlyEquivalent D' := ⟨a.toMul, by
    rw [hG_def, add_sub_cancel_left, principalDivisorHom_apply]⟩
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ h₁ hm G hGc hG,
    QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ h₂ hm D' hD'c hD']
  congr 2
  have := hGc.isInvertibleModule_divisorialSheaf
  have := hD'c.isInvertibleModule_divisorialSheaf
  exact degreeOn_eq_of_iso k sX i hdim hGD.divisorialSheafIso

/-- Intersection numbers are unchanged by an isomorphism of curves over `X`. -/
private theorem intersectionNumber_eq_of_iso_comp [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] {C C' : Scheme.{u}} (i : C ⟶ X) (i' : C' ⟶ X)
    [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C') (he : e.hom ≫ i' = i) (D : QDivisor X)
    (hD : D.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D.intersectionNumber k sX i' hdim' hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  unfold QDivisor.intersectionNumber Divisor.degreeOn
  have := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i i' hdim hdim' e he]

/-- Two closed subschemes cut out by equal ideal sheaves are isomorphic over `X`. -/
private theorem exists_iso_subscheme_of_eq {I J : X.IdealSheafData} (h : I = J) :
    ∃ e : I.subscheme ≅ J.subscheme, e.hom ≫ J.subschemeι = I.subschemeι := by
  subst h
  exact ⟨Iso.refl _, by simp⟩

/-- A proper curve over `k` is a curve over `k`. -/
private theorem isCurve_properCurve {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) :
    AlgebraicGeometry.IsCurve k (C.ι ≫ sX) where
  toIsIntegral := StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  toIsSeparated := inferInstance
  toLocallyOfFiniteType := inferInstance
  toQuasiCompact := inferInstance
  topologicalKrullDim_eq_one := C.dim_eq

/-- The underlying set of a proper curve is the closure of its generic point. -/
private theorem range_properCurve_ι {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) :
    Set.range C.ι = closure ({C.point} : Set X) := by
  unfold ProperCurve.ι curveSubschemeAtι
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

end Curves

/-- The divisors of two nonzero rational top forms on a normal variety are linearly
equivalent. -/
private theorem linearlyEquivalent_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ ω : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hω : ω ≠ 0) : Divisor.LinearlyEquivalent (divisorOfForm τ) (divisorOfForm ω) := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 ω hω
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul he (inv_ne_zero hc), ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm,
    coeff_divisorOfForm, e1, e2]
  ring

/-- The negative of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_neg {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, hC⟩ := hD
  exact ⟨-m, neg_ne_zero.mpr hm, by rwa [neg_smul, smul_neg, neg_neg]⟩

/-- `((-D) · C) = -(D · C)`. -/
private theorem intersectionNumber_neg (k : Type u) [Field k] {X C : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
    (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {D : QDivisor X}
    (hD : D.IsQCartier) (hD' : (-D).IsQCartier) :
    (-D).intersectionNumber k sX i hdim hD' = -(D.intersectionNumber k sX i hdim hD) := by
  have hadd := QDivisor.intersectionNumber_add' k sX i hdim D (-D) hD hD'
    (by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero)
  have h00 : (0 : QDivisor X).intersectionNumber k sX i hdim QDivisor.isQCartier_zero = 0 := by
    have := QDivisor.intersectionNumber_add' k sX i hdim (0 : QDivisor X) 0
      QDivisor.isQCartier_zero QDivisor.isQCartier_zero (by simpa using QDivisor.isQCartier_zero)
    simp only [add_zero] at this
    linarith
  rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ QDivisor.isQCartier_zero (add_neg_cancel D),
    h00] at hadd
  linarith

/-- **Projection of a contracted curve.** Let `L' = u^*L` be the pull-back of a `ℚ`-Cartier
`ℚ`-divisor along a proper morphism `u : V ⟶ W` of normal varieties and `C ⊆ V` a proper curve
contracted by `u ≫ f`. Either `(L' · C) = 0` (when `u(C)` is a point), or
`(L' · C) = d (L · u(C))` with `d ≥ 0`, where `u(C)` is a proper curve of `W` contracted by `f`. -/
private theorem intersectionNumber_pullback_eq_zero_or {k : Type u} [Field k]
    {V W Y : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) (f : W ⟶ Y) {L : QDivisor W}
    (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (hC : C.IsContractedBy (u ≫ f)) :
    L'.intersectionNumber k sV C.ι C.dim_le hL' = 0 ∨
      ∃ d : ℚ, 0 ≤ d ∧ ∃ C'' : ProperCurve sW, C''.IsContractedBy f ∧
        L'.intersectionNumber k sV C.ι C.dim_le hL' =
          d * L.intersectionNumber k sW C''.ι C''.dim_le hL := by
  have := isCurve_properCurve C
  set φ := C.ι ≫ u with hφ
  by_cases hpt : ∃ w : W, Set.range φ = {w}
  · left
    exact intersectionNumber_pullback_eq_zero k sV sW u hu C.ι hL h hpt
  · right
    have : AlgebraicGeometry.IsCurve k (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
    have : IsProper (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
    have hcurve := isCurve_imageι_comp sW φ hpt
    have key := intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu C.ι hL h hcurve
    have hrange : closure (Set.range φ) = closure ({u C.point} : Set W) := by
      rw [hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_properCurve_ι,
        closure_image_closure u.continuous, Set.image_singleton]
    have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({u C.point} : Set W)) := by
      rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
      congr 1
      ext1
      simp only [TopologicalSpace.Closeds.coe_closure]
      exact hrange
    obtain ⟨e, he⟩ := exists_iso_subscheme_of_eq hker
    have : IsProper φ := IsProper.of_comp φ sW
    have : IsProper (φ.imageι ≫ sW) := isProper_imageι_comp φ sW
    have hdim : topologicalKrullDim (curveSubschemeAt (u C.point)) = 1 :=
      (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).symm.trans
        hcurve.topologicalKrullDim_eq_one
    have hι : curveSubschemeAtι (u C.point) = e.inv ≫ φ.imageι := (Iso.eq_inv_comp e).mpr he
    have hprop : IsProper (curveSubschemeAtι (u C.point) ≫ sW) := by
      rw [hι, Category.assoc]; infer_instance
    let C'' : ProperCurve sW := ⟨u C.point, ⟨hdim, hprop⟩⟩
    have hC'' : C''.IsContractedBy f := by
      intro x hx
      have hsub : closure ({u C.point} : Set W) ⊆ u '' closure ({C.point} : Set V) :=
        (u.isClosedMap _ isClosed_closure).closure_subset_iff.mpr (by
          rintro _ rfl; exact ⟨C.point, subset_closure rfl, rfl⟩)
      obtain ⟨z, hz, rfl⟩ := hsub hx
      simpa only [Scheme.Hom.comp_apply] using hC z hz
    refine ⟨(degreeOver φ.toImage : ℚ), by positivity, C'', hC'', key.trans ?_⟩
    rw [intersectionNumber_eq_of_iso_comp sW φ.imageι C''.ι _ C''.dim_le e he _ hL]

/-- The degree of the pull-back of an `f`-nef `ℚ`-divisor on a curve contracted by `u ≫ f` is
non-negative. -/
private theorem intersectionNumber_pullback_nonneg {k : Type u} [Field k]
    {V W Y : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) (f : W ⟶ Y) {L : QDivisor W}
    (hN : QDivisor.IsRelativelyNef sW f L)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (hC : C.IsContractedBy (u ≫ f)) : 0 ≤ L'.intersectionNumber k sV C.ι C.dim_le hL' := by
  rcases intersectionNumber_pullback_eq_zero_or u hu f hN.1 h hL' C hC with
      h0 | ⟨d, hd, C'', hC'', heq⟩
  · rw [h0]
  · rw [heq]
    exact mul_nonneg hd
      (MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sW hN hN.1 C'' hC'')

/-- The degree of the pull-back of a `ℚ`-divisor `L` with `-L` `f`-nef on a curve contracted by
`u ≫ f` is non-positive. -/
private theorem intersectionNumber_pullback_nonpos {k : Type u} [Field k]
    {V W Y : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) (f : W ⟶ Y) {L : QDivisor W}
    (hL : L.IsQCartier) (hN : QDivisor.IsRelativelyNef sW f (-L))
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (hC : C.IsContractedBy (u ≫ f)) : L'.intersectionNumber k sV C.ι C.dim_le hL' ≤ 0 := by
  rcases intersectionNumber_pullback_eq_zero_or u hu f hL h hL' C hC with
      h0 | ⟨d, hd, C'', hC'', heq⟩
  · rw [h0]
  · rw [heq]
    have := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sW hN hN.1 C'' hC''
    rw [intersectionNumber_neg k sW C''.ι C''.dim_le hL hN.1] at this
    nlinarith

/-- **`Δ'_Z - Δ_Z` is `(g ≫ f)`-nef.** With `K_X = div(ω)`, `K_{X'} = div(ω')`, crepancy says
`K_Z + Δ_Z = g^*(K_X + Δ)` and `K'_Z + Δ'_Z = g'^*(K_{X'} + Δ')` for `K_Z = div(g^*ω)`,
`K'_Z = div(g'^*ω')`, and `K'_Z ∼ K_Z`. So `Δ'_Z - Δ_Z = (K_Z + Δ'_Z) - (K_Z + Δ_Z)` is
`ℚ`-Cartier, and on a curve `C` contracted by `g ≫ f` its degree is
`(g'^*(K_{X'} + Δ') · C) - (g^*(K_X + Δ) · C)`; by the projection formula each term is `0` or a
non-negative multiple of the degree on the image curve, which is contracted by `f'`, resp. `f`. -/
private theorem isRelativelyNef_sub_of_isCrepantBoundary {k : Type u} [Field k] [PerfectField k]
    {n : ℕ} {X X' Y Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {f' : X' ⟶ Y} [IsProper f] [IsProper f'] (hfs : f ≫ sY = sX)
    (hfs' : f' ≫ sY = sX') (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hN' : QDivisor.IsRelativelyNef sX' f' (Divisor.toQDivisor KX' + Δ'))
    {g : Z ⟶ X} {g' : Z ⟶ X'} [IsProper g] [IsProper g'] (hZ : IsNormalVariety k (g ≫ sX))
    (hZ' : IsNormalVariety k (g' ≫ sX'))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hcomm : g ≫ f = g' ≫ f')
    {ΔZ ΔZ' : QDivisor Z} (hΔZ : IsCrepantBoundary sX n KX Δ g hZ hg ΔZ)
    (hΔZ' : IsCrepantBoundary sX' n KX' Δ' g' hZ' hg' ΔZ') :
    QDivisor.IsRelativelyNef (g ≫ sX) (g ≫ f) (ΔZ' - ΔZ) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g ≫ sX) := hZ.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g' ≫ sX') := hZ'.1.toLocallyOfFiniteType
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
  have : QuasiCompact (g ≫ sX) := hZ.1.toQuasiCompact
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsDominant g := hg.isDominant
  have : IsDominant g' := hg'.isDominant
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k sX' := hX'.1
  have : AlgebraicGeometry.IsVariety k (g ≫ sX) := hZ.1
  have hsZ : g' ≫ sX' = g ≫ sX := by
    rw [← hfs', ← Category.assoc, ← hcomm, Category.assoc, hfs]
  have hnZ : topologicalKrullDim Z = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hg, hK.1]
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨ω', hω0', hωK'⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX' hK'
  have hLB := map_componentGenericPoint_notMem_supp g (Divisor.toQDivisor KX + Δ)
  have hLB' := map_componentGenericPoint_notMem_supp g' (Divisor.toQDivisor KX' + Δ')
  set KZ := divisorOfForm (pullbackRationalPluriForms sX g ω) with hKZ
  set KZ' := divisorOfForm (pullbackRationalPluriForms sX' g' ω') with hKZ'
  have hpb := isPullback_divisorOfForm_add hX hZ hg hK hΔZ hω0 hωK hLB
  have hpb' := isPullback_divisorOfForm_add hX' hZ' hg' hK' hΔZ' hω0' hωK' hLB'
  have hQ : (Divisor.toQDivisor KX + Δ).IsQCartier := by simpa using isQCartier_neg hN.1
  have hQ' : (Divisor.toQDivisor KX' + Δ').IsQCartier := hN'.1
  have hB := hpb.isQCartier hQ
  have hA := hpb'.isQCartier hQ'
  have hne : pullbackRationalPluriForms sX g ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hX hg hK.1 hω0
  have hne' : pullbackRationalPluriForms sX' g' ω' ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hX' hg' hK'.1 hω0'
  have hlin : KZ'.LinearlyEquivalent KZ := by
    have key : ∀ (s : Z ⟶ Spec (.of k)) (_ : s = g ≫ sX) [LocallyOfFiniteType s]
        (τ : RationalPluriForms s n 1), τ ≠ 0 → (divisorOfForm τ).LinearlyEquivalent KZ := by
      rintro s rfl _ τ hτ
      exact linearlyEquivalent_divisorOfForm hZ hnZ hτ hne
    exact key _ hsZ _ hne'
  have hA2 : (Divisor.toQDivisor KZ + ΔZ').IsQCartier := hA.add_of_linearlyEquivalent hlin
  have hBn : (-(Divisor.toQDivisor KZ + ΔZ)).IsQCartier := isQCartier_neg hB
  have hH : ΔZ' - ΔZ = (Divisor.toQDivisor KZ + ΔZ') + -(Divisor.toQDivisor KZ + ΔZ) := by abel
  have hHq : (ΔZ' - ΔZ).IsQCartier := hH ▸ hA2.add hBn
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (g ≫ sX) hHq
    fun C hC => ?_
  rw [MMP.Fourfold.intersectionNumber_congr _ C.ι C.dim_le hHq (hA2.add hBn) hH,
    QDivisor.intersectionNumber_add' k _ C.ι C.dim_le _ _ hA2 hBn,
    intersectionNumber_neg k _ C.ι C.dim_le hB hBn,
    ← intersectionNumber_add_eq_of_linearlyEquivalent (g ≫ sX) C.ι C.dim_le hlin ΔZ' hA hA2]
  linarith [intersectionNumber_pullback_nonneg g' hsZ f' hN' hpb' hA C
      (by rw [← hcomm]; exact hC),
    intersectionNumber_pullback_nonpos g rfl f hQ hN hpb hB C hC]

/-- An exceptional prime divisor of a morphism maps its generic point to a point of coheight at
least two. -/
private theorem two_le_coheight_of_isExceptional {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} (E : PrimeDivisor Y)
    (hE : RationalMap.IsExceptional (X := Y) f.toRationalMap E) :
    2 ≤ Order.coheight (f E.genericPoint) := by
  set η := E.genericPoint
  have hdef : RationalMap.DefinedAt (X := Y) f.toRationalMap η := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have h2 := (RationalMap.isExceptional_iff.mp hE) hdef
  have hsub : (TopologicalSpace.IrreducibleCloseds.closureSingleton (f η) : Set X) ⊆
      (RationalMap.transform (X := Y) f.toRationalMap E.idealSheaf.support : Set X) := by
    rw [TopologicalSpace.IrreducibleCloseds.coe_closureSingleton]
    refine (TopologicalSpace.Closeds.isClosed _).closure_subset_iff.mpr ?_
    rintro _ rfl
    refine RationalMap.image_subset_transform f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨η, ?_, rfl⟩
    change η ∈ E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hle := le_closedsCodimension_iff.mp h2 _ hsub
  have hcodim : codimension (TopologicalSpace.IrreducibleCloseds.closureSingleton (f η)) =
      Order.coheight (f η) := by
    have h : TopologicalSpace.IrreducibleCloseds.closureSingleton (f η) =
        irreducibleSetEquivPoints.symm (f η) :=
      TopologicalSpace.IrreducibleCloseds.ext (by
        rw [TopologicalSpace.IrreducibleCloseds.coe_closureSingleton,
          coe_irreducibleEquivPoints_symm_apply])
    rw [codimension_eq_coheight, h]
    exact Order.coheight_orderIso irreducibleSetEquivPoints.symm (f η)
  rwa [hcodim] at hle

/-- The discrepancy of a prime divisor `F` whose generic point maps to a point of coheight one is
minus the coefficient of the boundary at the prime divisor through that point. -/
private theorem exists_discrepancy_eq_neg_coeff {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {Y : Scheme.{u}}
    {f : Y ⟶ X} {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f}
    {F : PrimeDivisor Y} {a : ℚ} (ha : IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, F⟩ a)
    (h1 : Order.coheight (f F.genericPoint) = 1) :
    ∃ D : PrimeDivisor X, a = -Δ.coeff D ∧ D.genericPoint = f F.genericPoint := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have hE : ¬ (⟨Y, f, hY, hf, F⟩ : DivisorOver k sX).IsExceptional := fun hE => by
    have h2 := two_le_coheight_of_isExceptional (f := f) F hE
    rw [h1] at h2
    exact absurd h2 (by decide)
  obtain ⟨hX, hK, m, hm, hC, -⟩ := id ha
  obtain ⟨D, hc, hD⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
    ⟨hX, hK, m, by exact_mod_cast hm.ne', hC⟩ _ hE
  refine ⟨D, ha.eq hD, ?_⟩
  have h := (⟨Y, f, hY, hf, F⟩ : DivisorOver k sX).isGenericPoint_center
  rw [hc] at h
  exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure D ▸ isGenericPoint_closure).eq h

/-- One side of the coefficient comparison: if `f(g(η_F))` is the generic point of a prime
divisor `P` of `Y`, the coefficient of `F` in the crepant boundary of `(X, Δ)` on `Z` is the
coefficient of `P` in `f_*Δ`. -/
private theorem coeff_eq_transformDivisor_apply {k : Type u} [Field k] [PerfectField k]
    {n : ℕ} {X Y Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} [IsProper f] (hfs : f ≫ sY = sX) (hf : IsBirationalMorphism f)
    {K : Divisor X} {Δ : QDivisor X} {g : Z ⟶ X} {hZ : IsNormalVariety k (g ≫ sX)}
    {hg : IsBirationalMorphism g} {ΔZ : QDivisor Z}
    (hΔZ : IsCrepantBoundary sX n K Δ g hZ hg ΔZ) (F : PrimeDivisor Z) (P : PrimeDivisor Y)
    (hFP : f (g F.genericPoint) = P.genericPoint) :
    ΔZ.coeff F = RationalMap.transformDivisor (X := X) f.toRationalMap Δ P := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsNormal Y := hY.2
  have : IsSeparated sY := hY.1.toIsSeparated
  have : IsSeparated f := IsSeparated.of_comp f sY
  have : IsDominant f := hf.isDominant
  have hXY : IsNormalVariety k (f ≫ sY) := hfs ▸ hX
  obtain ⟨E, hEP, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hXY hf P
  have hbij := hf.functionFieldMap_bijective
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (f E.genericPoint)) := by rw [hEP]; infer_instance
  have : ValuationRing (Y.presheaf.stalk (f (g F.genericPoint))) := by
    rw [hFP]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g F.genericPoint)
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have hgE : E.genericPoint = g F.genericPoint :=
    MMP.Positivity.eq_of_isIso_stalkMap f hbij (hFP.trans hEP.symm)
  have h1 : Order.coheight (g F.genericPoint) = 1 := by
    rw [← hgE]; exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  obtain ⟨D, hD, hDg⟩ := exists_discrepancy_eq_neg_coeff (hΔZ F) h1
  obtain rfl : D = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hDg.trans hgE.symm)
  rw [htr]
  exact neg_injective hD

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : MMP.Mori.IsBirationalMorphism g) (hμ : MMP.Mori.IsBirationalMorphism μ) :
    MMP.Mori.IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rw [hfac]; exact h1
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- **The two crepant boundaries agree off the `(g ≫ f)`-exceptional divisors.** If `F` is not
`(g ≫ f)`-exceptional, `(g ≫ f)(η_F)` is the generic point of a prime divisor `P` of `Y`, and
both crepant boundaries have coefficient `coeff_P(f_*Δ) = coeff_P(f'_*Δ')` at `F`. -/
private theorem coeff_eq_of_not_isExceptional {k : Type u} [Field k] [PerfectField k]
    {n : ℕ} {X X' Y Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {f' : X' ⟶ Y} [IsProper f] [IsProper f'] (hfs : f ≫ sY = sX)
    (hfs' : f' ≫ sY = sX') (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hP : IsPair sX Δ) (hP' : IsPair sX' Δ')
    (hΔ : RationalMap.transformDivisor (X := X) f.toRationalMap Δ =
      RationalMap.transformDivisor (X := X') f'.toRationalMap Δ')
    {g : Z ⟶ X} {g' : Z ⟶ X'} [IsProper g] [IsProper g'] (hZ : IsNormalVariety k (g ≫ sX))
    (hZ' : IsNormalVariety k (g' ≫ sX'))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hcomm : g ≫ f = g' ≫ f')
    {ΔZ ΔZ' : QDivisor Z} (hΔZ : IsCrepantBoundary sX n KX Δ g hZ hg ΔZ)
    (hΔZ' : IsCrepantBoundary sX' n KX' Δ' g' hZ' hg' ΔZ') (F : PrimeDivisor Z)
    (hF : ¬ RationalMap.IsExceptional (X := Z) (g ≫ f).toRationalMap F) :
    ΔZ.coeff F = ΔZ'.coeff F := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsNormal Y := hY.2
  have hZY : IsNormalVariety k ((g ≫ f) ≫ sY) := by rwa [Category.assoc, hfs]
  have hh : IsBirationalMorphism (g ≫ f) := isBirationalMorphism_comp hg hf
  obtain ⟨P, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hY
    (⟨Z, g ≫ f, hZY, hh, F⟩ : DivisorOver k sY) hF
  have hFP : (g ≫ f) F.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hv
  have hFP' : f' (g' F.genericPoint) = P.genericPoint := by
    rwa [← Scheme.Hom.comp_apply, ← hcomm]
  rw [coeff_eq_transformDivisor_apply hX hY hfs hf hΔZ F P hFP,
    coeff_eq_transformDivisor_apply hX' hY hfs' hf' hΔZ' F P hFP', hΔ]

end CommonModel

open AlgebraicGeometry hiding PrimeDivisor

/-- **Comparison of discrepancies on a common model** (Kollár–Mori, proof of 3.38). Let
`f : X ⟶ Y`, `f' : X' ⟶ Y` be proper birational morphisms of normal varieties over a perfect
field, `Δ`, `Δ'` `ℚ`-divisors with `f_*Δ = f'_*Δ'`, `-(K_X + Δ)` `f`-nef and `K_{X'} + Δ'`
`f'`-nef (both `ℚ`-Cartier), and `g : Z ⟶ X`, `g' : Z ⟶ X'` proper birational morphisms from a
normal variety with `g ≫ f = g' ≫ f'`. If `H` is the `ℚ`-divisor on `Z` with
`coeff_F H = a(F, X, Δ) - a(F, X', Δ')` for every prime divisor `F`, then `H` is `ℚ`-Cartier
and `(g ≫ f)`-nef, and `coeff_F H = 0` for every prime divisor `F` of `Z` that is not
`(g ≫ f)`-exceptional. -/
@[mmp "lem_km3c_discrepancy_comparison_divisor"]
public theorem isRelativelyNef_of_isDiscrepancy_sub {k : Type u} [Field k] [PerfectField k]
    {n : ℕ} {X X' Y Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {f' : X' ⟶ Y} [IsProper f] [IsProper f'] (hfs : f ≫ sY = sX)
    (hfs' : f' ≫ sY = sX') (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hΔ : RationalMap.transformDivisor (X := X) f.toRationalMap Δ =
      RationalMap.transformDivisor (X := X') f'.toRationalMap Δ')
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hN' : QDivisor.IsRelativelyNef sX' f' (Divisor.toQDivisor KX' + Δ'))
    {g : Z ⟶ X} {g' : Z ⟶ X'} [IsProper g] [IsProper g'] (hZ : IsNormalVariety k (g ≫ sX))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hcomm : g ≫ f = g' ≫ f')
    (H : QDivisor Z)
    (hH : ∀ (F : PrimeDivisor Z) (a a' : ℚ), IsDiscrepancy sX n KX Δ ⟨Z, g, hZ, hg, F⟩ a →
      IsDiscrepancy sX' n KX' Δ' ⟨Z, g', by
        rwa [← hfs', ← Category.assoc, ← hcomm, Category.assoc, hfs], hg', F⟩ a' →
      H.coeff F = a - a') :
    QDivisor.IsRelativelyNef (g ≫ sX) (g ≫ f) H ∧
      ∀ F : PrimeDivisor Z, ¬ RationalMap.IsExceptional (X := Z) (g ≫ f).toRationalMap F →
        H.coeff F = 0 := by
  have hZ' : IsNormalVariety k (g' ≫ sX') := by
    rwa [← hfs', ← Category.assoc, ← hcomm, Category.assoc, hfs]
  have hP : IsPair sX Δ := isPair_of_isQCartier_neg hX hK hN.1
  have hP' : IsPair sX' Δ' := ⟨hX', n, KX', hK', hN'.1⟩
  obtain ⟨⟨ΔZ, hΔZ, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hP hK g hZ hg
  obtain ⟨⟨ΔZ', hΔZ', -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hP' hK' g' hZ' hg'
  have hHeq : H = ΔZ' - ΔZ := by
    ext F
    have := hH F _ _ (hΔZ F) (hΔZ' F)
    change H.coeff F = ΔZ'.coeff F - ΔZ.coeff F
    rw [this]; ring
  subst hHeq
  refine ⟨isRelativelyNef_sub_of_isCrepantBoundary hX hX' hY hfs hfs' hf hf' hK hK' hN hN' hZ hZ'
    hg hg' hcomm hΔZ hΔZ', fun F hF => ?_⟩
  change ΔZ'.coeff F - ΔZ.coeff F = 0
  rw [coeff_eq_of_not_isExceptional hX hX' hY hfs hfs' hf hf' hK hK' hP hP' hΔ hZ hZ' hg hg'
    hcomm hΔZ hΔZ' F hF, sub_self]

end MMP.Mori
