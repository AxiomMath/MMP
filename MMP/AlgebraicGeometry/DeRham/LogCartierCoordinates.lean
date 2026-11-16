module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Etale.Kaehler
public import StacksFrontier.RingTheory.DeRham.Cartier.Polynomial

/-!
# The logarithmic inverse Cartier isomorphism in coordinates

Let `p` be a prime, `A → B` a map of rings of characteristic `p`, and `x₁, …, xₙ ∈ B` Frobenius
coordinates of `B` over `A` (`KaehlerDifferential.Cartier.IsFrobeniusCoordinates`, with the
`dxⱼ` a basis of `Ω[B⁄A]`), for instance the variables of a polynomial algebra over a perfect
ring. Let `P` be a set of indices and `L = B[1/∏_{j ∈ P} xⱼ]`. Inside the exterior algebra of
`Ω[L⁄A]` the **logarithmic forms** of degree `i` are the `B`-combinations of wedges of `i`
generators `db` (`b ∈ B`) and `dlog xⱼ = xⱼ⁻¹ dxⱼ` (`j ∈ P`); they form a complex under the de
Rham differential, the affine logarithmic de Rham complex `Ω^•_{B/A}(log D)` of the divisor
`D = ∑_{j ∈ P} V(xⱼ)`. This file proves that **the inverse Cartier map
`C⁻¹ : Ω^i_{B/A}(log D) ⟶ H^i(F_*Ω^•_{B/A}(log D))`,
`b db₁ ∧ ⋯ ∧ dlog xⱼ ∧ ⋯ ↦ [b^p b₁^{p-1} db₁ ∧ ⋯ ∧ dlog xⱼ ∧ ⋯]`, is well defined and
bijective.**

The proof is the weight argument of the non-logarithmic case, run inside the logarithmic forms.
The forms `εⱼ = dlog xⱼ` (`j ∈ P`) and `εⱼ = dxⱼ` (`j ∉ P`) are a basis of `Ω[L⁄A]`, and the
logarithmic forms are exactly the `B`-combinations of their wedges `ε_s`. The Euler vector
fields `θⱼ = xⱼ ∂/∂xⱼ` take values in `B` on the generators, so contraction against them and the
Lie derivatives `L_{θⱼ}` preserve logarithmic forms. Since `dlog xⱼ` has weight `0`, the form
`c^p x^α ε_s` has `j`-th weight `αⱼ + [j ∈ s ∖ P]`, and the projector
`π = ∏ⱼ (1 - L_{θⱼ}^{p-1})` keeps exactly the forms `c^p x_{s ∖ P}^{p-1} ε_s`, which are the
values of `C⁻¹` on `c ε_s`. A closed logarithmic form `z` differs from `π z` by `L_θ^{p-1}`
of closed logarithmic forms, which are differentials of logarithmic forms by Cartan's formula;
so `C⁻¹` is onto. Injectivity, and the fact that the semilinearity, multiplicativity and the
values on generators hold up to differentials of logarithmic forms, reduce to the
non-logarithmic Cartier isomorphism of `L`
(`KaehlerDifferential.Cartier.inverseCartier_bijective_of_isFrobeniusCoordinates`): a closed
logarithmic form exact in `Ω^•_{L/A}` is the differential of a logarithmic form.

## Main definitions

* `MMP.DeRham.logForms`: the logarithmic forms of degree `i`, a `B`-submodule of the exterior
  algebra of `Ω[L⁄A]`; `MMP.DeRham.closedLogForms` and `MMP.DeRham.exactLogForms` the closed
  ones and the differentials of logarithmic forms.
* `MMP.DeRham.logBasis`: the basis `dlog xⱼ` (`j ∈ P`), `dxⱼ` (`j ∉ P`) of `Ω[L⁄A]`.
* `MMP.DeRham.cartierRepExt`: the Cartier representative `∑ c_s dx_s ↦ ∑ c_s^p x_s^{p-1} dx_s`,
  extended by zero to the exterior algebra.

## Main results

* `MMP.DeRham.coe_deRhamDifferential_mem_logForms`: the logarithmic forms are stable under `d`.
* `MMP.DeRham.exists_logInverseCartier_of_isFrobeniusCoordinates`: **the logarithmic inverse
  Cartier isomorphism** for `B → L` with a coordinate basis and Frobenius coordinates on both
  sides.
* `MMP.DeRham.isFrobeniusCoordinates_of_isLocalization_away`: Frobenius coordinates survive
  inverting an element.
* `MMP.DeRham.exists_logInverseCartier_of_isLocalization_away` and
  `MMP.DeRham.exists_logInverseCartier_of_isLocalization_away_castLE`: the isomorphism for
  `L = B[1/∏_{j ∈ P} xⱼ]`, and for `L = B[1/(x₁ ⋯ x_r)]`;
  `MMP.DeRham.exists_logInverseCartier_mvPolynomial` for `B = A[x₁, …, xₙ]`, `A` perfect.

## Implementation notes

The isomorphism is stated in elementary form, for subsets of the exterior algebra of `Ω[L⁄A]`:
a map `C` on the logarithmic forms with values in the closed logarithmic forms, additive,
Frobenius-semilinear and multiplicative modulo the exact logarithmic forms, with the stated
values on `db` and `dlog uₖ`, injective modulo exact logarithmic forms and onto the closed
logarithmic forms modulo exact ones. The map `C` is the Cartier representative attached to the
basis `dxⱼ` of `Ω[L⁄A]`. The poles are given as a family `u : ι → B` whose values are the
`xⱼ`, `j ∈ P`. As in the non-logarithmic theory all rings live in one universe.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §4.
* N. Katz, *Nilpotent connections and the monodromy theorem*, Publ. Math. IHÉS 39 (1970), §7.
-/

@[expose] public noncomputable section

open KaehlerDifferential KaehlerDifferential.Cartier exteriorPower

universe u

namespace MMP.DeRham

/-! ### Logarithmic forms -/

section LogForms

variable (A : Type u) {B : Type u} (L : Type u) [CommRing A] [CommRing B] [CommRing L]
  [Algebra A L] [Algebra B L] {ι : Type*}

/-- The generators `db` (`b ∈ B`) and `dlog uⱼ = uⱼ⁻¹ duⱼ` of the logarithmic one-forms. -/
def logGenerators (u : ι → B) : Set (Ω[L⁄A]) :=
  Set.range (fun b : B ↦ D A L (algebraMap B L b)) ∪
    Set.range (fun j ↦ Ring.inverse (algebraMap B L (u j)) • D A L (algebraMap B L (u j)))

/-- The logarithmic `i`-forms: the `B`-submodule of the exterior algebra of `Ω[L⁄A]` spanned by
the wedges of `i` generators `db` and `dlog uⱼ`. -/
def logForms (u : ι → B) (i : ℕ) : Submodule B (ExteriorAlgebra L (Ω[L⁄A])) :=
  Submodule.span B {ω | ∃ v : Fin i → Ω[L⁄A], (∀ m, v m ∈ logGenerators A L u) ∧
    ExteriorAlgebra.ιMulti L i v = ω}

/-- The closed logarithmic `i`-forms. -/
def closedLogForms (u : ι → B) (i : ℕ) : Set (ExteriorAlgebra L (Ω[L⁄A])) :=
  {ω | ω ∈ logForms A L u i ∧ ∃ x : ⋀[L]^i (Ω[L⁄A]),
    (x : ExteriorAlgebra L (Ω[L⁄A])) = ω ∧ deRhamDifferential (A := A) i x = 0}

/-- The exact logarithmic `i`-forms: `0`, and the differentials of logarithmic `(i - 1)`-forms. -/
def exactLogForms (u : ι → B) (i : ℕ) : Set (ExteriorAlgebra L (Ω[L⁄A])) :=
  {ω | ω = 0 ∨ ∃ (j : ℕ) (x : ⋀[L]^j (Ω[L⁄A])), j + 1 = i ∧
    (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u j ∧
    ((deRhamDifferential (A := A) j x : ⋀[L]^(j + 1) (Ω[L⁄A])) :
      ExteriorAlgebra L (Ω[L⁄A])) = ω}

variable {A L}

/-- `0` is an exact logarithmic form. -/
theorem zero_mem_exactLogForms (u : ι → B) (i : ℕ) : 0 ∈ exactLogForms A L u i :=
  Or.inl rfl

/-- The sum of two exact logarithmic forms of the same degree is exact logarithmic. -/
theorem add_mem_exactLogForms {u : ι → B} {i : ℕ} {ω η : ExteriorAlgebra L (Ω[L⁄A])}
    (hω : ω ∈ exactLogForms A L u i) (hη : η ∈ exactLogForms A L u i) :
    ω + η ∈ exactLogForms A L u i := by
  rcases hω with rfl | ⟨j, x, rfl, hx, rfl⟩
  · rwa [zero_add]
  rcases hη with rfl | ⟨j', x', hj, hx', rfl⟩
  · rw [add_zero]
    exact Or.inr ⟨j, x, rfl, hx, rfl⟩
  obtain rfl : j' = j := by omega
  exact Or.inr ⟨j', x + x', rfl, by rw [Submodule.coe_add]; exact add_mem hx hx',
    by rw [map_add, Submodule.coe_add]⟩

/-- The differential of a logarithmic form is an exact logarithmic form. -/
theorem coe_deRhamDifferential_mem_exactLogForms {u : ι → B} {j : ℕ} (x : ⋀[L]^j (Ω[L⁄A]))
    (hx : (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u j) :
    ((deRhamDifferential (A := A) j x : ⋀[L]^(j + 1) (Ω[L⁄A])) :
      ExteriorAlgebra L (Ω[L⁄A])) ∈ exactLogForms A L u (j + 1) :=
  Or.inr ⟨j, x, rfl, hx, rfl⟩

/-- A wedge of `i` logarithmic generators is a logarithmic `i`-form. -/
theorem ιMulti_mem_logForms {u : ι → B} {i : ℕ} (v : Fin i → Ω[L⁄A])
    (hv : ∀ m, v m ∈ logGenerators A L u) :
    ExteriorAlgebra.ιMulti L i v ∈ logForms A L u i :=
  Submodule.subset_span ⟨v, hv, rfl⟩

/-- `db` is a logarithmic generator for every `b ∈ B`. -/
theorem D_mem_logGenerators (u : ι → B) (b : B) :
    D A L (algebraMap B L b) ∈ logGenerators A L u :=
  Or.inl ⟨b, rfl⟩

/-- `dlog uⱼ = uⱼ⁻¹ duⱼ` is a logarithmic generator. -/
theorem dlog_mem_logGenerators (u : ι → B) (j : ι) :
    Ring.inverse (algebraMap B L (u j)) • D A L (algebraMap B L (u j)) ∈
      logGenerators A L u :=
  Or.inr ⟨j, rfl⟩

/-- The logarithmic `i`-forms lie in `⋀^i Ω[L⁄A]`. -/
theorem logForms_le (u : ι → B) (i : ℕ) :
    logForms A L u i ≤ (⋀[L]^i (Ω[L⁄A])).restrictScalars B := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, -, rfl⟩
  exact ExteriorAlgebra.ιMulti_range L i ⟨v, rfl⟩

/-- **Induction on logarithmic forms**: a `B`-submodule of `⋀^i Ω[L⁄A]` containing the wedges
of generators contains every logarithmic form. -/
theorem mem_of_mem_logForms {u : ι → B} {i : ℕ} (S : Submodule B (⋀[L]^i (Ω[L⁄A])))
    (hS : ∀ v : Fin i → Ω[L⁄A], (∀ m, v m ∈ logGenerators A L u) →
      exteriorPower.ιMulti L i v ∈ S)
    (y : ⋀[L]^i (Ω[L⁄A])) (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    y ∈ S := by
  have hle : logForms A L u i ≤ S.map ((⋀[L]^i (Ω[L⁄A])).subtype.restrictScalars B) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨exteriorPower.ιMulti L i v, hS v hv, by simp [exteriorPower.ιMulti_apply_coe]⟩
  obtain ⟨z, hz, hzy⟩ := hle hy
  rwa [← Subtype.coe_injective hzy]

/-- **Induction on logarithmic forms** for an `L`-linear map: if it sends the wedges of
generators to logarithmic forms, it sends all logarithmic forms to logarithmic forms. -/
theorem logForms_induction {u : ι → B} {i k : ℕ}
    (f : ⋀[L]^i (Ω[L⁄A]) →ₗ[L] ⋀[L]^k (Ω[L⁄A]))
    (hf : ∀ v : Fin i → Ω[L⁄A], (∀ m, v m ∈ logGenerators A L u) →
      ((f (exteriorPower.ιMulti L i v) : ⋀[L]^k (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈
        logForms A L u k)
    (y : ⋀[L]^i (Ω[L⁄A])) (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    ((f y : ⋀[L]^k (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u k := by
  let N : Submodule B (ExteriorAlgebra L (Ω[L⁄A])) :=
    { carrier := {ω | ∃ z : ⋀[L]^i (Ω[L⁄A]), (z : ExteriorAlgebra L (Ω[L⁄A])) = ω ∧
        ((f z : ⋀[L]^k (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u k}
      zero_mem' := ⟨0, rfl, by simp⟩
      add_mem' := by
        rintro _ _ ⟨z, rfl, hz⟩ ⟨z', rfl, hz'⟩
        exact ⟨z + z', rfl, by simpa using add_mem hz hz'⟩
      smul_mem' := by
        rintro b _ ⟨z, rfl, hz⟩
        refine ⟨b • z, rfl, ?_⟩
        rw [LinearMap.map_smul_of_tower, Submodule.coe_smul_of_tower]
        exact Submodule.smul_mem _ b hz }
  have hle : logForms A L u i ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨exteriorPower.ιMulti L i v, by rw [exteriorPower.ιMulti_apply_coe], hf v hv⟩
  obtain ⟨z, hz, hfz⟩ := hle hy
  rwa [Subtype.coe_injective hz] at hfz

end LogForms

/-! ### The de Rham differential, contractions and Lie derivatives on logarithmic forms

On a spanning form `b · v₁ ∧ ⋯ ∧ vᵢ` with every `vₘ` either `dc` or `dlog t`, the differential is
`db ∧ v₁ ∧ ⋯ ∧ vᵢ`: writing `vₘ = aₘ dgₘ` with `daₘ` a multiple of `dgₘ`, the part `b · d(∏ aₘ)`
of the differential lies in the span of the `dgₘ` and dies in the wedge. -/

section Differential

section Wedge

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `w` lies in the span of `g₁, …, gᵢ`, then `w ∧ g₁ ∧ ⋯ ∧ gᵢ = 0`. -/
theorem ι_mul_ιMulti_eq_zero_of_mem_span {i : ℕ} (g : Fin i → M) {w : M}
    (hw : w ∈ Submodule.span R (Set.range g)) :
    ExteriorAlgebra.ι R w * ExteriorAlgebra.ιMulti R i g = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    have h := ExteriorAlgebra.ιMulti_succ_apply (R := R) (Fin.cons (g m) g : Fin (i + 1) → M)
    simp only [Fin.cons_zero, Matrix.vecTail, Function.comp_def, Fin.cons_succ] at h
    rw [← h]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := m.succ) (by simp)
      (Fin.succ_ne_zero m).symm
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, add_mul, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, hx, smul_zero]

end Wedge

variable {A B L : Type u} [CommRing A] [CommRing B] [CommRing L] [Algebra A L] [Algebra B L]
  {ι : Type*}

/-- In the exterior algebra, `d(c dg₁ ∧ ⋯ ∧ dgᵢ) = dc ∧ dg₁ ∧ ⋯ ∧ dgᵢ`. -/
theorem coe_deRhamDifferential_smul_ιMulti_D (i : ℕ) (c : L) (g : Fin i → L) :
    ((deRhamDifferential (A := A) i (c • exteriorPower.ιMulti L i fun m ↦ D A L (g m)) :
      ⋀[L]^(i+1) (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) =
      ExteriorAlgebra.ι L (D A L c) * ExteriorAlgebra.ιMulti L i (fun m ↦ D A L (g m)) := by
  have h := deRhamDifferential_smul_ιMulti_D (A := A) (B := L) i (Fin.cons c g)
  simp only [Fin.cons_zero, Fin.cons_succ] at h
  rw [h, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
  simp [Matrix.vecTail, Function.comp_def]

/-- If every `daₘ` lies in the span of the `dgₗ`, then
`d(c · a₁ dg₁ ∧ ⋯ ∧ aᵢ dgᵢ) = dc ∧ a₁ dg₁ ∧ ⋯ ∧ aᵢ dgᵢ`. -/
theorem coe_deRhamDifferential_smul_ιMulti_of_D_mem (i : ℕ) (c : L) (a g : Fin i → L)
    (ha : ∀ m, D A L (a m) ∈ Submodule.span L (Set.range fun l ↦ D A L (g l))) :
    ((deRhamDifferential (A := A) i
        (c • exteriorPower.ιMulti L i fun m ↦ a m • D A L (g m)) :
      ⋀[L]^(i+1) (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) =
      ExteriorAlgebra.ι L (D A L c) *
        ExteriorAlgebra.ιMulti L i (fun m ↦ a m • D A L (g m)) := by
  set S := Submodule.span L (Set.range fun l ↦ D A L (g l))
  have hprod : ∀ s : Finset (Fin i), D A L (∏ m ∈ s, a m) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert m s hm ih =>
      rw [Finset.prod_insert hm, Derivation.leibniz]
      exact S.add_mem (S.smul_mem _ ih) (S.smul_mem _ (ha m))
  rw [AlternatingMap.map_smul_univ, smul_smul, coe_deRhamDifferential_smul_ιMulti_D,
    Derivation.leibniz, map_add, add_mul, map_smul, smul_mul_assoc,
    ι_mul_ιMulti_eq_zero_of_mem_span _ (hprod Finset.univ), smul_zero, zero_add, map_smul,
    smul_mul_assoc, AlternatingMap.map_smul_univ, mul_smul_comm]

/-- `d(x⁻¹)` is a multiple of `dx` (and `0` when `x` is not a unit). -/
theorem D_inverse_mem_span (x : L) :
    D A L (Ring.inverse x) ∈ Submodule.span L (Set.range fun _ : Unit ↦ D A L x) := by
  have hx : D A L x ∈ Submodule.span L (Set.range fun _ : Unit ↦ D A L x) :=
    Submodule.subset_span ⟨(), rfl⟩
  by_cases h : IsUnit x
  · have hl := (D A L).leibniz (Ring.inverse x) x
    rw [Ring.inverse_mul_cancel x h, Derivation.map_one_eq_zero] at hl
    have he : D A L (Ring.inverse x) =
        Ring.inverse x • (-(Ring.inverse x • D A L x)) := by
      rw [eq_neg_of_add_eq_zero_left hl.symm, neg_neg, smul_smul, Ring.inverse_mul_cancel x h,
        one_smul]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hx))
  · rw [Ring.inverse_non_unit x h, Derivation.map_zero]
    exact Submodule.zero_mem _

/-- Each logarithmic generator `db` or `dlog u` is `a dg` with `da` a multiple of `dg`. -/
theorem exists_eq_smul_D_of_mem_logGenerators (u : ι → B) {w : Ω[L⁄A]}
    (hw : w ∈ logGenerators A L u) :
    ∃ a g : L, w = a • D A L g ∧
      D A L a ∈ Submodule.span L (Set.range fun _ : Unit ↦ D A L g) := by
  rcases hw with ⟨b, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨1, algebraMap B L b, by rw [one_smul], by simp⟩
  · exact ⟨_, _, rfl, D_inverse_mem_span _⟩

/-- **The logarithmic forms are stable under the de Rham differential.** -/
theorem coe_deRhamDifferential_mem_logForms (u : ι → B) (j : ℕ) (x : ⋀[L]^j (Ω[L⁄A]))
    (hx : (x : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u j) :
    ((deRhamDifferential (A := A) j x : ⋀[L]^(j + 1) (Ω[L⁄A])) :
      ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u (j + 1) := by
  obtain ⟨n, f, gen, hsum⟩ := Submodule.mem_span_set'.1 hx
  choose v hv hvω using fun i ↦ (gen i).2
  choose a g hag hD using fun i m ↦ exists_eq_smul_D_of_mem_logGenerators (A := A) u (hv i m)
  have hxe : x = ∑ i, algebraMap B L (f i) •
      exteriorPower.ιMulti L j (fun m ↦ a i m • D A L (g i m)) := by
    refine Subtype.coe_injective ?_
    dsimp only
    rw [← hsum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Submodule.coe_smul, exteriorPower.ιMulti_apply_coe, ← hvω i, algebraMap_smul]
    congr 2
    funext m
    exact hag i m
  rw [hxe, map_sum, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have hspan : ∀ m, D A L (a i m) ∈ Submodule.span L (Set.range fun l ↦ D A L (g i l)) := by
    intro m
    refine Submodule.span_le.2 ?_ (hD i m)
    rintro _ ⟨-, rfl⟩
    exact Submodule.subset_span ⟨m, rfl⟩
  rw [coe_deRhamDifferential_smul_ιMulti_of_D_mem j _ (a i) (g i) hspan]
  refine Submodule.subset_span ⟨Fin.cons (D A L (algebraMap B L (f i)))
    (fun m ↦ a i m • D A L (g i m)), ?_, ?_⟩
  · refine Fin.cases ?_ (fun m ↦ ?_)
    · exact Or.inl ⟨f i, rfl⟩
    · rw [Fin.cons_succ, ← hag i m]
      exact hv i m
  · rw [ExteriorAlgebra.ιMulti_succ_apply]
    simp [Matrix.vecTail, Function.comp_def]

/-- **Contraction against a vector field taking values in `B` on the generators preserves
logarithmic forms.** -/
theorem coe_contraction_mem_logForms {u : ι → B} (θ : Ω[L⁄A] →ₗ[L] L)
    (hθ : ∀ w ∈ logGenerators A L u, θ w ∈ Set.range (algebraMap B L)) (k : ℕ)
    (y : ⋀[L]^(k + 1) (Ω[L⁄A])) (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u (k + 1)) :
    ((contraction θ k y : ⋀[L]^k (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u k := by
  refine logForms_induction (contraction θ k) (fun v hv ↦ ?_) y hy
  rw [contraction_ιMulti, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun m _ ↦ ?_
  obtain ⟨c, hc⟩ := hθ _ (hv m)
  rw [Submodule.coe_smul_of_tower, Submodule.coe_smul, ← hc, algebraMap_smul,
    exteriorPower.ιMulti_apply_coe]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.smul_mem _ c
    (ιMulti_mem_logForms (m.removeNth v) fun l ↦ hv _))

/-- **The Lie derivative along such a vector field preserves logarithmic forms.** -/
theorem coe_lie_mem_logForms {u : ι → B} (θ : Ω[L⁄A] →ₗ[L] L)
    (hθ : ∀ w ∈ logGenerators A L u, θ w ∈ Set.range (algebraMap B L)) (i : ℕ)
    (y : ⋀[L]^i (Ω[L⁄A])) (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    ((lie A θ i y : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i := by
  cases i with
  | zero =>
    rw [lie_zero_apply]
    exact coe_contraction_mem_logForms θ hθ 0 _ (coe_deRhamDifferential_mem_logForms u 0 y hy)
  | succ k =>
    rw [lie_succ_apply, Submodule.coe_add]
    exact add_mem
      (coe_deRhamDifferential_mem_logForms u k _ (coe_contraction_mem_logForms θ hθ k y hy))
      (coe_contraction_mem_logForms θ hθ (k + 1) _
        (coe_deRhamDifferential_mem_logForms u (k + 1) y hy))

/-- Every power of the Lie derivative along a vector field taking values in `B` on the
generators preserves logarithmic forms. -/
theorem coe_lie_pow_mem_logForms {u : ι → B} (θ : Ω[L⁄A] →ₗ[L] L)
    (hθ : ∀ w ∈ logGenerators A L u, θ w ∈ Set.range (algebraMap B L)) (i m : ℕ)
    (y : ⋀[L]^i (Ω[L⁄A])) (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    (((lie A θ i ^ m) y : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈
      logForms A L u i := by
  induction m with
  | zero => exact hy
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact coe_lie_mem_logForms θ hθ i _ ih

end Differential

/-! ### The logarithmic basis

Let `x₁, …, xₙ ∈ B` be such that the `dxⱼ` form a basis of `Ω[L⁄A]`, and let `P` be a set of
indices with `xⱼ` invertible in `L` for `j ∈ P`. The forms `εⱼ = dlog xⱼ` (`j ∈ P`) and
`εⱼ = dxⱼ` (`j ∉ P`) are again a basis of `Ω[L⁄A]`, and when `B → L` reads the coordinates of
every `db` in `B` and the poles `uₖ` are the `xⱼ`, `j ∈ P`, the logarithmic forms of degree `i`
are exactly the `B`-combinations of the wedges `ε_s`. -/

section LogBasis

variable {A B L : Type u} [CommRing A] [CommRing B] [CommRing L] [Algebra A L] [Algebra B L]
  {n : ℕ} (P : Finset (Fin n)) (x : Fin n → B)

/-- `xⱼ⁻¹` at a pole `j ∈ P`, and `1` elsewhere. -/
def logScale (j : Fin n) : L :=
  if j ∈ P then Ring.inverse (algebraMap B L (x j)) else 1

/-- `xⱼ` at a pole `j ∈ P`, and `1` elsewhere. -/
def poleFactor (j : Fin n) : B :=
  if j ∈ P then x j else 1

variable {P x}

/-- `logScale P x j * poleFactor P x j = 1` when the poles `xⱼ`, `j ∈ P`, are units of `L`. -/
theorem logScale_mul_poleFactor (hP : ∀ j ∈ P, IsUnit (algebraMap B L (x j))) (j : Fin n) :
    logScale (L := L) P x j * algebraMap B L (poleFactor P x j) = 1 := by
  unfold logScale poleFactor
  split_ifs with h
  · exact Ring.inverse_mul_cancel _ (hP j h)
  · simp

/-- `logScale P x j` is a unit when the poles `xⱼ`, `j ∈ P`, are units of `L`. -/
theorem isUnit_logScale (hP : ∀ j ∈ P, IsUnit (algebraMap B L (x j))) (j : Fin n) :
    IsUnit (logScale (L := L) P x j) :=
  isUnit_iff_exists_inv.2 ⟨_, logScale_mul_poleFactor hP j⟩

variable (bL : Module.Basis (Fin n) L (Ω[L⁄A]))

/-- **The logarithmic basis** `εⱼ = xⱼ⁻¹ dxⱼ` (`j ∈ P`), `εⱼ = dxⱼ` (`j ∉ P`) of `Ω[L⁄A]`. -/
def logBasis (hP : ∀ j ∈ P, IsUnit (algebraMap B L (x j))) : Module.Basis (Fin n) L (Ω[L⁄A]) :=
  bL.unitsSMul fun j ↦ (isUnit_logScale hP j).unit

variable {bL} (hP : ∀ j ∈ P, IsUnit (algebraMap B L (x j)))

/-- `εⱼ = logScale P x j • bⱼ`. -/
theorem logBasis_apply (j : Fin n) : logBasis bL hP j = logScale (L := L) P x j • bL j := by
  rw [logBasis, Module.Basis.unitsSMul_apply, Units.smul_def, IsUnit.unit_spec]

/-- The `j`-th coordinate of `w` in the logarithmic basis is `poleFactor P x j` times its
`j`-th coordinate in `bL`. -/
theorem logBasis_repr (w : Ω[L⁄A]) (j : Fin n) :
    (logBasis bL hP).repr w j = algebraMap B L (poleFactor P x j) * bL.repr w j := by
  rw [logBasis, Module.Basis.repr_unitsSMul, Units.smul_def, smul_eq_mul]
  congr 1
  exact Units.inv_eq_of_mul_eq_one_right (by rw [IsUnit.unit_spec, logScale_mul_poleFactor hP])

/-- The wedge `ε_s` is `∏_{j ∈ s} logScale P x j` times the corresponding wedge of `bL`. -/
theorem logBasis_exteriorPower_apply {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    (logBasis bL hP).exteriorPower i s =
      (∏ k, logScale (L := L) P x (enum s k)) • bL.exteriorPower i s := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply, ιMulti_family, ιMulti_family,
    ← AlternatingMap.map_smul_univ]
  congr 1
  funext k
  exact logBasis_apply hP _

variable {ι : Type*} {u : ι → B} (hb : ∀ j, bL j = D A L (algebraMap B L (x j)))
  (hu₁ : ∀ k, ∃ j ∈ P, x j = u k) (hu₂ : ∀ j ∈ P, ∃ k, u k = x j)

include hb

include hu₂ in
/-- Each element `εⱼ` of the logarithmic basis is a logarithmic generator. -/
theorem logBasis_mem_logGenerators (j : Fin n) : logBasis bL hP j ∈ logGenerators A L u := by
  rw [logBasis_apply, hb, logScale]
  split_ifs with h
  · obtain ⟨k, hk⟩ := hu₂ j h
    rw [← hk]
    exact dlog_mem_logGenerators u k
  · rw [one_smul]
    exact D_mem_logGenerators u _

include hu₁ in
/-- The coordinates of a logarithmic generator in the logarithmic basis lie in `B`. -/
theorem logBasis_repr_mem_range
    (hcoord : ∀ (b : B) j, bL.repr (D A L (algebraMap B L b)) j ∈ Set.range (algebraMap B L))
    {w : Ω[L⁄A]} (hw : w ∈ logGenerators A L u) (j : Fin n) :
    (logBasis bL hP).repr w j ∈ Set.range (algebraMap B L) := by
  rcases hw with ⟨b, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨c, hc⟩ := hcoord b j
    rw [logBasis_repr, ← hc, ← map_mul]
    exact ⟨_, rfl⟩
  · obtain ⟨j₀, hj₀, hk⟩ := hu₁ k
    dsimp only
    have he : Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k)) =
        logBasis bL hP j₀ := by
      rw [logBasis_apply, hb, logScale, ite_eq_left hj₀, hk]
    rw [he, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩

include hu₁ in
/-- **The coefficients of a logarithmic form in the logarithmic basis lie in `B`.** -/
theorem logBasis_exteriorPower_repr_mem_range
    (hcoord : ∀ (b : B) j, bL.repr (D A L (algebraMap B L b)) j ∈ Set.range (algebraMap B L))
    {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) (s : Set.powersetCard (Fin n) i) :
    ((logBasis bL hP).exteriorPower i).repr y s ∈ Set.range (algebraMap B L) := by
  let S : Submodule B (⋀[L]^i (Ω[L⁄A])) :=
    { carrier := {z | ∀ s, ((logBasis bL hP).exteriorPower i).repr z s ∈
        Set.range (algebraMap B L)}
      zero_mem' := fun s ↦ ⟨0, by simp⟩
      add_mem' := by
        intro z z' hz hz' s
        obtain ⟨c, hc⟩ := hz s
        obtain ⟨c', hc'⟩ := hz' s
        exact ⟨c + c', by rw [map_add, hc, hc', map_add, Finsupp.add_apply]⟩
      smul_mem' := by
        intro b z hz s
        obtain ⟨c, hc⟩ := hz s
        refine ⟨b * c, ?_⟩
        rw [← algebraMap_smul L b z, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hc] }
  refine mem_of_mem_logForms S (fun v hv s ↦ ?_) y hy s
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  choose c hc using fun a b ↦ logBasis_repr_mem_range hP hb hu₁ hcoord (hv a) (enum s b)
  have hM : (Matrix.of fun a b ↦ (logBasis bL hP).coord (enum s b) (v a)) =
      (algebraMap B L).mapMatrix (Matrix.of c) := by
    ext a b
    simp [hc]
  rw [hM, ← RingHom.map_det]
  exact ⟨_, rfl⟩

include hu₂ in
/-- Each wedge `ε_s` of the logarithmic basis is a logarithmic form. -/
theorem coe_logBasis_exteriorPower_mem_logForms {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    (((logBasis bL hP).exteriorPower i s : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈
      logForms A L u i := by
  rw [exteriorPower.basis_apply, ιMulti_family, exteriorPower.ιMulti_apply_coe]
  exact ιMulti_mem_logForms _ fun k ↦ logBasis_mem_logGenerators hP hb hu₂ _

include hu₂ in
/-- A `B`-combination `∑ c_s ε_s` of the wedges of the logarithmic basis is a logarithmic
form. -/
theorem coe_sum_logBasis_mem_logForms {i : ℕ} (c : Set.powersetCard (Fin n) i → B) :
    ((∑ s, algebraMap B L (c s) • (logBasis bL hP).exteriorPower i s : ⋀[L]^i (Ω[L⁄A])) :
      ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i := by
  rw [Submodule.coe_sum]
  refine Submodule.sum_mem _ fun s _ ↦ ?_
  rw [Submodule.coe_smul, algebraMap_smul]
  exact Submodule.smul_mem _ _ (coe_logBasis_exteriorPower_mem_logForms hP hb hu₂ s)

include hu₁ in
/-- **A logarithmic form is a `B`-combination of the wedges of the logarithmic basis.** -/
theorem exists_eq_sum_logBasis
    (hcoord : ∀ (b : B) j, bL.repr (D A L (algebraMap B L b)) j ∈ Set.range (algebraMap B L))
    {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    ∃ c : Set.powersetCard (Fin n) i → B,
      y = ∑ s, algebraMap B L (c s) • (logBasis bL hP).exteriorPower i s := by
  choose c hc using logBasis_exteriorPower_repr_mem_range hP hb hu₁ hcoord y hy
  refine ⟨c, ?_⟩
  conv_lhs => rw [← ((logBasis bL hP).exteriorPower i).sum_repr y]
  exact Finset.sum_congr rfl fun s _ ↦ by rw [hc]

include hP hu₁ in
/-- **The Euler vector fields take values in `B` on the logarithmic generators.** -/
theorem eulerField_mem_range
    (hcoord : ∀ (b : B) j, bL.repr (D A L (algebraMap B L b)) j ∈ Set.range (algebraMap B L))
    (j : Fin n) {w : Ω[L⁄A]} (hw : w ∈ logGenerators A L u) :
    eulerField A (fun j ↦ algebraMap B L (x j)) bL j w ∈ Set.range (algebraMap B L) := by
  rcases hw with ⟨b, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨c, hc⟩ := hcoord b j
    rw [eulerField, LinearMap.smul_apply, Module.Basis.coord_apply, ← hc, smul_eq_mul, ← map_mul]
    exact ⟨_, rfl⟩
  · obtain ⟨j₀, hj₀, hk⟩ := hu₁ k
    dsimp only
    rw [← hk, map_smul, eulerField_D hb, smul_eq_mul]
    split_ifs
    · exact ⟨1, by rw [map_one, Ring.inverse_mul_cancel _ (hP j₀ hj₀)]⟩
    · exact ⟨0, by rw [map_zero, mul_zero]⟩

end LogBasis

/-! ### The weight projection on logarithmic forms

With `θⱼ = xⱼ ∂/∂xⱼ` the Euler fields, the form `c^p x^α ε_s` (`c ∈ B`, `0 ≤ αⱼ < p`) is the
spanning form `(c x_{s ∩ P}⁻¹)^p x^{α + (p - 1) 1_{s ∩ P}} dx_s` of the non-logarithmic theory,
of `j`-th weight `αⱼ + [j ∈ s ∖ P]` modulo `p`: `dlog xⱼ` has weight `0`. So the projector
`π = ∏ⱼ (1 - L_{θⱼ}^{p-1})` keeps exactly the forms `c^p x_{s ∖ P}^{p-1} ε_s`. -/

section Projection

variable (p : ℕ) [Fact p.Prime] {A B L : Type u} [CommRing A] [CommRing B] [CommRing L]
  [Algebra A L] [Algebra B L] {n : ℕ} (P : Finset (Fin n))

/-- The exponent `α + (p - 1) 1_{s ∩ P}`. -/
def logShift {i : ℕ} (s : Set.powersetCard (Fin n) i) (α : Fin n → ℕ) : Fin n → ℕ :=
  fun j ↦ α j + if j ∈ (s : Finset (Fin n)) ∧ j ∈ P then p - 1 else 0

/-- The exponent `(p - 1) 1_{s ∖ P}` of the logarithmic Cartier form attached to `s`. -/
def logExponent {i : ℕ} (s : Set.powersetCard (Fin n) i) : Fin n → Fin p :=
  fun j ↦ if j ∈ (s : Finset (Fin n)) ∧ j ∉ P then
    ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩ else ⟨0, (Fact.out : p.Prime).pos⟩

variable {p P}

/-- For `a < p`, the number `a + (p - 1)[s ∧ P] + [s]` is divisible by `p` exactly when
`a = (p - 1)[s ∧ ¬P]`. -/
theorem dvd_logShift_iff {a : ℕ} (ha : a < p) (hs hP : Prop) [Decidable hs] [Decidable hP] :
    p ∣ a + (if hs ∧ hP then p - 1 else 0) + (if hs then 1 else 0) ↔
      a = if hs ∧ ¬hP then p - 1 else 0 := by
  have hp := (Fact.out : p.Prime).two_le
  by_cases h₁ : hs <;> by_cases h₂ : hP <;> simp only [h₁, h₂, not_true_eq_false,
    not_false_eq_true, and_true, and_false, ite_true, ite_false, add_zero]
  · rw [show a + (p - 1) + 1 = a + p by omega, Nat.dvd_add_self_right]
    exact ⟨fun h ↦ Nat.eq_zero_of_dvd_of_lt h ha, fun h ↦ h ▸ dvd_zero p⟩
  · constructor
    · intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    · intro h
      rw [h, Nat.sub_add_cancel (by omega)]
  · exact ⟨fun h ↦ Nat.eq_zero_of_dvd_of_lt h ha, fun h ↦ h ▸ dvd_zero p⟩
  · exact ⟨fun h ↦ Nat.eq_zero_of_dvd_of_lt h ha, fun h ↦ h ▸ dvd_zero p⟩

/-- **The weights of `c^p x^α ε_s` are all divisible by `p` exactly when `α` is the logarithmic
Cartier exponent of `s`.** -/
theorem forall_dvd_logShift_iff {i : ℕ} (s : Set.powersetCard (Fin n) i) (α : Fin n → Fin p) :
    (∀ j ∈ List.finRange n,
      p ∣ (logShift p P s (fun j ↦ (α j : ℕ)) j + ∑ k, if enum s k = j then 1 else 0)) ↔
      α = logExponent p P s := by
  constructor
  · intro h
    funext j
    apply Fin.ext
    have hj := h j (List.mem_finRange j)
    rw [sum_enum_eq, logShift, dvd_logShift_iff (α j).2] at hj
    rw [hj, logExponent]
    split_ifs <;> rfl
  · rintro rfl j _
    rw [sum_enum_eq, logShift, dvd_logShift_iff (logExponent p P s j).2, logExponent]
    split_ifs <;> rfl

/-- Shifting the logarithmic Cartier exponent of `s` gives the Cartier exponent
`(p - 1) 1_s`. -/
theorem logShift_logExponent {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    logShift p P s (fun j ↦ (logExponent p P s j : ℕ)) = fun j ↦ (cartierExponent p s j : ℕ) := by
  funext j
  simp only [logShift, logExponent, cartierExponent]
  by_cases h₁ : j ∈ (s : Finset (Fin n)) <;> by_cases h₂ : j ∈ P <;> simp [h₁, h₂]

/-- The product of `f` over the enumeration of `s` is the product of `f` over `s`. -/
theorem prod_enum {M : Type*} [CommMonoid M] {i : ℕ} (s : Set.powersetCard (Fin n) i)
    (f : Fin n → M) : ∏ k, f (enum s k) = ∏ j ∈ (s : Finset (Fin n)), f j := by
  have h : ((s : Finset (Fin n))) =
      Finset.univ.map (Set.powersetCard.ofFinEmbEquiv.symm s).toEmbedding := by
    ext j
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    exact (exists_enum_eq_iff s j).symm
  rw [h, Finset.prod_map]
  rfl

variable {x : Fin n → B}

/-- The image in `L` of the monomial `x^α` is the monomial in the images of the `xⱼ`. -/
theorem algebraMap_monomial (α : Fin n → ℕ) :
    algebraMap B L (monomial x α) = monomial (fun j ↦ algebraMap B L (x j)) α := by
  simp [monomial, map_prod, map_pow]

variable (hP : ∀ j ∈ P, IsUnit (algebraMap B L (x j)))

include hP

/-- `∏_{j ∈ s} logScale P x j * ∏_{j ∈ s} poleFactor P x j = 1`. -/
theorem prod_logScale_mul_prod_poleFactor {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    (∏ k, logScale (L := L) P x (enum s k)) *
      algebraMap B L (∏ k, poleFactor P x (enum s k)) = 1 := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun k _ ↦ logScale_mul_poleFactor hP _

/-- With `λ = ∏_{j ∈ s} logScale P x j = x_{s ∩ P}⁻¹`, one has `λ^p x_{s ∩ P}^{p-1} = λ`. -/
theorem prod_logScale_eq {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    (∏ k, logScale (L := L) P x (enum s k)) ^ p *
      ∏ j, algebraMap B L (x j) ^ (if j ∈ (s : Finset (Fin n)) ∧ j ∈ P then p - 1 else 0) =
      ∏ k, logScale (L := L) P x (enum s k) := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
  rw [prod_enum, ← Finset.prod_subset (Finset.subset_univ (s : Finset (Fin n)))
    (fun j _ hj ↦ by rw [ite_eq_right (fun h ↦ hj h.1), pow_zero]), ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  simp only [logScale, hj, true_and]
  split_ifs with h
  · rw [hq, Nat.add_sub_cancel, pow_succ', mul_assoc, ← mul_pow,
      Ring.inverse_mul_cancel _ (hP j h), one_pow, mul_one]
  · simp

variable {bL : Module.Basis (Fin n) L (Ω[L⁄A])} (hb : ∀ j, bL j = D A L (algebraMap B L (x j)))

include hb

/-- **`c^p x^α ε_s` is a spanning form of the non-logarithmic theory.** -/
theorem smul_logBasis_eq_spanForm (c : B) (α : Fin n → ℕ) {i : ℕ}
    (s : Set.powersetCard (Fin n) i) :
    (algebraMap B L c ^ p * monomial (fun j ↦ algebraMap B L (x j)) α) •
        (logBasis bL hP).exteriorPower i s =
      spanForm p A (fun j ↦ algebraMap B L (x j))
        (algebraMap B L c * ∏ k, logScale (L := L) P x (enum s k)) (logShift p P s α)
        (enum s) := by
  rw [logBasis_exteriorPower_apply, exteriorPower_basis_eq hb, smul_smul, spanForm]
  congr 1
  have hm : monomial (fun j ↦ algebraMap B L (x j)) (logShift p P s α) =
      monomial (fun j ↦ algebraMap B L (x j)) α *
        ∏ j, algebraMap B L (x j) ^ (if j ∈ (s : Finset (Fin n)) ∧ j ∈ P then p - 1 else 0) := by
    simp only [monomial, logShift, pow_add, Finset.prod_mul_distrib]
  rw [hm]
  linear_combination (algebraMap B L c ^ p * monomial (fun j ↦ algebraMap B L (x j)) α) *
    (prod_logScale_eq (p := p) hP s).symm

variable [CharP L p] {ι : Type*} {u : ι → B}
  (hu₁ : ∀ k, ∃ j ∈ P, x j = u k) (hu₂ : ∀ j ∈ P, ∃ k, u k = x j)
  (hcoord : ∀ (b : B) j, bL.repr (D A L (algebraMap B L b)) j ∈ Set.range (algebraMap B L))

include hu₁ hu₂ hcoord

/-- **The projection of a logarithmic form is the Cartier representative of a logarithmic
form.** -/
theorem exists_projList_eq_cartierRep_of_mem_logForms (hF : IsFrobeniusCoordinates p B x)
    {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    ∃ ω : ⋀[L]^i (Ω[L⁄A]), (ω : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧
      projList p A (fun j ↦ algebraMap B L (x j)) bL (List.finRange n) i y =
        cartierRep p A (fun j ↦ algebraMap B L (x j)) bL i ω := by
  classical
  obtain ⟨c, rfl⟩ := exists_eq_sum_logBasis hP hb hu₁ hcoord y hy
  choose d hd using fun s ↦ hF.2 (c s)
  have hx : ∑ s, algebraMap B L (c s) • (logBasis bL hP).exteriorPower i s =
      ∑ s, ∑ α, spanForm p A (fun j ↦ algebraMap B L (x j))
        (algebraMap B L (d s α) * ∏ k, logScale (L := L) P x (enum s k))
        (logShift p P s (fun j ↦ (α j : ℕ))) (enum s) := by
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← hd s, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [← smul_logBasis_eq_spanForm hP hb, map_mul, map_pow, algebraMap_monomial]
  refine ⟨∑ s, algebraMap B L (d s (logExponent p P s)) • (logBasis bL hP).exteriorPower i s,
    coe_sum_logBasis_mem_logForms hP hb hu₂ _, ?_⟩
  rw [hx, map_sum]
  change _ = cartierRepHom p (fun j ↦ algebraMap B L (x j)) bL i _
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_sum]
  simp only [projList_spanForm p hb, forall_dvd_logShift_iff]
  rw [Finset.sum_ite_eq' Finset.univ (logExponent p P s), ite_eq_left (Finset.mem_univ _),
    logShift_logExponent]
  change _ = cartierRep p A (fun j ↦ algebraMap B L (x j)) bL i _
  rw [logBasis_exteriorPower_apply, smul_smul, cartierRep_smul_basis,
    cartierBasisForm_eq_spanForm, spanForm, spanForm, smul_smul, one_pow, one_mul]

omit [CharP L p] hu₂ in
/-- **A closed logarithmic form is cohomologous, through logarithmic forms, to its
projection**, and the projection is again logarithmic and closed. -/
theorem projList_mem_logForms_of_closed (l : List (Fin n)) (i : ℕ) (y : ⋀[L]^i (Ω[L⁄A]))
    (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i)
    (hcl : deRhamDifferential (A := A) i y = 0) :
    ((projList p A (fun j ↦ algebraMap B L (x j)) bL l i y : ⋀[L]^i (Ω[L⁄A])) :
        ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i ∧
      deRhamDifferential (A := A) i (projList p A (fun j ↦ algebraMap B L (x j)) bL l i y) = 0 ∧
      ((y - projList p A (fun j ↦ algebraMap B L (x j)) bL l i y : ⋀[L]^i (Ω[L⁄A])) :
        ExteriorAlgebra L (Ω[L⁄A])) ∈ exactLogForms A L u i := by
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = m + 1 :=
    ⟨p - 2, by have := (Fact.out : p.Prime).two_le; omega⟩
  induction l with
  | nil =>
    refine ⟨hy, hcl, ?_⟩
    rw [show projList p A (fun j ↦ algebraMap B L (x j)) bL [] i y = y from rfl, sub_self]
    exact zero_mem_exactLogForms u i
  | cons j l ih =>
    obtain ⟨hlog, hcl', hex⟩ := ih
    set y' := projList p A (fun j ↦ algebraMap B L (x j)) bL l i y
    set θ := eulerField A (fun j ↦ algebraMap B L (x j)) bL j
    have hθ : ∀ w ∈ logGenerators A L u, θ w ∈ Set.range (algebraMap B L) :=
      fun w hw ↦ eulerField_mem_range hP hb hu₁ hcoord j hw
    change ((weightProj p A _ bL j i y' : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈ _ ∧
      deRhamDifferential (A := A) i (weightProj p A _ bL j i y') = 0 ∧
      ((y - weightProj p A _ bL j i y' : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈ _
    have hw : weightProj p A (fun j ↦ algebraMap B L (x j)) bL j i y' =
        y' - (lie A θ i ^ (m + 1)) y' := by
      rw [weightProj, LinearMap.sub_apply, LinearMap.id_apply, hm]
    have hlie_log := coe_lie_pow_mem_logForms θ hθ i (m + 1) y' hlog
    refine ⟨?_, ?_, ?_⟩
    · rw [hw, Submodule.coe_sub]
      exact sub_mem hlog hlie_log
    · rw [hw, map_sub, hcl', deRhamDifferential_lie_pow_eq_zero A _ i (m + 1) y' hcl', sub_zero]
    · have hlie : (((lie A θ i ^ (m + 1)) y' : ⋀[L]^i (Ω[L⁄A])) :
          ExteriorAlgebra L (Ω[L⁄A])) ∈ exactLogForms A L u i := by
        cases i with
        | zero =>
          rw [lie_pow_zero_eq_zero_of_closed A _ m y' hcl']
          exact zero_mem_exactLogForms u 0
        | succ k =>
          rw [lie_pow_eq_deRhamDifferential A _ k m y' hcl']
          exact coe_deRhamDifferential_mem_exactLogForms _
            (coe_lie_pow_mem_logForms θ hθ k m _ (coe_contraction_mem_logForms θ hθ k y' hlog))
      have : y - weightProj p A (fun j ↦ algebraMap B L (x j)) bL j i y' =
          (y - y') + (lie A θ i ^ (m + 1)) y' := by
        rw [hw]; abel
      rw [this, Submodule.coe_add]
      exact add_mem_exactLogForms hex hlie

end Projection

/-! ### The Cartier representative

For a basis `dt₁, …, dtₙ` of `Ω[L⁄A]`, `cartierRep` is Frobenius-semilinear, and it is
multiplicative up to exact forms: both `cartierRep (ω ∧ η)` and `cartierRep ω ∧ cartierRep η`
represent `C⁻¹(ω ∧ η)`, which on `dt_s ∧ dt_{s'}` is computed by
`KaehlerDifferential.Cartier.inverseCartier_ιMulti_D`. -/

section CartierRep

variable (p : ℕ) [Fact p.Prime] {A L : Type u} [CommRing A] [CommRing L] [Algebra A L]
  [CharP L p] {n : ℕ} {t : Fin n → L} {b : Module.Basis (Fin n) L (Ω[L⁄A])}

omit [Fact p.Prime] [CharP L p] in
/-- The Cartier representative is Frobenius-semilinear:
`cartierRep (c • ω) = c ^ p • cartierRep ω`. -/
theorem cartierRep_smul (i : ℕ) (c : L) (ω : ⋀[L]^i (Ω[L⁄A])) :
    cartierRep p A t b i (c • ω) = c ^ p • cartierRep p A t b i ω := by
  simp only [cartierRep, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_pow, Finset.smul_sum,
    smul_smul]

/-- The Cartier representative commutes with finite sums. -/
theorem cartierRep_sum {κ : Type*} (s : Finset κ) (i : ℕ) (f : κ → ⋀[L]^i (Ω[L⁄A])) :
    cartierRep p A t b i (∑ k ∈ s, f k) = ∑ k ∈ s, cartierRep p A t b i (f k) :=
  map_sum (cartierRepHom p t b i) f s

omit [CharP L p] in
/-- The Cartier representative of the basis wedge indexed by `s` is `cartierBasisForm p A t s`. -/
theorem cartierRep_basis {i : ℕ} (s : Set.powersetCard (Fin n) i) :
    cartierRep p A t b i (b.exteriorPower i s) = cartierBasisForm p A t s := by
  simpa using cartierRep_smul_basis p (t := t) (b := b) (1 : L) s

/-- The Cartier representative of `ω = ∑ c_s b_s` is `∑ c_s ^ p • cartierRep b_s`. -/
theorem cartierRep_eq_sum {i : ℕ} (ω : ⋀[L]^i (Ω[L⁄A])) :
    cartierRep p A t b i ω =
      ∑ s, ((b.exteriorPower i).repr ω s) ^ p • cartierRep p A t b i (b.exteriorPower i s) := by
  conv_lhs => rw [← (b.exteriorPower i).sum_repr ω]
  rw [cartierRep_sum]
  simp only [cartierRep_smul]

omit [CharP L p] in
/-- `(∑ aₖ Xₖ) ∧ (∑ a'ₗ Yₗ) = ∑ₖ ∑ₗ aₖ a'ₗ (Xₖ ∧ Yₗ)`. -/
theorem wedgeMul_sum_smul {κ κ' : Type*} [Fintype κ] [Fintype κ'] {i j : ℕ} (a : κ → L)
    (X : κ → ⋀[L]^i (Ω[L⁄A])) (a' : κ' → L) (Y : κ' → ⋀[L]^j (Ω[L⁄A])) :
    wedgeMul i j (∑ k, a k • X k) (∑ k', a' k' • Y k') =
      ∑ k, ∑ k', (a k * a' k') • wedgeMul i j (X k) (Y k') := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- If the Frobenius twist of `y` is exact, so is that of `c ^ p • y`. -/
theorem twist_smul_mem_exactForms {i : ℕ} (c : L) {y : ⋀[L]^i (Ω[L⁄A])}
    (hy : twist p y ∈ exactForms p A L i) : twist p (c ^ p • y) ∈ exactForms p A L i := by
  rw [← smul_twist]
  exact Submodule.smul_mem _ c hy

variable (hb : ∀ j, b j = D A L (t j))

include hb

omit hb in
/-- `Fin.append (f ∘ g) (f ∘ h) = f ∘ Fin.append g h`. -/
theorem fin_append_comp {α β : Type*} (f : α → β) {i j : ℕ} (g : Fin i → α) (h : Fin j → α) :
    Fin.append (fun k ↦ f (g k)) (fun k ↦ f (h k)) = fun k ↦ f (Fin.append g h k) := by
  funext k
  refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) k <;> simp

/-- **The Cartier representative is multiplicative up to exact forms.** -/
theorem twist_cartierRep_wedgeMul_sub_mem_exactForms (i j : ℕ) (ω : ⋀[L]^i (Ω[L⁄A]))
    (η : ⋀[L]^j (Ω[L⁄A])) :
    twist p (cartierRep p A t b (i + j) (wedgeMul i j ω η) -
      wedgeMul i j (cartierRep p A t b i ω) (cartierRep p A t b j η)) ∈
        exactForms p A L (i + j) := by
  classical
  have hbasis : ∀ (s : Set.powersetCard (Fin n) i) (s' : Set.powersetCard (Fin n) j),
      twist p (cartierRep p A t b (i + j)
          (wedgeMul i j (b.exteriorPower i s) (b.exteriorPower j s')) -
        wedgeMul i j (cartierRep p A t b i (b.exteriorPower i s))
          (cartierRep p A t b j (b.exteriorPower j s'))) ∈ exactForms p A L (i + j) := by
    intro s s'
    rw [cartierRep_basis, cartierRep_basis, exteriorPower_basis_eq hb, exteriorPower_basis_eq hb,
      wedgeMul_ιMulti, cartierBasisForm, cartierBasisForm, wedgeMul_ιMulti,
      fin_append_comp (fun y ↦ D A L y) (fun k ↦ t (enum s k)) (fun k ↦ t (enum s' k)),
      fin_append_comp (fun y ↦ y ^ (p - 1) • D A L y) (fun k ↦ t (enum s k))
        (fun k ↦ t (enum s' k))]
    have key := inverseCartier_eq_cohomologyMk_cartierRep p hb (i + j)
      (ιMulti L (i + j) fun k ↦ D A L (Fin.append (fun k ↦ t (enum s k))
        (fun k ↦ t (enum s' k)) k))
    rw [inverseCartier_ιMulti_D, eq_comm, cohomologyMk_eq_iff, coe_wedgeClosed_cartierForm] at key
    rw [map_sub]
    exact key
  have h1 : cartierRep p A t b (i + j) (wedgeMul i j ω η) =
      ∑ s, ∑ s', ((b.exteriorPower i).repr ω s * (b.exteriorPower j).repr η s') ^ p •
        cartierRep p A t b (i + j) (wedgeMul i j (b.exteriorPower i s) (b.exteriorPower j s')) := by
    conv_lhs => rw [← (b.exteriorPower i).sum_repr ω, ← (b.exteriorPower j).sum_repr η]
    rw [wedgeMul_sum_smul, cartierRep_sum]
    simp only [cartierRep_sum, cartierRep_smul]
  have h2 : wedgeMul i j (cartierRep p A t b i ω) (cartierRep p A t b j η) =
      ∑ s, ∑ s', ((b.exteriorPower i).repr ω s * (b.exteriorPower j).repr η s') ^ p •
        wedgeMul i j (cartierRep p A t b i (b.exteriorPower i s))
          (cartierRep p A t b j (b.exteriorPower j s')) := by
    rw [cartierRep_eq_sum p ω, cartierRep_eq_sum p η, wedgeMul_sum_smul]
    simp only [mul_pow]
  have hsum : cartierRep p A t b (i + j) (wedgeMul i j ω η) -
      wedgeMul i j (cartierRep p A t b i ω) (cartierRep p A t b j η) =
      ∑ s, ∑ s', ((b.exteriorPower i).repr ω s * (b.exteriorPower j).repr η s') ^ p •
        (cartierRep p A t b (i + j)
          (wedgeMul i j (b.exteriorPower i s) (b.exteriorPower j s')) -
        wedgeMul i j (cartierRep p A t b i (b.exteriorPower i s))
          (cartierRep p A t b j (b.exteriorPower j s'))) := by
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    simp only [smul_sub]
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun s _ ↦ ?_
  rw [map_sum]
  exact Submodule.sum_mem _ fun s' _ ↦ twist_smul_mem_exactForms p _ (hbasis s s')

/-- `C⁻¹(db)` is represented by `b^{p-1} db`. -/
theorem twist_cartierRep_one_sub_mem_exactForms (c : L) :
    twist p (cartierRep p A t b 1 (ιMulti L 1 fun _ ↦ D A L c) -
      c ^ (p - 1) • ιMulti L 1 fun _ ↦ D A L c) ∈ exactForms p A L 1 := by
  have key := inverseCartier_eq_cohomologyMk_cartierRep p hb 1 (ιMulti L 1 fun _ ↦ D A L c)
  rw [inverseCartier_ιMulti_D p (fun _ : Fin 1 ↦ c), eq_comm, cohomologyMk_eq_iff,
    coe_wedgeClosed_cartierForm] at key
  rw [map_sub, ← ιMulti_one_smul]
  exact key

end CartierRep

/-! ### The logarithmic inverse Cartier isomorphism -/

section Main

open scoped Classical in
/-- The Cartier representative, extended by zero from `⋀^i Ω[L⁄A]` to the exterior algebra. -/
def cartierRepExt (p : ℕ) {A L : Type u} [CommRing A] [CommRing L] [Algebra A L] {n : ℕ}
    (t : Fin n → L) (b : Module.Basis (Fin n) L (Ω[L⁄A])) (i : ℕ)
    (ω : ExteriorAlgebra L (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A]) :=
  if h : ω ∈ ⋀[L]^i (Ω[L⁄A]) then (cartierRep p A t b i ⟨ω, h⟩ : ExteriorAlgebra L (Ω[L⁄A]))
  else 0

/-- On `⋀^i Ω[L⁄A]`, the extended Cartier representative is the Cartier representative. -/
theorem cartierRepExt_coe (p : ℕ) {A L : Type u} [CommRing A] [CommRing L] [Algebra A L]
    {n : ℕ} (t : Fin n → L) (b : Module.Basis (Fin n) L (Ω[L⁄A])) {i : ℕ}
    (y : ⋀[L]^i (Ω[L⁄A])) :
    cartierRepExt p t b i (y : ExteriorAlgebra L (Ω[L⁄A])) = (cartierRep p A t b i y : _) := by
  rw [cartierRepExt, dite_eq_left y.2]

/-- The wedge of a single vector `w` is `ι w` in the exterior algebra. -/
theorem coe_ιMulti_one {L M : Type*} [CommRing L] [AddCommGroup M] [Module L M] (w : M) :
    ((ιMulti L 1 fun _ ↦ w : ⋀[L]^1 M) : ExteriorAlgebra L M) = ExteriorAlgebra.ι L w := by
  rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]

variable {A B L : Type u} [CommRing A] [CommRing B] [CommRing L] [Algebra A L] [Algebra B L]
  {ι : Type*}

/-- **The logarithmic forms are closed under the wedge product.** -/
theorem mul_mem_logForms {u : ι → B} {i j : ℕ} {ω η : ExteriorAlgebra L (Ω[L⁄A])}
    (hω : ω ∈ logForms A L u i) (hη : η ∈ logForms A L u j) :
    ω * η ∈ logForms A L u (i + j) := by
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    induction hη using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
      refine ιMulti_mem_logForms _ fun m ↦ ?_
      refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) m
      · rw [Fin.append_left]; exact hv k
      · rw [Fin.append_right]; exact hw k
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

variable (p : ℕ) [Fact p.Prime] [CharP L p]

/-- An exact logarithmic form is exact. -/
theorem twist_mem_exactForms_of_coe_mem_exactLogForms {u : ι → B} {i : ℕ}
    (y : ⋀[L]^i (Ω[L⁄A])) (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ exactLogForms A L u i) :
    twist p y ∈ exactForms p A L i := by
  rcases hy with h | ⟨j, x, rfl, -, h⟩
  · rw [show y = 0 from Subtype.coe_injective h, map_zero]
    exact zero_mem _
  · rw [show y = deRhamDifferential (A := A) j x from (Subtype.coe_injective h).symm]
    exact (twist_mem_exactForms_succ _).2 ⟨x, rfl⟩

variable {n : ℕ} {P : Finset (Fin n)} {x : Fin n → B}
  (hP : ∀ j ∈ P, IsUnit (algebraMap B L (x j)))
  {bL : Module.Basis (Fin n) L (Ω[L⁄A])} (hb : ∀ j, bL j = D A L (algebraMap B L (x j)))
  {u : ι → B} (hu₁ : ∀ k, ∃ j ∈ P, x j = u k) (hu₂ : ∀ j ∈ P, ∃ k, u k = x j)
  (hcoord : ∀ (b : B) j, bL.repr (D A L (algebraMap B L b)) j ∈ Set.range (algebraMap B L))

include hP hb

/-- **The Cartier representative on the logarithmic basis**:
`c ε_s ↦ c^p x_{s ∖ P}^{p-1} ε_s`. -/
theorem cartierRep_sum_logBasis {i : ℕ} (c : Set.powersetCard (Fin n) i → B) :
    cartierRep p A (fun j ↦ algebraMap B L (x j)) bL i
        (∑ s, algebraMap B L (c s) • (logBasis bL hP).exteriorPower i s) =
      ∑ s, algebraMap B L (c s ^ p * monomial x (fun j ↦ (logExponent p P s j : ℕ))) •
        (logBasis bL hP).exteriorPower i s := by
  rw [cartierRep_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have h := smul_logBasis_eq_spanForm (p := p) hP hb (c s)
    (fun j ↦ (logExponent p P s j : ℕ)) s
  rw [map_mul, map_pow, algebraMap_monomial, h, logShift_logExponent, spanForm,
    logBasis_exteriorPower_apply, smul_smul, cartierRep_smul_basis, cartierBasisForm_eq_spanForm,
    spanForm, smul_smul, one_pow, one_mul]

include hu₁ hu₂ hcoord

/-- The Cartier representative of a logarithmic form is logarithmic. -/
theorem coe_cartierRep_mem_logForms {i : ℕ} (y : ⋀[L]^i (Ω[L⁄A]))
    (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i) :
    ((cartierRep p A (fun j ↦ algebraMap B L (x j)) bL i y : ⋀[L]^i (Ω[L⁄A])) :
      ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i := by
  obtain ⟨c, rfl⟩ := exists_eq_sum_logBasis hP hb hu₁ hcoord y hy
  rw [cartierRep_sum_logBasis p hP hb]
  exact coe_sum_logBasis_mem_logForms hP hb hu₂ _

/-- **A closed logarithmic form which is exact is the differential of a logarithmic form.** -/
theorem coe_mem_exactLogForms_of_twist_mem_exactForms (hF : IsFrobeniusCoordinates p B x)
    (hFL : IsFrobeniusCoordinates p L (fun j ↦ algebraMap B L (x j))) {i : ℕ}
    (y : ⋀[L]^i (Ω[L⁄A])) (hy : (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i)
    (hcl : deRhamDifferential (A := A) i y = 0) (hex : twist p y ∈ exactForms p A L i) :
    (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ exactLogForms A L u i := by
  obtain ⟨-, -, hdiff⟩ := projList_mem_logForms_of_closed (p := p) hP hb hu₁ hcoord
    (List.finRange n) i y hy hcl
  obtain ⟨ω, -, hω⟩ := exists_projList_eq_cartierRep_of_mem_logForms hP hb hu₁ hu₂ hcoord hF y hy
  have hzero : ω = 0 := by
    apply (inverseCartier_bijective_of_isFrobeniusCoordinates p hb hFL i).1
    rw [map_zero, inverseCartier_eq_cohomologyMk_cartierRep p hb, cohomologyMk_eq_zero_iff]
    change twist p (cartierRep p A _ bL i ω) ∈ _
    have h := sub_mem hex (twist_mem_exactForms_of_coe_mem_exactLogForms p _ hdiff)
    rwa [← map_sub, sub_sub_cancel, hω] at h
  rwa [hω, hzero, cartierRep_zero, sub_zero] at hdiff

/-- **The Cartier representative is multiplicative modulo exact logarithmic forms.** -/
theorem cartierRepExt_mul_sub_mem_exactLogForms (hF : IsFrobeniusCoordinates p B x)
    (hFL : IsFrobeniusCoordinates p L (fun j ↦ algebraMap B L (x j))) {i j : ℕ}
    {ω η : ExteriorAlgebra L (Ω[L⁄A])} (hω : ω ∈ logForms A L u i)
    (hη : η ∈ logForms A L u j) :
    cartierRepExt p (fun l ↦ algebraMap B L (x l)) bL (i + j) (ω * η) -
        cartierRepExt p (fun l ↦ algebraMap B L (x l)) bL i ω *
          cartierRepExt p (fun l ↦ algebraMap B L (x l)) bL j η ∈
      exactLogForms A L u (i + j) := by
  obtain ⟨y, rfl⟩ : ∃ y : ⋀[L]^i (Ω[L⁄A]), (y : ExteriorAlgebra L (Ω[L⁄A])) = ω :=
    ⟨⟨ω, logForms_le u i hω⟩, rfl⟩
  obtain ⟨y', rfl⟩ : ∃ y' : ⋀[L]^j (Ω[L⁄A]), (y' : ExteriorAlgebra L (Ω[L⁄A])) = η :=
    ⟨⟨η, logForms_le u j hη⟩, rfl⟩
  rw [← wedgeMul_apply_coe, cartierRepExt_coe, cartierRepExt_coe, cartierRepExt_coe,
    ← wedgeMul_apply_coe, ← Submodule.coe_sub]
  refine coe_mem_exactLogForms_of_twist_mem_exactForms p hP hb hu₁ hu₂ hcoord hF hFL _ ?_ ?_
    (twist_cartierRep_wedgeMul_sub_mem_exactForms p hb i j y y')
  · rw [Submodule.coe_sub]
    refine sub_mem (coe_cartierRep_mem_logForms p hP hb hu₁ hu₂ hcoord _ ?_) ?_
    · rw [wedgeMul_apply_coe]
      exact mul_mem_logForms hω hη
    · rw [wedgeMul_apply_coe]
      exact mul_mem_logForms (coe_cartierRep_mem_logForms p hP hb hu₁ hu₂ hcoord y hω)
        (coe_cartierRep_mem_logForms p hP hb hu₁ hu₂ hcoord y' hη)
  · rw [map_sub, deRhamDifferential_cartierRep, zero_sub, neg_eq_zero]
    refine Subtype.ext ?_
    rw [coe_deRhamDifferential_wedgeMul, deRhamDifferential_cartierRep,
      deRhamDifferential_cartierRep]
    simp

/-- **The Cartier representative fixes `dlog uₖ` modulo exact logarithmic forms.** -/
theorem cartierRepExt_dlog_sub_mem_exactLogForms (hF : IsFrobeniusCoordinates p B x)
    (hFL : IsFrobeniusCoordinates p L (fun j ↦ algebraMap B L (x j))) (k : ι) :
    cartierRepExt p (fun j ↦ algebraMap B L (x j)) bL 1 (ExteriorAlgebra.ι L
        (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k)))) -
      ExteriorAlgebra.ι L (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k))) ∈
        exactLogForms A L u 1 := by
  obtain ⟨j₀, hj₀, hk⟩ := hu₁ k
  set a := algebraMap B L (u k) with ha
  have hunit : IsUnit a := by
    rw [ha, ← hk]
    exact hP j₀ hj₀
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
  have hscal : Ring.inverse a ^ p * a ^ (p - 1) = Ring.inverse a := by
    rw [hq, Nat.add_sub_cancel, pow_succ', mul_assoc, ← mul_pow,
      Ring.inverse_mul_cancel _ hunit, one_pow, mul_one]
  have hdlog : ((ιMulti L 1 fun _ ↦ Ring.inverse a • D A L a : ⋀[L]^1 (Ω[L⁄A])) :
      ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u 1 := by
    rw [exteriorPower.ιMulti_apply_coe]
    exact ιMulti_mem_logForms _ fun _ ↦ dlog_mem_logGenerators u k
  have heq : cartierRep p A (fun j ↦ algebraMap B L (x j)) bL 1
        (ιMulti L 1 fun _ ↦ Ring.inverse a • D A L a) -
      (ιMulti L 1 fun _ ↦ Ring.inverse a • D A L a) =
      Ring.inverse a ^ p • (cartierRep p A (fun j ↦ algebraMap B L (x j)) bL 1
        (ιMulti L 1 fun _ ↦ D A L a) - a ^ (p - 1) • ιMulti L 1 fun _ ↦ D A L a) := by
    rw [ιMulti_one_smul, cartierRep_smul, smul_sub, smul_smul, hscal]
  rw [← coe_ιMulti_one, cartierRepExt_coe, ← Submodule.coe_sub]
  refine coe_mem_exactLogForms_of_twist_mem_exactForms p hP hb hu₁ hu₂ hcoord hF hFL _ ?_ ?_ ?_
  · rw [Submodule.coe_sub]
    exact sub_mem (coe_cartierRep_mem_logForms p hP hb hu₁ hu₂ hcoord _ hdlog) hdlog
  · rw [heq, deRhamDifferential_pow_smul, map_sub, deRhamDifferential_cartierRep,
      deRhamDifferential_pow_pred_smul_D, sub_zero, smul_zero]
  · rw [heq]
    exact twist_smul_mem_exactForms p _ (twist_cartierRep_one_sub_mem_exactForms p hb a)

/-- **The logarithmic inverse Cartier isomorphism in coordinates.**

Let `x₁, …, xₙ` be Frobenius coordinates of `B` over `A`, let `B → L` be a map such that the
`dxⱼ` form a basis of `Ω[L⁄A]` in which every `db`, `b ∈ B`, has coordinates in `B`, let the
`xⱼ`, `j ∈ P`, be units of `L`, and suppose the `xⱼ` are Frobenius coordinates of `L` as well.
For poles `uₖ` running over the `xⱼ`, `j ∈ P`, the Cartier representative `C` is, on the
logarithmic forms, a Frobenius-semilinear and multiplicative map into the closed logarithmic
forms modulo the exact logarithmic forms, with `C(db) = b^{p-1} db` and `C(dlog uₖ) = dlog uₖ`,
and it is bijective onto the cohomology of the logarithmic de Rham complex. -/
theorem exists_logInverseCartier_of_isFrobeniusCoordinates (hF : IsFrobeniusCoordinates p B x)
    (hFL : IsFrobeniusCoordinates p L (fun j ↦ algebraMap B L (x j))) :
    ∃ C : ℕ → ExteriorAlgebra L (Ω[L⁄A]) → ExteriorAlgebra L (Ω[L⁄A]),
      (∀ i, ∀ ω ∈ logForms A L u i, C i ω ∈ closedLogForms A L u i) ∧
      (∀ i, ∀ ω ∈ logForms A L u i, ∀ η ∈ logForms A L u i,
        C i (ω + η) - (C i ω + C i η) ∈ exactLogForms A L u i) ∧
      (∀ i (b : B), ∀ ω ∈ logForms A L u i, C i (b • ω) - b ^ p • C i ω ∈ exactLogForms A L u i) ∧
      (∀ i j, ∀ ω ∈ logForms A L u i, ∀ η ∈ logForms A L u j,
        C (i + j) (ω * η) - C i ω * C j η ∈ exactLogForms A L u (i + j)) ∧
      C 0 1 = 1 ∧
      (∀ b : B, C 1 (ExteriorAlgebra.ι L (D A L (algebraMap B L b))) -
        ExteriorAlgebra.ι L (algebraMap B L b ^ (p - 1) • D A L (algebraMap B L b)) ∈
          exactLogForms A L u 1) ∧
      (∀ k : ι, C 1 (ExteriorAlgebra.ι L
          (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k)))) -
        ExteriorAlgebra.ι L (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k))) ∈
          exactLogForms A L u 1) ∧
      (∀ i, ∀ ω ∈ logForms A L u i, C i ω ∈ exactLogForms A L u i → ω = 0) ∧
      (∀ i, ∀ z ∈ closedLogForms A L u i, ∃ ω ∈ logForms A L u i,
        z - C i ω ∈ exactLogForms A L u i) := by
  set t : Fin n → L := fun j ↦ algebraMap B L (x j)
  have hlift : ∀ i ω, ω ∈ logForms A L u i →
      ∃ y : ⋀[L]^i (Ω[L⁄A]), (y : ExteriorAlgebra L (Ω[L⁄A])) = ω :=
    fun i ω hω ↦ ⟨⟨ω, logForms_le u i hω⟩, rfl⟩
  have hrep : ∀ i (y : ⋀[L]^i (Ω[L⁄A])), (y : ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u i →
      ((cartierRep p A t bL i y : ⋀[L]^i (Ω[L⁄A])) : ExteriorAlgebra L (Ω[L⁄A])) ∈
        logForms A L u i :=
    fun i y hy ↦ coe_cartierRep_mem_logForms p hP hb hu₁ hu₂ hcoord y hy
  have hgen : ∀ c : B, ((ιMulti L 1 fun _ ↦ D A L (algebraMap B L c) : ⋀[L]^1 (Ω[L⁄A])) :
      ExteriorAlgebra L (Ω[L⁄A])) ∈ logForms A L u 1 := fun c ↦ by
    rw [exteriorPower.ιMulti_apply_coe]
    exact ιMulti_mem_logForms _ fun _ ↦ D_mem_logGenerators u c
  refine ⟨cartierRepExt p t bL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro i _ hω
    obtain ⟨y, rfl⟩ := hlift i _ hω
    rw [cartierRepExt_coe]
    exact ⟨hrep _ y hω, _, rfl, deRhamDifferential_cartierRep p i y⟩
  · rintro i _ hω _ hη
    obtain ⟨y, rfl⟩ := hlift i _ hω
    obtain ⟨y', rfl⟩ := hlift i _ hη
    rw [← Submodule.coe_add, cartierRepExt_coe, cartierRepExt_coe, cartierRepExt_coe,
      cartierRep_add, Submodule.coe_add, sub_self]
    exact zero_mem_exactLogForms u i
  · rintro i b _ hω
    obtain ⟨y, rfl⟩ := hlift i _ hω
    rw [← Submodule.coe_smul_of_tower, cartierRepExt_coe, cartierRepExt_coe,
      ← algebraMap_smul L b y, cartierRep_smul, Submodule.coe_smul, ← map_pow, algebraMap_smul,
      sub_self]
    exact zero_mem_exactLogForms u i
  · exact fun i j _ hω _ hη ↦
      cartierRepExt_mul_sub_mem_exactLogForms p hP hb hu₁ hu₂ hcoord hF hFL hω hη
  · have s : Set.powersetCard (Fin n) 0 :=
      Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb (Nat.zero_le n))
    calc cartierRepExt p t bL 0 1 =
        cartierRepExt p t bL 0 ((bL.exteriorPower 0 s : ⋀[L]^0 (Ω[L⁄A])) :
          ExteriorAlgebra L (Ω[L⁄A])) := by
          rw [exteriorPower_basis_eq hb, exteriorPower.ιMulti_apply_coe,
            ExteriorAlgebra.ιMulti_zero_apply]
      _ = 1 := by
          rw [cartierRepExt_coe, cartierRep_basis, cartierBasisForm,
            exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]
  · intro c
    rw [← coe_ιMulti_one, ← coe_ιMulti_one, ιMulti_one_smul, cartierRepExt_coe,
      ← Submodule.coe_sub]
    refine coe_mem_exactLogForms_of_twist_mem_exactForms p hP hb hu₁ hu₂ hcoord hF hFL _ ?_ ?_
      (twist_cartierRep_one_sub_mem_exactForms p hb _)
    · rw [Submodule.coe_sub, Submodule.coe_smul, ← map_pow, algebraMap_smul]
      exact sub_mem (hrep _ _ (hgen c)) (Submodule.smul_mem _ _ (hgen c))
    · rw [map_sub, deRhamDifferential_cartierRep, deRhamDifferential_pow_pred_smul_D, sub_zero]
  · exact cartierRepExt_dlog_sub_mem_exactLogForms p hP hb hu₁ hu₂ hcoord hF hFL
  · rintro i _ hω hC
    obtain ⟨y, rfl⟩ := hlift i _ hω
    rw [cartierRepExt_coe] at hC
    have h0 : inverseCartier p A L i y = 0 := by
      rw [inverseCartier_eq_cohomologyMk_cartierRep p hb, cohomologyMk_eq_zero_iff]
      exact twist_mem_exactForms_of_coe_mem_exactLogForms p _ hC
    rw [(inverseCartier_bijective_of_isFrobeniusCoordinates p hb hFL i).1
      (h0.trans (map_zero _).symm), Submodule.coe_zero]
  · rintro i _ ⟨hz, y, rfl, hcl⟩
    obtain ⟨-, -, hdiff⟩ := projList_mem_logForms_of_closed (p := p) hP hb hu₁ hcoord
      (List.finRange n) i y hz hcl
    obtain ⟨ω, hω, hπ⟩ :=
      exists_projList_eq_cartierRep_of_mem_logForms hP hb hu₁ hu₂ hcoord hF y hz
    refine ⟨ω, hω, ?_⟩
    rw [cartierRepExt_coe, ← hπ, ← Submodule.coe_sub]
    exact hdiff

end Main

/-! ### Inverting a product of coordinates -/

section Away

variable (p : ℕ) [hp : Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [CharP B p] {n : ℕ} {x : Fin n → B}

omit hp [CharP B p] in
/-- The image in `L` of `∑_α c_α^p x^α` is `∑_α c_α^p x^α` in the images of the `xⱼ`. -/
theorem algebraMap_sum_pow_mul_monomial (L : Type u) [CommRing L] [Algebra B L]
    (c : (Fin n → Fin p) → B) :
    algebraMap B L (∑ α, c α ^ p * monomial x (fun j ↦ (α j : ℕ))) =
      ∑ α, algebraMap B L (c α) ^ p *
        monomial (fun j ↦ algebraMap B L (x j)) (fun j ↦ (α j : ℕ)) := by
  simp only [map_sum, map_mul, map_pow, algebraMap_monomial]

omit [CharP B p] in
/-- The Frobenius sum in the images of Frobenius coordinates is injective on `B[1/f]`. -/
theorem frobeniusSum_injective_of_isLocalization_away (f : B) (L : Type u) [CommRing L]
    [Algebra B L] [IsLocalization.Away f L] [CharP L p] (hF : IsFrobeniusCoordinates p B x) :
    Function.Injective fun c : (Fin n → Fin p) → L ↦
      ∑ α, c α ^ p * monomial (fun j ↦ algebraMap B L (x j)) (fun j ↦ (α j : ℕ)) := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.pos; omega⟩
  have hu : IsUnit (algebraMap B L f) := IsLocalization.Away.algebraMap_isUnit f
  intro d₁ d₂ h
  set e := d₁ - d₂
  have he : ∑ α, e α ^ p * monomial (fun j ↦ algebraMap B L (x j)) (fun j ↦ (α j : ℕ)) = 0 := by
    have h' : ∑ α, d₁ α ^ p * monomial (fun j ↦ algebraMap B L (x j)) (fun j ↦ (α j : ℕ)) -
        ∑ α, d₂ α ^ p * monomial (fun j ↦ algebraMap B L (x j)) (fun j ↦ (α j : ℕ)) = 0 :=
      sub_eq_zero.2 h
    rw [← h', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    simp only [e, Pi.sub_apply, sub_pow_char, sub_mul]
  suffices e = 0 from sub_eq_zero.1 this
  obtain ⟨⟨_, m, rfl⟩, hb⟩ :=
    IsLocalization.exist_integer_multiples (Submonoid.powers f) Finset.univ e
  choose a ha using fun α ↦ hb α (Finset.mem_univ α)
  have ha' : ∀ α, algebraMap B L (a α) = algebraMap B L (f ^ m) * e α := fun α ↦ by
    rw [ha α, Algebra.smul_def]
  have hzero : algebraMap B L (∑ α, a α ^ p * monomial x (fun j ↦ (α j : ℕ))) = 0 := by
    rw [algebraMap_sum_pow_mul_monomial]
    simp only [ha', mul_pow, mul_assoc, ← Finset.mul_sum, he, mul_zero]
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) L _).1 hzero
  have hsum : (fun c : (Fin n → Fin p) → B ↦ ∑ α, c α ^ p * monomial x (fun j ↦ (α j : ℕ)))
      (fun α ↦ f ^ N * a α) =
      (fun c : (Fin n → Fin p) → B ↦ ∑ α, c α ^ p * monomial x (fun j ↦ (α j : ℕ))) 0 := by
    simp only [Pi.zero_apply, zero_pow hp.out.ne_zero, zero_mul, Finset.sum_const_zero]
    have h2 : ∑ α, (f ^ N * a α) ^ p * monomial x (fun j ↦ (α j : ℕ)) =
        (f ^ N) ^ q * (f ^ N * ∑ α, a α ^ p * monomial x (fun j ↦ (α j : ℕ))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ ↦ ?_
      rw [mul_pow, show (f ^ N) ^ p = (f ^ N) ^ q * f ^ N by rw [hq, pow_succ]]
      ring
    change f ^ N * _ = 0 at hN
    rw [h2, hN, mul_zero]
  funext α
  have h3 := congrFun (hF.1 hsum) α
  simp only [Pi.zero_apply] at h3
  have h4 : algebraMap B L (a α) = 0 := by
    have := congrArg (algebraMap B L) h3
    rw [map_mul, map_zero, map_pow] at this
    exact (hu.pow N).mul_right_eq_zero.1 this
  rw [ha', map_pow] at h4
  exact (hu.pow m).mul_right_eq_zero.1 h4

omit [CharP B p] in
/-- The Frobenius sum in the images of Frobenius coordinates is surjective on `B[1/f]`. -/
theorem frobeniusSum_surjective_of_isLocalization_away (f : B) (L : Type u) [CommRing L]
    [Algebra B L] [IsLocalization.Away f L] [CharP L p] (hF : IsFrobeniusCoordinates p B x) :
    Function.Surjective fun c : (Fin n → Fin p) → L ↦
      ∑ α, c α ^ p * monomial (fun j ↦ algebraMap B L (x j)) (fun j ↦ (α j : ℕ)) := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.pos; omega⟩
  have hu : IsUnit (algebraMap B L f) := IsLocalization.Away.algebraMap_isUnit f
  set v := Ring.inverse (algebraMap B L f)
  have hv : algebraMap B L f * v = 1 := Ring.mul_inverse_cancel _ hu
  intro y
  obtain ⟨⟨a, _, m, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) y
  obtain ⟨c, hc⟩ := hF.2 (a * f ^ (q * m))
  refine ⟨fun α ↦ algebraMap B L (c α) * v ^ m, ?_⟩
  have hy : y = algebraMap B L a * v ^ m := by
    change y * algebraMap B L (f ^ m) = algebraMap B L a at h
    calc y = y * (algebraMap B L f * v) ^ m := by rw [hv, one_pow, mul_one]
      _ = _ := by rw [mul_pow, ← mul_assoc, ← map_pow, h]
  have hcL := congrArg (algebraMap B L) hc
  rw [algebraMap_sum_pow_mul_monomial] at hcL
  rw [hy]
  calc ∑ α, (algebraMap B L (c α) * v ^ m) ^ p *
        monomial (fun j ↦ algebraMap B L (x j)) (fun j ↦ (α j : ℕ)) =
      (∑ α, algebraMap B L (c α) ^ p *
        monomial (fun j ↦ algebraMap B L (x j)) (fun j ↦ (α j : ℕ))) * v ^ (p * m) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun α _ ↦ ?_
        ring
    _ = algebraMap B L (a * f ^ (q * m)) * v ^ (p * m) := by rw [hcL]
    _ = algebraMap B L a * v ^ m * (algebraMap B L f * v) ^ (q * m) := by
        rw [map_mul, map_pow, hq]
        ring
    _ = algebraMap B L a * v ^ m := by rw [hv, one_pow, mul_one]

omit [CharP B p] in
/-- **Frobenius coordinates survive inverting an element.** -/
theorem isFrobeniusCoordinates_of_isLocalization_away (f : B) (L : Type u) [CommRing L]
    [Algebra B L] [IsLocalization.Away f L] [CharP L p] (hF : IsFrobeniusCoordinates p B x) :
    IsFrobeniusCoordinates p L (fun j ↦ algebraMap B L (x j)) :=
  ⟨frobeniusSum_injective_of_isLocalization_away p f L hF,
    frobeniusSum_surjective_of_isLocalization_away p f L hF⟩

/-- **The logarithmic inverse Cartier isomorphism for `B[1/∏_{j ∈ P} xⱼ]`.**

Let `A → B` be a map of rings of characteristic `p` such that `dx₁, …, dxₙ` is a basis of
`Ω[B⁄A]` and `x₁, …, xₙ` are Frobenius coordinates of `B` (for instance `B = A[x₁, …, xₙ]` with
`A` perfect), and let `L = B[1/∏_{j ∈ P} xⱼ]`. For poles `uₖ` running over the `xⱼ`, `j ∈ P`,
the inverse Cartier map is a well-defined, Frobenius-semilinear, multiplicative map from the
logarithmic forms to the cohomology of the logarithmic de Rham complex, with `C⁻¹(db) =
[b^{p-1} db]` and `C⁻¹(dlog uₖ) = [dlog uₖ]`, and it is bijective. -/
theorem exists_logInverseCartier_of_isLocalization_away (bB : Module.Basis (Fin n) B (Ω[B⁄A]))
    (hb : ∀ j, bB j = D A B (x j)) (hF : IsFrobeniusCoordinates p B x) (P : Finset (Fin n))
    {ι : Type*} (u : ι → B) (hu₁ : ∀ k, ∃ j ∈ P, x j = u k) (hu₂ : ∀ j ∈ P, ∃ k, u k = x j)
    (L : Type u) [CommRing L] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    [IsLocalization.Away (∏ j ∈ P, x j) L] :
    ∃ C : ℕ → ExteriorAlgebra L (Ω[L⁄A]) → ExteriorAlgebra L (Ω[L⁄A]),
      (∀ i, ∀ ω ∈ logForms A L u i, C i ω ∈ closedLogForms A L u i) ∧
      (∀ i, ∀ ω ∈ logForms A L u i, ∀ η ∈ logForms A L u i,
        C i (ω + η) - (C i ω + C i η) ∈ exactLogForms A L u i) ∧
      (∀ i (b : B), ∀ ω ∈ logForms A L u i, C i (b • ω) - b ^ p • C i ω ∈ exactLogForms A L u i) ∧
      (∀ i j, ∀ ω ∈ logForms A L u i, ∀ η ∈ logForms A L u j,
        C (i + j) (ω * η) - C i ω * C j η ∈ exactLogForms A L u (i + j)) ∧
      C 0 1 = 1 ∧
      (∀ b : B, C 1 (ExteriorAlgebra.ι L (D A L (algebraMap B L b))) -
        ExteriorAlgebra.ι L (algebraMap B L b ^ (p - 1) • D A L (algebraMap B L b)) ∈
          exactLogForms A L u 1) ∧
      (∀ k : ι, C 1 (ExteriorAlgebra.ι L
          (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k)))) -
        ExteriorAlgebra.ι L (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k))) ∈
          exactLogForms A L u 1) ∧
      (∀ i, ∀ ω ∈ logForms A L u i, C i ω ∈ exactLogForms A L u i → ω = 0) ∧
      (∀ i, ∀ z ∈ closedLogForms A L u i, ∃ ω ∈ logForms A L u i,
        z - C i ω ∈ exactLogForms A L u i) := by
  rcases subsingleton_or_nontrivial L with hL | hL
  · have : Subsingleton (ExteriorAlgebra L (Ω[L⁄A])) := ⟨fun a b ↦ by
      rw [← one_smul L a, ← one_smul L b, Subsingleton.elim (1 : L) 0, zero_smul, zero_smul]⟩
    have h0 : ∀ i ω, ω ∈ exactLogForms A L u i := fun i ω ↦ Or.inl (Subsingleton.elim _ _)
    refine ⟨fun _ _ ↦ 0, fun _ _ _ ↦ ⟨zero_mem _, 0, Submodule.coe_zero, map_zero _⟩,
      fun _ _ _ _ _ ↦ h0 _ _, fun _ _ _ _ ↦ h0 _ _, fun _ _ _ _ _ _ ↦ h0 _ _,
      Subsingleton.elim _ _, fun _ ↦ h0 _ _, fun _ ↦ h0 _ _,
      fun _ _ _ _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ ⟨0, zero_mem _, h0 _ _⟩⟩
  · have : CharP L p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (algebraMap B L), CharP.cast_eq_zero, map_zero])
    set f := ∏ j ∈ P, x j
    let bL := bB.ofIsLocalizedModule L (Submonoid.powers f) (KaehlerDifferential.map A A B L)
    have hbL : ∀ j, bL j = D A L (algebraMap B L (x j)) := fun j ↦ by
      rw [Module.Basis.ofIsLocalizedModule_apply, hb, KaehlerDifferential.map_D A A B L]
    have hcoord : ∀ (b : B) j, bL.repr (D A L (algebraMap B L b)) j ∈
        Set.range (algebraMap B L) := fun b j ↦
      ⟨bB.repr (D A B b) j, by
        rw [← KaehlerDifferential.map_D A A B L, Module.Basis.ofIsLocalizedModule_repr_apply]⟩
    have hP : ∀ j ∈ P, IsUnit (algebraMap B L (x j)) := fun j hj ↦
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ hj))
        (IsLocalization.Away.algebraMap_isUnit f)
    exact exists_logInverseCartier_of_isFrobeniusCoordinates p hP hbL hu₁ hu₂ hcoord hF
      (isFrobeniusCoordinates_of_isLocalization_away p f L hF)

/-- **The logarithmic inverse Cartier isomorphism for `B[1/(x₁ ⋯ x_r)]`**, with poles along the
first `r` coordinates: the case `P = {1, …, r}` of
`MMP.DeRham.exists_logInverseCartier_of_isLocalization_away`. -/
theorem exists_logInverseCartier_of_isLocalization_away_castLE
    (bB : Module.Basis (Fin n) B (Ω[B⁄A])) (hb : ∀ j, bB j = D A B (x j))
    (hF : IsFrobeniusCoordinates p B x) {r : ℕ} (hr : r ≤ n)
    (L : Type u) [CommRing L] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    [hL : IsLocalization.Away (∏ k : Fin r, x (Fin.castLE hr k)) L] :
    let ι := Fin r
    let u : Fin r → B := fun k ↦ x (Fin.castLE hr k)
    ∃ C : ℕ → ExteriorAlgebra L (Ω[L⁄A]) → ExteriorAlgebra L (Ω[L⁄A]),
      (∀ i, ∀ ω ∈ logForms A L u i, C i ω ∈ closedLogForms A L u i) ∧
      (∀ i, ∀ ω ∈ logForms A L u i, ∀ η ∈ logForms A L u i,
        C i (ω + η) - (C i ω + C i η) ∈ exactLogForms A L u i) ∧
      (∀ i (b : B), ∀ ω ∈ logForms A L u i, C i (b • ω) - b ^ p • C i ω ∈ exactLogForms A L u i) ∧
      (∀ i j, ∀ ω ∈ logForms A L u i, ∀ η ∈ logForms A L u j,
        C (i + j) (ω * η) - C i ω * C j η ∈ exactLogForms A L u (i + j)) ∧
      C 0 1 = 1 ∧
      (∀ b : B, C 1 (ExteriorAlgebra.ι L (D A L (algebraMap B L b))) -
        ExteriorAlgebra.ι L (algebraMap B L b ^ (p - 1) • D A L (algebraMap B L b)) ∈
          exactLogForms A L u 1) ∧
      (∀ k : ι, C 1 (ExteriorAlgebra.ι L
          (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k)))) -
        ExteriorAlgebra.ι L (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k))) ∈
          exactLogForms A L u 1) ∧
      (∀ i, ∀ ω ∈ logForms A L u i, C i ω ∈ exactLogForms A L u i → ω = 0) ∧
      (∀ i, ∀ z ∈ closedLogForms A L u i, ∃ ω ∈ logForms A L u i,
        z - C i ω ∈ exactLogForms A L u i) := by
  intro ι u
  let P : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hr)
  have e : ∏ j ∈ P, x j = ∏ k : Fin r, x (Fin.castLE hr k) := by
    simp [P, Finset.prod_map]
  have : IsLocalization.Away (∏ j ∈ P, x j) L := e ▸ hL
  refine exists_logInverseCartier_of_isLocalization_away p bB hb hF P u
    (fun k ↦ ⟨Fin.castLE hr k, Finset.mem_map_of_mem _ (Finset.mem_univ k), rfl⟩)
    (fun j hj ↦ ?_) L
  obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hj
  exact ⟨k, rfl⟩

/-- **The logarithmic inverse Cartier isomorphism for `A[x₁, …, xₙ][1/(x₁ ⋯ x_r)]`** over a
perfect ring `A` of characteristic `p`. -/
theorem exists_logInverseCartier_mvPolynomial [CharP A p] [PerfectRing A p] {r : ℕ} (hr : r ≤ n)
    (L : Type u) [CommRing L] [Algebra A L] [Algebra (MvPolynomial (Fin n) A) L]
    [IsScalarTower A (MvPolynomial (Fin n) A) L]
    [IsLocalization.Away (∏ k : Fin r, (MvPolynomial.X (Fin.castLE hr k) :
      MvPolynomial (Fin n) A)) L] :
    let ι := Fin r
    let B := MvPolynomial (Fin n) A
    let u : Fin r → B := fun k ↦ MvPolynomial.X (Fin.castLE hr k)
    ∃ C : ℕ → ExteriorAlgebra L (Ω[L⁄A]) → ExteriorAlgebra L (Ω[L⁄A]),
      (∀ i, ∀ ω ∈ logForms A L u i, C i ω ∈ closedLogForms A L u i) ∧
      (∀ i, ∀ ω ∈ logForms A L u i, ∀ η ∈ logForms A L u i,
        C i (ω + η) - (C i ω + C i η) ∈ exactLogForms A L u i) ∧
      (∀ i (b : B), ∀ ω ∈ logForms A L u i, C i (b • ω) - b ^ p • C i ω ∈ exactLogForms A L u i) ∧
      (∀ i j, ∀ ω ∈ logForms A L u i, ∀ η ∈ logForms A L u j,
        C (i + j) (ω * η) - C i ω * C j η ∈ exactLogForms A L u (i + j)) ∧
      C 0 1 = 1 ∧
      (∀ b : B, C 1 (ExteriorAlgebra.ι L (D A L (algebraMap B L b))) -
        ExteriorAlgebra.ι L (algebraMap B L b ^ (p - 1) • D A L (algebraMap B L b)) ∈
          exactLogForms A L u 1) ∧
      (∀ k : ι, C 1 (ExteriorAlgebra.ι L
          (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k)))) -
        ExteriorAlgebra.ι L (Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k))) ∈
          exactLogForms A L u 1) ∧
      (∀ i, ∀ ω ∈ logForms A L u i, C i ω ∈ exactLogForms A L u i → ω = 0) ∧
      (∀ i, ∀ z ∈ closedLogForms A L u i, ∃ ω ∈ logForms A L u i,
        z - C i ω ∈ exactLogForms A L u i) :=
  exists_logInverseCartier_of_isLocalization_away_castLE p (mvPolynomialBasis A (Fin n))
    (mvPolynomialBasis_eq_D A) (isFrobeniusCoordinates_mvPolynomial p A) hr L

end Away

end MMP.DeRham

end
