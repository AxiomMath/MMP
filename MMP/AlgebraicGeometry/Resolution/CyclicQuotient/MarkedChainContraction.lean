module

public import MMP.AlgebraicGeometry.Resolution.CyclicQuotient.ChainPlumbing
public import MMP.AlgebraicGeometry.Resolution.CyclicQuotient.MarkedChainFormalRigidity

/-!
# Contracting a doubly marked negative chain gives a cyclic quotient

Let `K` be algebraically closed of characteristic `0` and let `f : X ⟶ Y` be a proper morphism
from a smooth surface to a normal surface with `f_* 𝒪_X = 𝒪_Y`. Let `y ∈ Y` be a closed point
whose reduced fibre is a chain `E = E₁ + ⋯ + E_r` of smooth rational curves with simple normal
crossings, `Eᵢ² = -bᵢ` and every `bᵢ ≥ 2`, and mark its two ends by smooth formal curve germs
`Z_L`, `Z_R` transverse to `E₁`, resp. `E_r`, away from the other components and at distinct
points. By the theorem on formal functions, `𝒪̂_{Y,y}` is the ring of formal functions on `X`
along `E`; write `I_Z ⊆ 𝒪̂_{Y,y}` for the ideal of those vanishing on the marking `Z`. Then
`𝒪̂_{Y,y} ≅ K[[u, v]]^{μ_m}` over `K`, for the action of `μ_m` with weights `(1, q)`, some
`m ≥ 2` and `q` prime to `m`, by an isomorphism carrying `I_{Z_L}`, `I_{Z_R}` and
`I_{Z_L} ∩ I_{Z_R}` to the invariants in `(u)`, `(v)` and `(u) ∩ (v)`.

## Main results

* `MMP.Flips.exists_ringEquiv_cyclicInvariants_of_isSNCChain_fibre`: the completed local ring
  at the image of a contracted doubly marked negative chain is a cyclic quotient
  `MMP.Flips.cyclicInvariants K m q`, compatibly with the two marking ideals.

## Implementation notes

*Thickenings and formal functions.* Write `I_E = ∏ᵢ I_{Eᵢ}` and `(n+1)E` for the closed
subscheme cut out by `I_E ^ (n + 1)`. A formal function along `E` is a compatible family of
global sections of the thickenings `(n+1)E`. The comparison `𝒪̂_{Y,y} → Γ((n+1)E, 𝒪)` of the
theorem on formal functions is the unique ring map `ψ n` which on the image of a germ `s_y`,
`s ∈ 𝒪_Y(U)`, is the pullback of `s` along `(n+1)E ⟶ X ⟶ Y` (every point of `(n+1)E` lies over
`y ∈ U`); since `𝔪_y ^ (n+1)` maps into `I_E ^ (n + 1)` and every element of the stalk is a germ,
these equations determine `ψ n`.

*The markings.* As in `MMP.Mori.exists_formalPlumbingCharts_of_isSNCChain`, a smooth formal
curve germ `Ẑ` at `p` transverse to `E` is recorded by its traces `Zₙ = Ẑ ∩ (n+1)E`: closed
subschemes `Zₙ ⊆ (n+1)E` with `Zₙ = Zₙ₊₁ ∩ (n+1)E`, `Z₀ = {p}` and
`Zₙ ≅ Spec K[t]/(t^(n+1))` over `K`. A formal function vanishes on `Ẑ` exactly when it vanishes
on every trace, so `I_Z` is the set of `a ∈ 𝒪̂_{Y,y}` with `ψ n a ↦ 0` in `Γ(Zₙ, 𝒪)` for all `n`.

*The chain.* On a smooth surface, `(Eᵢ · Eᵢ₊₁) = 1` says that consecutive components meet
transversally in exactly one point; non-consecutive components are disjoint.

*The isomorphism.* `K[[u, v]]^{μ_m}` is a subring of `K[[u, v]]`, so the `K`-isomorphism is a
ring isomorphism `φ : K[[u, v]]^{μ_m} ≃+* 𝒪̂_{Y,y}` matching the constants of `K[[u, v]]` with
the image of `K → 𝒪_{Y,y} → 𝒪̂_{Y,y}`.

*The proof.* The formal rigidity of the marked chain
(`MMP.Mori.exists_formalPlumbingCharts_of_isSNCChain`) gives formal plumbing charts on the
thickenings `(n+1)E`. Reading a formal function along `E` in these charts identifies the ring of
formal functions with the compatible families of power series on the charts, which is the
cyclic quotient `K[[u, v]]^{μ_m}` (`MMP.Flips.exists_ringHom_cyclicInvariants_chainPlumbing`).
By the theorem on formal functions in degree zero
(`AlgebraicGeometry.Scheme.IdealSheafData.bijective_completionToFormalNeighborhood`) the ring of
formal functions along `E` is `𝒪̂_{Y,y}`. Under the composite the marking `x₀ = 0` of the first
chart becomes `u = 0` and the marking `y_r = 0` of the last chart becomes `v = 0`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6.3
-/

universe u v

open CategoryTheory AlgebraicGeometry IsLocalRing MMP.Mori

namespace MMP.Flips

/-! ### Formal functions on the charts of the plumbing -/

section PlumbingCharts

open MvPolynomial

section Charts

variable {K : Type v} [Field K] {X : Scheme.{v}} (sX : X ⟶ Spec (.of K)) (I : X.IdealSheafData)

/-- The trace of an open of `X` on the `(n+1)`-st thickening `(n+1)E`. -/
private noncomputable abbrev trS (n : ℕ) (V : X.Opens) : (I ^ (n + 1)).subscheme.Opens :=
  (I ^ (n + 1)).subschemeι ⁻¹ᵁ V

/-- The constants `K → Γ((n+1)E, U)`. -/
private noncomputable def σS (n : ℕ) (U : (I ^ (n + 1)).subscheme.Opens) :
    K →+* Γ((I ^ (n + 1)).subscheme, U) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U
    (by rw [Scheme.Hom.preimage_top]; exact le_top)).hom

/-- The restriction `(n+2)E → (n+1)E` on the trace of an open. -/
private noncomputable def ρS (n : ℕ) (V : X.Opens) :
    Γ((I ^ (n + 1 + 1)).subscheme, trS I (n + 1) V) →+* Γ((I ^ (n + 1)).subscheme, trS I n V) :=
  ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top (Nat.le_succ (n + 1)) :
      I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (trS I (n + 1) V) (trS I n V)
    (by simp only [trS, ← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι,
      le_refl])).hom

/-- Restriction between opens of a thickening. -/
private noncomputable def resS (n : ℕ) {U U' : (I ^ (n + 1)).subscheme.Opens} (h : U' ≤ U) :
    Γ((I ^ (n + 1)).subscheme, U) →+* Γ((I ^ (n + 1)).subscheme, U') :=
  ((I ^ (n + 1)).subscheme.presheaf.map (homOfLE h).op).hom

private theorem resS_resS (n : ℕ) {U U' U'' : (I ^ (n + 1)).subscheme.Opens} (h : U' ≤ U)
    (h' : U'' ≤ U') (s : Γ((I ^ (n + 1)).subscheme, U)) :
    resS I n h' (resS I n h s) = resS I n (h'.trans h) s := by
  simp only [resS, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem resS_σS (n : ℕ) {U U' : (I ^ (n + 1)).subscheme.Opens} (h : U' ≤ U) (c : K) :
    resS I n h (σS sX I n U c) = σS sX I n U' c := by
  simp only [resS, σS]
  rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]

private theorem ρS_resS_top (n : ℕ) (V : X.Opens) (s : Γ(I.thickening (n + 1), ⊤)) :
    ρS I n V (resS I (n + 1) le_top s) = resS I n le_top (I.thickeningRestriction n s) := by
  simp only [ρS, resS, Scheme.IdealSheafData.thickeningRestriction, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.appTop, Scheme.Hom.app, Scheme.Hom.appLE_map]
  rfl

private theorem appLE_eq_of_eq {A B : Scheme.{v}} {f g : A ⟶ B} (h : f = g)
    {U : B.Opens} {W : A.Opens} (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h
  rfl

private theorem ρS_σS (n : ℕ) (V : X.Opens) (c : K) :
    ρS I n V (σS sX I (n + 1) (trS I (n + 1) V) c) = σS sX I n (trS I n V) c := by
  simp only [ρS, σS]
  rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_comp_appLE]
  have : Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top (Nat.le_succ (n + 1)) :
      I ^ (n + 1 + 1) ≤ I ^ (n + 1)) ≫ (I ^ (n + 1 + 1)).subschemeι ≫ sX =
      (I ^ (n + 1)).subschemeι ≫ sX := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  rw [appLE_eq_of_eq this]

end Charts

section Poly

variable {K : Type*} [Field K]

/-- Membership in a power of `(X i)`: every monomial has `X i`-degree at least `n + 1`. -/
private theorem mem_span_X_pow_iff (i : Fin 2) (n : ℕ) (Q : MvPolynomial (Fin 2) K) :
    Q ∈ Ideal.span {(X i : MvPolynomial (Fin 2) K)} ^ (n + 1) ↔
      ∀ e ∈ Q.support, n + 1 ≤ e i := by
  rw [Ideal.span_singleton_pow, X_pow_eq_monomial,
    show ({monomial (Finsupp.single i (n + 1)) (1 : K)} : Set (MvPolynomial (Fin 2) K)) =
      (fun s => monomial s 1) '' {Finsupp.single i (n + 1)} by simp,
    mem_ideal_span_monomial_image]
  simp only [Set.mem_singleton_iff, exists_eq_left, Finsupp.single_le_iff]

/-- Membership in a power of `(X₀ X₁)`: every monomial has both degrees at least `n + 1`. -/
private theorem mem_span_X_mul_X_pow_iff (n : ℕ) (Q : MvPolynomial (Fin 2) K) :
    Q ∈ Ideal.span {(X 0 * X 1 : MvPolynomial (Fin 2) K)} ^ (n + 1) ↔
      ∀ e ∈ Q.support, n + 1 ≤ min (e 0) (e 1) := by
  have : (X 0 * X 1 : MvPolynomial (Fin 2) K) ^ (n + 1) =
      monomial (Finsupp.single 0 (n + 1) + Finsupp.single 1 (n + 1)) 1 := by
    rw [mul_pow, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  rw [Ideal.span_singleton_pow, this,
    show ({monomial (Finsupp.single 0 (n + 1) + Finsupp.single 1 (n + 1)) (1 : K)} :
      Set (MvPolynomial (Fin 2) K)) = (fun s => monomial s 1) ''
        {Finsupp.single 0 (n + 1) + Finsupp.single 1 (n + 1)} by simp,
    mem_ideal_span_monomial_image]
  simp only [Set.mem_singleton_iff, exists_eq_left, le_min_iff]
  refine forall₂_congr fun e _ => ⟨fun h => ⟨by simpa using h 0, by simpa using h 1⟩, ?_⟩
  rintro ⟨h0, h1⟩ i
  fin_cases i <;> simpa

/-- The coefficient of `x^a y^c` (`a, c ∈ ℤ`, zero for a negative exponent). -/
private noncomputable def coeffZ (f : MvPolynomial (Fin 2) K) (a c : ℤ) : K :=
  if 0 ≤ a ∧ 0 ≤ c then f.coeff (Finsupp.single 0 a.toNat + Finsupp.single 1 c.toNat) else 0

private theorem coeffZ_of_neg_left (f : MvPolynomial (Fin 2) K) {a : ℤ} (ha : a < 0) (c : ℤ) :
    coeffZ f a c = 0 := by
  simp [coeffZ, not_le.mpr ha]

private theorem coeffZ_of_neg_right (f : MvPolynomial (Fin 2) K) (a : ℤ) {c : ℤ} (hc : c < 0) :
    coeffZ f a c = 0 := by
  simp [coeffZ, not_le.mpr hc]

private theorem coeffZ_natCast (f : MvPolynomial (Fin 2) K) (p c : ℕ) :
    coeffZ f p c = f.coeff (Finsupp.single 0 p + Finsupp.single 1 c) := by
  simp [coeffZ]

private theorem eq_single_add_single (e : Fin 2 →₀ ℕ) :
    e = Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) := by
  ext i; fin_cases i <;> simp

/-- The coefficient of `X₀^N Q` at `(p, c)`. -/
private theorem coeff_single_add_single_X_pow_mul (Q : MvPolynomial (Fin 2) K) (N p c : ℕ) :
    (X 0 ^ N * Q).coeff (Finsupp.single 0 p + Finsupp.single 1 c) = coeffZ Q ((p : ℤ) - N) c := by
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  by_cases h : N ≤ p
  · rw [if_pos (by
      intro i; fin_cases i <;> simp [Finsupp.single_apply]; omega), one_mul]
    rw [show ((p : ℤ) - N) = ((p - N : ℕ) : ℤ) by omega, coeffZ_natCast]
    congr 1
    ext i; fin_cases i <;> simp [Finsupp.single_apply]
  · rw [if_neg (by
      intro hle; have := hle 0; simp at this; omega), coeffZ_of_neg_left _ (by omega)]

private theorem single_add_single_inj {a c a' c' : ℕ} :
    (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 c = Finsupp.single 0 a' + Finsupp.single 1 c')
      ↔ a = a' ∧ c = c' := by
  refine ⟨fun h => ⟨by simpa using congrArg (· 0) h, by simpa using congrArg (· 1) h⟩, ?_⟩
  rintro ⟨rfl, rfl⟩
  rfl

private theorem coeff_X_pow_mul_of_lt (Q : MvPolynomial (Fin 2) K) {N : ℕ} {e : Fin 2 →₀ ℕ}
    (h : e 0 < N) : (X 0 ^ N * Q).coeff e = 0 := by
  rw [eq_single_add_single e, coeff_single_add_single_X_pow_mul, coeffZ_of_neg_left _ (by omega)]

/-- A ring map out of `K[x, y]` sends `c x^a y^b` to `ev (C c) * ev x ^ a * ev y ^ b`. -/
private theorem map_monomial_fin_two {W : Type*} [CommRing W] (ev : MvPolynomial (Fin 2) K →+* W)
    (e : Fin 2 →₀ ℕ) (c : K) :
    ev (monomial e c) = ev (C c) * ev (X 0) ^ e 0 * ev (X 1) ^ e 1 := by
  rw [monomial_eq, map_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two,
    map_mul, map_pow, map_pow, mul_assoc]

/-- The polynomial `x^N Q'(x^b y, x⁻¹)`, for `N` at least the `y`-degree of `Q'`. -/
private noncomputable def transport (b N : ℕ) (Q' : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 2) K :=
  ∑ e ∈ Q'.support, monomial (Finsupp.single 0 (b * e 0 + N - e 1) + Finsupp.single 1 (e 0))
    (Q'.coeff e)

private theorem coeff_transport (b N : ℕ) (Q' : MvPolynomial (Fin 2) K)
    (hN : ∀ e ∈ Q'.support, e 1 ≤ N) (p c : ℕ) :
    (transport b N Q').coeff (Finsupp.single 0 p + Finsupp.single 1 c) =
      coeffZ Q' c ((b : ℤ) * c + N - p) := by
  classical
  rw [transport, coeff_sum]
  simp only [coeff_monomial, single_add_single_inj]
  by_cases hp : p ≤ b * c + N
  · have hcast : ((b : ℤ) * c + N - p) = ((b * c + N - p : ℕ) : ℤ) := by push_cast [hp]; ring
    rw [hcast, coeffZ_natCast]
    by_cases hmem : Finsupp.single 0 c + Finsupp.single 1 (b * c + N - p) ∈ Q'.support
    · rw [Finset.sum_eq_single (Finsupp.single 0 c + Finsupp.single 1 (b * c + N - p))]
      · rw [if_pos]
        have h1 := hN _ hmem
        simp at h1 ⊢
        omega
      · intro e he hne
        rw [if_neg]
        rintro ⟨h1, rfl⟩
        apply hne
        have := hN e he
        ext i; fin_cases i <;> simp <;> omega
      · intro h; exact absurd hmem h
    · rw [notMem_support_iff.mp hmem]
      refine Finset.sum_eq_zero fun e he => if_neg ?_
      rintro ⟨h1, rfl⟩
      apply hmem
      have := hN e he
      convert he using 1
      ext i; fin_cases i <;> simp <;> omega
  · rw [coeffZ_of_neg_right _ _ (by push_cast; omega)]
    refine Finset.sum_eq_zero fun e he => if_neg ?_
    rintro ⟨h1, rfl⟩
    have := hN e he
    omega

/-- `x^N` times the image of `Q'` under `x' ↦ x^b y`, `y' ↦ x⁻¹` is the image of
`transport b N Q'`. -/
private theorem pow_mul_map_eq_map_transport {W : Type*} [CommRing W]
    (ev ev' : MvPolynomial (Fin 2) K →+* W) (b N : ℕ) {ζ : W} (hξζ : ev (X 0) * ζ = 1)
    (hx' : ev' (X 0) = ev (X 0) ^ b * ev (X 1)) (hy' : ev' (X 1) = ζ)
    (hC : ∀ c, ev' (C c) = ev (C c)) (Q' : MvPolynomial (Fin 2) K)
    (hN : ∀ e ∈ Q'.support, e 1 ≤ N) :
    ev (X 0) ^ N * ev' Q' = ev (transport b N Q') := by
  conv_lhs => rw [Q'.as_sum]
  rw [map_sum, Finset.mul_sum, transport, map_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [map_monomial_fin_two, map_monomial_fin_two, hx', hy', hC]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply,
    one_ne_zero, if_false, zero_ne_one, add_zero, zero_add]
  have hle := hN e he
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, show b * e 0 + (e 1 + d) - e 1 = b * e 0 + d by omega, mul_pow, ← pow_mul, pow_add,
    pow_add]
  have : ev (X 0) ^ e 1 * ζ ^ e 1 = 1 := by rw [← mul_pow, hξζ, one_pow]
  linear_combination (ev (C (Q'.coeff e)) * ev (X 0) ^ d * ev (X 0) ^ (b * e 0) *
    ev (X 1) ^ e 0) * this

/-- If the coefficients of `x^a y^c` in `Q` and of `x'^c y'^(bc - a)` in `Q'` agree for `c ≤ n`,
then `x^t F` lies in the kernel of `P`, where `F = x^N Q - transport b N Q'`. -/
private theorem map_X_pow_mul_eq_zero_of_coeffZ {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin 2) K →+* R) (n t N b : ℕ)
    (hP : ∀ Q, P Q = 0 ↔ ∀ e ∈ Q.support, n + 1 ≤ e 1 ∧ t ≤ e 0) (Q Q' F : MvPolynomial (Fin 2) K)
    (hcoeff : ∀ m p c : ℕ, (X 0 ^ m * F).coeff (Finsupp.single 0 (p + m) + Finsupp.single 1 c)
      = coeffZ Q ((p : ℤ) - N) c - coeffZ Q' c ((b : ℤ) * c - ((p : ℤ) - N)))
    (h : ∀ a c : ℤ, c ≤ n → coeffZ Q a c = coeffZ Q' c (b * c - a)) :
    P (X 0 ^ t * F) = 0 := by
  rw [hP]
  intro e he
  have ht : t ≤ e 0 := by
    by_contra hlt
    exact mem_support_iff.mp he (coeff_X_pow_mul_of_lt F (by omega))
  refine ⟨?_, ht⟩
  by_contra hlt
  obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le ht
  apply mem_support_iff.mp he
  rw [eq_single_add_single e, hp, add_comm t p, hcoeff t p (e 1),
    h _ _ (by push_cast; omega), sub_self]

/-- **Agreement on the overlap of two consecutive plumbing charts.** Let `P`, `P'` present the
two charts by `K[x, y]`, the first with kernel the monomials of `y`-degree `> n` (and `x`-degree
`≥ t`), let `α`, `β` be the restrictions to the overlap, `α` inverting `x`, with `y' = x⁻¹` and
`x' = x^b y` there. Then the classes of `Q` and `Q'` agree on the overlap exactly when the
coefficients of `x^a y^c` in `Q` and of `x'^c y'^(bc - a)` in `Q'` agree for every `c ≤ n`. -/
private theorem map_eq_map_iff_coeffZ {R R' W : Type*} [CommRing R] [CommRing R'] [CommRing W]
    (P : MvPolynomial (Fin 2) K →+* R) (P' : MvPolynomial (Fin 2) K →+* R')
    (n t : ℕ) (hP : ∀ Q, P Q = 0 ↔ ∀ e ∈ Q.support, n + 1 ≤ e 1 ∧ t ≤ e 0)
    (α : R →+* W) (hα : ∀ z, α z = 0 → ∃ m : ℕ, P (X 0) ^ m * z = 0)
    (β : R' →+* W) (b : ℕ)
    (h1 : α (P (X 0)) * β (P' (X 1)) = 1)
    (h2 : β (P' (X 0)) = α (P (X 0)) ^ b * α (P (X 1)))
    (hC : ∀ c : K, β (P' (C c)) = α (P (C c))) (Q Q' : MvPolynomial (Fin 2) K) :
    α (P Q) = β (P' Q') ↔ ∀ a c : ℤ, c ≤ n → coeffZ Q a c = coeffZ Q' c (b * c - a) := by
  set N := Q'.support.sup (fun e => e 1)
  have hN : ∀ e ∈ Q'.support, e 1 ≤ N := fun e he => Finset.le_sup (f := fun e => e 1) he
  have hA := pow_mul_map_eq_map_transport (α.comp P) (β.comp P') b N h1 h2 rfl hC Q' hN
  simp only [RingHom.comp_apply] at hA
  have hξ : IsUnit (α (P (X 0))) := IsUnit.of_mul_eq_one _ h1
  set F := X 0 ^ N * Q - transport b N Q' with hF
  have key : α (P Q) = β (P' Q') ↔ α (P F) = 0 := by
    rw [hF, map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, ← hA, ← mul_sub,
      (hξ.pow N).mul_right_eq_zero, sub_eq_zero]
  have hcoeff : ∀ (m p c : ℕ), (X 0 ^ m * F).coeff (Finsupp.single 0 (p + m) + Finsupp.single 1 c)
      = coeffZ Q ((p : ℤ) - N) c - coeffZ Q' c ((b : ℤ) * c - ((p : ℤ) - N)) := by
    intro m p c
    rw [coeff_single_add_single_X_pow_mul,
      show ((p + m : ℕ) : ℤ) - m = ((p : ℕ) : ℤ) by push_cast; ring,
      coeffZ_natCast, hF, coeff_sub, coeff_single_add_single_X_pow_mul, coeff_transport b N Q' hN]
    congr 2; ring
  rw [key]
  constructor
  · intro h0 a c hc
    obtain ⟨m, hm⟩ := hα _ h0
    rw [← map_pow, ← map_mul, hP] at hm
    rcases lt_or_ge c 0 with hc0 | hc0
    · rw [coeffZ_of_neg_right _ _ hc0, coeffZ_of_neg_left _ hc0]
    lift c to ℕ using hc0
    rcases lt_or_ge (a + N) 0 with ha | ha
    · rw [coeffZ_of_neg_left _ (by omega)]
      unfold coeffZ
      split_ifs with h
      · have hnm : Finsupp.single 0 (c : ℤ).toNat + Finsupp.single 1 ((b : ℤ) * c - a).toNat ∉
          Q'.support :=
          fun hmem => by
            have h2 := hN _ hmem
            simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, one_ne_zero,
              if_false, if_true, zero_add] at h2
            have h3 := Int.self_le_toNat ((b : ℤ) * c - a)
            have h4 : (0 : ℤ) ≤ (b : ℤ) * c := by positivity
            omega
        rw [notMem_support_iff.mp hnm]
      · rfl
    · lift (a + N) to ℕ using ha with p hp
      have hz := hcoeff m p c
      have hmem : Finsupp.single 0 (p + m) + Finsupp.single 1 c ∉ (X 0 ^ m * F).support :=
        fun hmem => by
          have := (hm _ hmem).1
          simp at this
          omega
      rw [notMem_support_iff.mp hmem, show (p : ℤ) - N = a by omega] at hz
      exact sub_eq_zero.mp hz.symm
  · intro h
    exact (hξ.pow t).mul_right_eq_zero.mp (by
      simpa only [map_mul, map_pow, map_zero] using
        congrArg α (map_X_pow_mul_eq_zero_of_coeffZ P n t N b hP Q Q' F hcoeff h))

end Poly

section Plumbing

variable {K : Type v} [Field K]

/-- The order of a monomial along the exceptional ideal of chart `j`: `y`-degree on the first
chart, `x`-degree on the last, the smaller of the two in between. -/
private def ordc (r : ℕ) (j : Fin (r + 1)) (e : Fin 2 →₀ ℕ) : ℕ :=
  if (j : ℕ) = 0 then e 1 else if (j : ℕ) = r then e 0 else min (e 0) (e 1)

private theorem ordc_mono (r : ℕ) (j : Fin (r + 1)) {e e' : Fin 2 →₀ ℕ} (h : e ≤ e') :
    ordc r j e ≤ ordc r j e' := by
  have h0 := h 0
  have h1 := h 1
  unfold ordc
  split_ifs <;> omega

/-- The exceptional ideal of chart `j`: `(y)`, `(x)` or `(x y)`. -/
private noncomputable def chartIdeal (r : ℕ) (j : Fin (r + 1)) : Ideal (MvPolynomial (Fin 2) K) :=
  if j = 0 then Ideal.span {X 1} else if j = Fin.last r then Ideal.span {X 0}
    else Ideal.span {X 0 * X 1}

private theorem mem_chartIdeal_pow_iff {r : ℕ} (j : Fin (r + 1)) (n : ℕ)
    (Q : MvPolynomial (Fin 2) K) :
    Q ∈ chartIdeal r j ^ (n + 1) ↔ ∀ e ∈ Q.support, n + 1 ≤ ordc r j e := by
  unfold chartIdeal ordc
  by_cases h0 : j = 0
  · subst h0
    simp only [if_true, Fin.val_zero]
    exact mem_span_X_pow_iff 1 n Q
  · have h0' : (j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
    simp only [if_neg h0, if_neg h0']
    by_cases hl : j = Fin.last r
    · subst hl
      simp only [if_true, Fin.val_last]
      exact mem_span_X_pow_iff 0 n Q
    · have hl' : (j : ℕ) ≠ r := fun h => hl (Fin.ext (by simpa using h))
      simp only [if_neg hl, if_neg hl']
      exact mem_span_X_mul_X_pow_iff n Q

end Plumbing

section ChartData

variable {K : Type v} [Field K] {X : Scheme.{v}} (sX : X ⟶ Spec (.of K))
  (I : X.IdealSheafData) {r : ℕ} (V : Fin (r + 1) → X.Opens)
  (x y : ∀ j n, Γ((I ^ (n + 1)).subscheme, trS I n (V j)))

/-- The presentation `K[x, y] → Γ((n+1)E ∩ V_j)` of chart `j` on the `(n+1)`-st thickening. -/
private noncomputable def chartPres (j : Fin (r + 1)) (n : ℕ) :
    MvPolynomial (Fin 2) K →+* Γ((I ^ (n + 1)).subscheme, trS I n (V j)) :=
  eval₂Hom (σS sX I n (trS I n (V j))) ![x j n, y j n]

private theorem chartPres_X_zero (j : Fin (r + 1)) (n : ℕ) :
    chartPres sX I V x y j n (MvPolynomial.X 0) = x j n := by
  simp [chartPres]

private theorem chartPres_X_one (j : Fin (r + 1)) (n : ℕ) :
    chartPres sX I V x y j n (MvPolynomial.X 1) = y j n := by
  simp [chartPres]

private theorem chartPres_C (j : Fin (r + 1)) (n : ℕ) (c : K) :
    chartPres sX I V x y j n (C c) = σS sX I n (trS I n (V j)) c := by
  simp [chartPres]

private theorem ρS_chartPres (hcomp : ∀ j n, ρS I n (V j) (x j (n + 1)) = x j n ∧
      ρS I n (V j) (y j (n + 1)) = y j n) (j : Fin (r + 1)) (n : ℕ)
    (Q : MvPolynomial (Fin 2) K) :
    ρS I n (V j) (chartPres sX I V x y j (n + 1) Q) = chartPres sX I V x y j n Q := by
  have : (ρS I n (V j)).comp (chartPres sX I V x y j (n + 1)) = chartPres sX I V x y j n := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, chartPres_C, ρS_σS]
    · fin_cases i
      · simp only [RingHom.comp_apply, Fin.zero_eta, Fin.isValue, chartPres_X_zero, (hcomp j n).1]
      · simp only [RingHom.comp_apply, Fin.mk_one, Fin.isValue, chartPres_X_one, (hcomp j n).2]
  exact congrArg (fun φ => φ Q) this

variable {sX I V x y} in
private theorem chartPres_eq_zero_iff
    (hker : ∀ j n, RingHom.ker (chartPres sX I V x y j n) = chartIdeal r j ^ (n + 1))
    (j : Fin (r + 1)) (n : ℕ)
    (Q : MvPolynomial (Fin 2) K) :
    chartPres sX I V x y j n Q = 0 ↔ ∀ e ∈ Q.support, n + 1 ≤ ordc r j e := by
  rw [← RingHom.mem_ker, hker, mem_chartIdeal_pow_iff]

variable {sX I V x y} in
private theorem coeff_eq_of_chartPres_eq
    (hker : ∀ j n, RingHom.ker (chartPres sX I V x y j n) = chartIdeal r j ^ (n + 1))
    {j : Fin (r + 1)} {n : ℕ}
    {Q₁ Q₂ : MvPolynomial (Fin 2) K} (h : chartPres sX I V x y j n Q₁ = chartPres sX I V x y j n Q₂)
    {e : Fin 2 →₀ ℕ} (he : ordc r j e ≤ n) : Q₁.coeff e = Q₂.coeff e := by
  have h0 : chartPres sX I V x y j n (Q₁ - Q₂) = 0 := by rw [map_sub, h, sub_self]
  rw [chartPres_eq_zero_iff hker] at h0
  by_contra hne
  have := h0 e (by rw [mem_support_iff, coeff_sub]; exact sub_ne_zero.mpr hne)
  omega

variable (hsurj : ∀ j n, Function.Surjective (chartPres sX I V x y j n))

/-- A polynomial representing a function on the thickening on chart `j`. -/
private noncomputable def repc (j : Fin (r + 1)) (n : ℕ) (s : Γ(I.thickening n, ⊤)) :
    MvPolynomial (Fin 2) K :=
  Function.surjInv (hsurj j n) (resS I n le_top s)

private theorem chartPres_repc (j : Fin (r + 1)) (n : ℕ) (s : Γ(I.thickening n, ⊤)) :
    chartPres sX I V x y j n (repc sX I V x y hsurj j n s) = resS I n le_top s :=
  Function.surjInv_eq (hsurj j n) _

end ChartData

section Xi

variable {K : Type v} [Field K] {X : Scheme.{v}} {sX : X ⟶ Spec (.of K)}
  {I : X.IdealSheafData} {r : ℕ} {V : Fin (r + 1) → X.Opens}
  {x y : ∀ j n, Γ((I ^ (n + 1)).subscheme, trS I n (V j))}
  (hcomp : ∀ j n, ρS I n (V j) (x j (n + 1)) = x j n ∧
      ρS I n (V j) (y j (n + 1)) = y j n)
  (hsurj : ∀ j n, Function.Surjective (chartPres sX I V x y j n))
  (hker : ∀ j n, RingHom.ker (chartPres sX I V x y j n) = chartIdeal r j ^ (n + 1))

include hcomp hker in
private theorem coeff_repc_succ (a : I.formalNeighborhoodRing) (j : Fin (r + 1)) (n : ℕ)
    {e : Fin 2 →₀ ℕ} (he : ordc r j e ≤ n) :
    (repc sX I V x y hsurj j (n + 1) (a.1 (n + 1))).coeff e =
      (repc sX I V x y hsurj j n (a.1 n)).coeff e := by
  apply coeff_eq_of_chartPres_eq hker _ he
  rw [← ρS_chartPres sX I V x y hcomp, chartPres_repc, chartPres_repc, ρS_resS_top, a.2 n]

include hcomp hker in
private theorem coeff_repc_le (a : I.formalNeighborhoodRing) (j : Fin (r + 1)) {m n : ℕ}
    (hmn : m ≤ n) {e : Fin 2 →₀ ℕ} (he : ordc r j e ≤ m) :
    (repc sX I V x y hsurj j n (a.1 n)).coeff e =
      (repc sX I V x y hsurj j m (a.1 m)).coeff e := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih => rw [coeff_repc_succ hcomp hsurj hker a j n (he.trans hmn), ih]

/-- The coefficients of a formal function on the thickenings, read on the charts. -/
private noncomputable def chartCoeffs (a : I.formalNeighborhoodRing) :
    Fin (r + 1) → MvPowerSeries (Fin 2) K :=
  fun j e => (repc sX I V x y hsurj j (ordc r j e) (a.1 (ordc r j e))).coeff e

include hcomp hker in
private theorem coeff_chartCoeffs (a : I.formalNeighborhoodRing) (j : Fin (r + 1)) {n : ℕ}
    {e : Fin 2 →₀ ℕ} (he : ordc r j e ≤ n) :
    MvPowerSeries.coeff e (chartCoeffs hsurj a j) = (repc sX I V x y hsurj j n (a.1 n)).coeff e :=
  (coeff_repc_le hcomp hsurj hker a j he le_rfl).symm

/-- **Formal functions on the thickenings as families of power series on the charts.** -/
private noncomputable def chartCoeffsHom :
    I.formalNeighborhoodRing →+* (Fin (r + 1) → MvPowerSeries (Fin 2) K) where
  toFun := chartCoeffs hsurj
  map_one' := funext fun j => MvPowerSeries.ext fun e => by
    rw [coeff_chartCoeffs hcomp hsurj hker 1 j le_rfl]
    have : chartPres sX I V x y j (ordc r j e) (repc sX I V x y hsurj j (ordc r j e)
        ((1 : I.formalNeighborhoodRing).1 (ordc r j e))) =
        chartPres sX I V x y j (ordc r j e) 1 := by
      rw [chartPres_repc, map_one]; exact map_one _
    rw [coeff_eq_of_chartPres_eq hker this le_rfl, MvPolynomial.coeff_one, Pi.one_apply,
      MvPowerSeries.coeff_one]
    simp only [eq_comm]
  map_mul' a b := funext fun j => MvPowerSeries.ext fun e => by
    change MvPowerSeries.coeff e (chartCoeffs hsurj (a * b) j) =
      MvPowerSeries.coeff e (chartCoeffs hsurj a j * chartCoeffs hsurj b j)
    set n := ordc r j e
    rw [coeff_chartCoeffs hcomp hsurj hker (a * b) j (le_refl n)]
    have : chartPres sX I V x y j n (repc sX I V x y hsurj j n ((a * b).1 n)) =
        chartPres sX I V x y j n (repc sX I V x y hsurj j n (a.1 n) *
          repc sX I V x y hsurj j n (b.1 n)) := by
      rw [map_mul, chartPres_repc, chartPres_repc, chartPres_repc]
      exact map_mul _ _ _
    rw [coeff_eq_of_chartPres_eq hker this le_rfl, MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [coeff_chartCoeffs hcomp hsurj hker a j (ordc_mono r j (hp' ▸ le_self_add)),
      coeff_chartCoeffs hcomp hsurj hker b j (ordc_mono r j (hp' ▸ le_add_self))]
  map_zero' := funext fun j => MvPowerSeries.ext fun e => by
    rw [coeff_chartCoeffs hcomp hsurj hker 0 j le_rfl]
    have : chartPres sX I V x y j (ordc r j e) (repc sX I V x y hsurj j (ordc r j e)
        ((0 : I.formalNeighborhoodRing).1 (ordc r j e))) =
        chartPres sX I V x y j (ordc r j e) 0 := by
      rw [chartPres_repc, map_zero]; exact map_zero _
    rw [coeff_eq_of_chartPres_eq hker this le_rfl, MvPolynomial.coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply]
    rfl
  map_add' a b := funext fun j => MvPowerSeries.ext fun e => by
    change MvPowerSeries.coeff e (chartCoeffs hsurj (a + b) j) =
      MvPowerSeries.coeff e (chartCoeffs hsurj a j + chartCoeffs hsurj b j)
    rw [map_add, coeff_chartCoeffs hcomp hsurj hker (a + b) j le_rfl,
      coeff_chartCoeffs hcomp hsurj hker a j le_rfl, coeff_chartCoeffs hcomp hsurj hker b j le_rfl,
      ← MvPolynomial.coeff_add]
    refine coeff_eq_of_chartPres_eq (j := j) (n := ordc r j e) hker ?_ le_rfl
    rw [map_add, chartPres_repc, chartPres_repc, chartPres_repc]
    exact map_add _ _ _

end Xi

section Sheaf

variable {Y : Scheme.{v}} {ι : Type*}

private theorem eq_of_map_eq_of_le_iSup (U : ι → Y.Opens) (hU : ⊤ ≤ ⨆ i, U i) (s t : Γ(Y, ⊤))
    (h : ∀ i, (Y.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s =
      (Y.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' Y.sheaf U ⊤ (fun i => homOfLE le_top) hU s t h

private theorem exists_map_eq_of_le_iSup (U : ι → Y.Opens) (hU : ⊤ ≤ ⨆ i, U i)
    (sf : ∀ i, Γ(Y, U i))
    (h : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (sf i) =
      (Y.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (sf j)) :
    ∃ s : Γ(Y, ⊤), ∀ i, (Y.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = sf i := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf U ⊤ (fun i => homOfLE le_top) hU
    sf h
  exact ⟨s, hs⟩

/-- If `z ∈ Γ(Y, U)` restricts to zero on the basic open `D(f)` of an affine open `U`, then
`f ^ m * z = 0` for some `m`. -/
private theorem exists_pow_mul_eq_zero_of_map_eq_zero {U W : Y.Opens} (hU : IsAffineOpen U)
    (f : Γ(Y, U)) (hW : W = Y.basicOpen f) (hWU : W ≤ U) (z : Γ(Y, U))
    (hz : (Y.presheaf.map (homOfLE hWU).op).hom z = 0) : ∃ m : ℕ, f ^ m * z = 0 := by
  subst hW
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y hU z f hz

end Sheaf

section XiProps

variable {K : Type v} [Field K] {X : Scheme.{v}} {sX : X ⟶ Spec (.of K)}
  {I : X.IdealSheafData} {r : ℕ} {V : Fin (r + 1) → X.Opens}
  {x y : ∀ j n, Γ((I ^ (n + 1)).subscheme, trS I n (V j))}
  (hcomp : ∀ j n, ρS I n (V j) (x j (n + 1)) = x j n ∧
      ρS I n (V j) (y j (n + 1)) = y j n)
  (hsurj : ∀ j n, Function.Surjective (chartPres sX I V x y j n))
  (hker : ∀ j n, RingHom.ker (chartPres sX I V x y j n) = chartIdeal r j ^ (n + 1))
  (hcovS : ∀ n, ⊤ ≤ ⨆ j, trS I n (V j))

include hcovS in
private theorem chartCoeffsHom_injective :
    Function.Injective (chartCoeffsHom hcomp hsurj hker) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine Subtype.ext (funext fun n => ?_)
  refine eq_of_map_eq_of_le_iSup (fun j => trS I n (V j)) (hcovS n) _ _ fun j => ?_
  change resS I n le_top (a.1 n) = resS I n le_top 0
  rw [map_zero, ← chartPres_repc sX I V x y hsurj, chartPres_eq_zero_iff hker]
  intro e he
  by_contra hlt
  have := congrArg (fun f : Fin (r + 1) → MvPowerSeries (Fin 2) K => MvPowerSeries.coeff e (f j))
    ha
  simp only [Pi.zero_apply, map_zero] at this
  change MvPowerSeries.coeff e (chartCoeffs hsurj a j) = 0 at this
  rw [coeff_chartCoeffs hcomp hsurj hker a j (n := n) (by omega)] at this
  exact mem_support_iff.mp he this

private theorem chartCoeffsHom_const (c : K) (a : I.formalNeighborhoodRing)
    (ha : ∀ n, a.1 n = σS sX I n ⊤ c) :
    chartCoeffsHom hcomp hsurj hker a = fun _ => MvPowerSeries.C c := by
  funext j
  ext e
  change MvPowerSeries.coeff e (chartCoeffs hsurj a j) = _
  rw [coeff_chartCoeffs hcomp hsurj hker a j le_rfl]
  have : chartPres sX I V x y j (ordc r j e)
      (repc sX I V x y hsurj j (ordc r j e) (a.1 (ordc r j e))) =
      chartPres sX I V x y j (ordc r j e) (MvPolynomial.C c) := by
    rw [chartPres_repc, ha, resS_σS, chartPres_C]
  rw [coeff_eq_of_chartPres_eq hker this le_rfl, MvPolynomial.coeff_C, MvPowerSeries.coeff_C]
  simp only [eq_comm]

/-- Membership in `(X_i) + (X_{1-i})^(n+1)`. -/
private theorem mem_span_X_sup_span_X_pow_iff (i i' : Fin 2) (n : ℕ)
    (Q : MvPolynomial (Fin 2) K) :
    Q ∈ Ideal.span {(MvPolynomial.X i : MvPolynomial (Fin 2) K)} ⊔
      Ideal.span {(MvPolynomial.X i' : MvPolynomial (Fin 2) K)} ^ (n + 1) ↔
      ∀ e, e i = 0 → e i' ≤ n → Q.coeff e = 0 := by
  rw [Ideal.span_singleton_pow, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X,
    ← Ideal.span_union, show ({MvPolynomial.monomial (Finsupp.single i 1) (1 : K)} ∪
      {MvPolynomial.monomial (Finsupp.single i' (n + 1)) 1} : Set (MvPolynomial (Fin 2) K)) =
      (fun s => MvPolynomial.monomial s 1) '' {Finsupp.single i 1, Finsupp.single i' (n + 1)} by
        rw [Set.image_pair]; rfl, MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h e he0 he1
    by_contra hne
    obtain ⟨si, hsi, hle⟩ := h e (mem_support_iff.mpr hne)
    rcases hsi with rfl | rfl
    · have := hle i; simp at this; omega
    · have := hle i'; simp at this; omega
  · intro h e he
    by_cases h0 : e i = 0
    · refine ⟨Finsupp.single i' (n + 1), Or.inr rfl, ?_⟩
      rw [Finsupp.single_le_iff]
      by_contra hlt
      exact mem_support_iff.mp he (h e h0 (by omega))
    · exact ⟨Finsupp.single i 1, Or.inl rfl, Finsupp.single_le_iff.mpr (by omega)⟩

include hker in
/-- On chart `j`, a section lies in the ideal of `P(X_i)` exactly when its representative has no
monomial free of `X_i` of order at most `n`, given that the chart kernel is `(X_{i'})^(n+1)`. -/
private theorem resS_mem_span_iff (j : Fin (r + 1)) (n : ℕ) (i i' : Fin 2)
    (hJ : chartIdeal r j = Ideal.span {(MvPolynomial.X i' : MvPolynomial (Fin 2) K)})
    (s : Γ(I.thickening n, ⊤)) :
    resS I n le_top s ∈ Ideal.span {chartPres sX I V x y j n (MvPolynomial.X i)} ↔
      ∀ e, e i = 0 → e i' ≤ n → (repc sX I V x y hsurj j n s).coeff e = 0 := by
  rw [← chartPres_repc sX I V x y hsurj, ← Set.image_singleton, ← Ideal.map_span,
    ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (hsurj j n), ← RingHom.ker_eq_comap_bot,
    hker, hJ, mem_span_X_sup_span_X_pow_iff i i']

private theorem chartCoeffsHom_first_mem_span_iff (a : I.formalNeighborhoodRing) :
    chartCoeffsHom hcomp hsurj hker a 0 ∈ Ideal.span {MvPowerSeries.X 0} ↔
      ∀ n, resS I n le_top (a.1 n) ∈ Ideal.span {x 0 n} := by
  have hJ : chartIdeal r (0 : Fin (r + 1)) =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} := by
    simp [chartIdeal]
  have hord : ∀ e : Fin 2 →₀ ℕ, ordc r 0 e = e 1 := fun e => by simp [ordc]
  simp_rw [← chartPres_X_zero sX I V x y 0, resS_mem_span_iff hsurj hker 0 _ 0 1 hJ,
    Ideal.mem_span_singleton, MvPowerSeries.X_dvd_iff]
  constructor
  · intro h n e he0 he1
    have := h e he0
    change MvPowerSeries.coeff e (chartCoeffs hsurj a 0) = 0 at this
    rwa [coeff_chartCoeffs hcomp hsurj hker a 0 (n := n) (by rw [hord]; exact he1)] at this
  · intro h e he0
    change MvPowerSeries.coeff e (chartCoeffs hsurj a 0) = 0
    rw [coeff_chartCoeffs hcomp hsurj hker a 0 (n := e 1) (by rw [hord])]
    exact h (e 1) e he0 le_rfl

private theorem chartCoeffsHom_last_mem_span_iff (hr : 0 < r) (a : I.formalNeighborhoodRing) :
    chartCoeffsHom hcomp hsurj hker a (Fin.last r) ∈ Ideal.span {MvPowerSeries.X 1} ↔
      ∀ n, resS I n le_top (a.1 n) ∈ Ideal.span {y (Fin.last r) n} := by
  have h0 : (Fin.last r) ≠ 0 := fun h => by
    have := congrArg Fin.val h; simp at this; omega
  have hJ : chartIdeal r (Fin.last r) =
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} := by
    simp [chartIdeal, h0]
  have hord : ∀ e : Fin 2 →₀ ℕ, ordc r (Fin.last r) e = e 0 := fun e => by
    simp [ordc]; omega
  simp_rw [← chartPres_X_one sX I V x y (Fin.last r),
    resS_mem_span_iff hsurj hker (Fin.last r) _ 1 0 hJ,
    Ideal.mem_span_singleton, MvPowerSeries.X_dvd_iff]
  constructor
  · intro h n e he0 he1
    have := h e he0
    change MvPowerSeries.coeff e (chartCoeffs hsurj a (Fin.last r)) = 0 at this
    rwa [coeff_chartCoeffs hcomp hsurj hker a (Fin.last r) (n := n)
      (by rw [hord]; exact he1)] at this
  · intro h e he0
    change MvPowerSeries.coeff e (chartCoeffs hsurj a (Fin.last r)) = 0
    rw [coeff_chartCoeffs hcomp hsurj hker a (Fin.last r) (n := e 0) (by rw [hord])]
    exact h (e 0) e he0 le_rfl

end XiProps

/-- The coefficient of `x^a y^c` of a power series (`a, c ∈ ℤ`, zero for a negative exponent). -/
private noncomputable def coeffZps {K : Type*} [Field K] (f : MvPowerSeries (Fin 2) K)
    (a c : ℤ) : K :=
  if 0 ≤ a ∧ 0 ≤ c then
    MvPowerSeries.coeff (Finsupp.single 0 a.toNat + Finsupp.single 1 c.toNat) f else 0

/-- The compatible families of power series on the charts of the formal plumbing. -/
private def plumbingSet {K : Type*} [Field K] (r : ℕ) (b : Fin r → ℕ) :
    Set (Fin (r + 1) → MvPowerSeries (Fin 2) K) :=
  {f | (∀ j n, {e : Fin 2 →₀ ℕ | MvPowerSeries.coeff e (f j) ≠ 0 ∧ ordc r j e < n}.Finite) ∧
    ∀ (i : Fin r) (a c : ℤ),
      coeffZps (f i.castSucc) a c = coeffZps (f i.succ) c ((b i : ℤ) * c - a)}

section XiRange

variable {K : Type v} [Field K] {X : Scheme.{v}} {sX : X ⟶ Spec (.of K)}
  {I : X.IdealSheafData} {r : ℕ} {V : Fin (r + 1) → X.Opens}
  {x y : ∀ j n, Γ((I ^ (n + 1)).subscheme, trS I n (V j))}
  (hcomp : ∀ j n, ρS I n (V j) (x j (n + 1)) = x j n ∧
      ρS I n (V j) (y j (n + 1)) = y j n)
  (hsurj : ∀ j n, Function.Surjective (chartPres sX I V x y j n))
  (hker : ∀ j n, RingHom.ker (chartPres sX I V x y j n) = chartIdeal r j ^ (n + 1))
  (hcovS : ∀ n, ⊤ ≤ ⨆ j, trS I n (V j)) (b : Fin r → ℕ)
  (haff : ∀ j n, IsAffineOpen (trS I n (V j)))
  (hovx : ∀ (i : Fin r) n, trS I n (V i.castSucc) ⊓ trS I n (V i.succ) =
    (I ^ (n + 1)).subscheme.basicOpen (x i.castSucc n))
  (hemp : ∀ (j k : Fin (r + 1)) n, j.val + 2 ≤ k.val → trS I n (V j) ⊓ trS I n (V k) = ⊥)
  (htrans : ∀ (i : Fin r) n,
    resS I n (inf_le_right : trS I n (V i.castSucc) ⊓ trS I n (V i.succ) ≤ _) (y i.succ n) *
      resS I n (inf_le_left : trS I n (V i.castSucc) ⊓ trS I n (V i.succ) ≤ _)
        (x i.castSucc n) = 1 ∧
    resS I n (inf_le_right : trS I n (V i.castSucc) ⊓ trS I n (V i.succ) ≤ _) (x i.succ n) =
      resS I n (inf_le_left : trS I n (V i.castSucc) ⊓ trS I n (V i.succ) ≤ _)
        (x i.castSucc n) ^ b i *
      resS I n (inf_le_left : trS I n (V i.castSucc) ⊓ trS I n (V i.succ) ≤ _) (y i.castSucc n))

include hker haff hovx htrans in
/-- Agreement on the overlap of charts `i` and `i + 1`, read on coefficients. -/
private theorem resS_chartPres_eq_iff (i : Fin r) (n : ℕ) (Q Q' : MvPolynomial (Fin 2) K) :
    resS I n (inf_le_left : trS I n (V i.castSucc) ⊓ trS I n (V i.succ) ≤ _)
        (chartPres sX I V x y i.castSucc n Q) =
      resS I n (inf_le_right : trS I n (V i.castSucc) ⊓ trS I n (V i.succ) ≤ _)
        (chartPres sX I V x y i.succ n Q') ↔
      ∀ a c : ℤ, c ≤ n → coeffZ Q a c = coeffZ Q' c (b i * c - a) := by
  have hne : (i.castSucc : ℕ) ≠ r := by simp; omega
  refine map_eq_map_iff_coeffZ (chartPres sX I V x y i.castSucc n) (chartPres sX I V x y i.succ n) n
    (if (i : ℕ) = 0 then 0 else n + 1) ?_ _ ?_ _ (b i) ?_ ?_ ?_ Q Q'
  · intro Q
    rw [chartPres_eq_zero_iff hker]
    refine forall₂_congr fun e _ => ?_
    unfold ordc
    simp only [Fin.coe_castSucc, hne, if_false]
    split_ifs <;> omega
  · intro z hz
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_map_eq_zero (haff i.castSucc n) (x i.castSucc n)
      (hovx i n) inf_le_left z hz
    exact ⟨m, by rwa [chartPres_X_zero]⟩
  · rw [chartPres_X_zero, chartPres_X_one, mul_comm]; exact (htrans i n).1
  · rw [chartPres_X_zero, chartPres_X_one, chartPres_X_zero]; exact (htrans i n).2
  · intro c
    rw [chartPres_C, chartPres_C, resS_σS, resS_σS]

private theorem ordc_le_add (j : Fin (r + 1)) (e : Fin 2 →₀ ℕ) : ordc r j e ≤ e 0 + e 1 := by
  unfold ordc; split_ifs <;> omega

private theorem ordc_le_left (j : Fin (r + 1)) (hj : (j : ℕ) ≠ 0) (e : Fin 2 →₀ ℕ) :
    ordc r j e ≤ e 0 := by
  unfold ordc; split_ifs <;> omega

private theorem ordc_le_right (j : Fin (r + 1)) (hj : (j : ℕ) ≠ r) (e : Fin 2 →₀ ℕ) :
    ordc r j e ≤ e 1 := by
  unfold ordc; split_ifs <;> omega

include hcomp hker in
private theorem coeffZps_chartCoeffs (a : I.formalNeighborhoodRing) (j : Fin (r + 1)) (p c : ℤ)
    {n : ℕ}
    (hn : p.toNat + c.toNat ≤ n) :
    coeffZps (chartCoeffs hsurj a j) p c = coeffZ (repc sX I V x y hsurj j n (a.1 n)) p c := by
  unfold coeffZps coeffZ
  split_ifs with h
  · refine coeff_chartCoeffs hcomp hsurj hker a j ((ordc_le_add j _).trans ?_)
    simpa using hn
  · rfl

include hcomp hker haff hovx htrans in
private theorem range_chartCoeffsHom_subset :
    Set.range (chartCoeffsHom hcomp hsurj hker) ⊆ plumbingSet r b := by
  rintro _ ⟨a, rfl⟩
  refine ⟨fun j n => ?_, fun i p c => ?_⟩
  · refine (repc sX I V x y hsurj j n (a.1 n)).support.finite_toSet.subset fun e ⟨hne, hlt⟩ => ?_
    rw [Finset.mem_coe, mem_support_iff]
    change MvPowerSeries.coeff e (chartCoeffs hsurj a j) ≠ 0 at hne
    rwa [coeff_chartCoeffs hcomp hsurj hker a j (n := n) hlt.le] at hne
  · change coeffZps (chartCoeffs hsurj a i.castSucc) p c = coeffZps (chartCoeffs hsurj a i.succ) c _
    rcases lt_or_ge c 0 with hc | hc
    · simp [coeffZps, not_le.mpr hc]
    set n := c.toNat + p.toNat + ((b i : ℤ) * c - p).toNat
    rw [coeffZps_chartCoeffs hcomp hsurj hker a _ p c (n := n) (by omega),
      coeffZps_chartCoeffs hcomp hsurj hker a _ c _ (n := n) (by omega)]
    refine (resS_chartPres_eq_iff hker b haff hovx htrans i n _ _).mp ?_ p c (by omega)
    rw [chartPres_repc, chartPres_repc, resS_resS, resS_resS]

include hcomp hker hcovS haff hovx hemp htrans in
private theorem plumbingSet_subset_range_chartCoeffsHom :
    plumbingSet r b ⊆ Set.range (chartCoeffsHom hcomp hsurj hker) := by
  classical
  rintro f ⟨hfin, hrel⟩
  let T : ℕ → Fin (r + 1) → MvPolynomial (Fin 2) K := fun n j =>
    ∑ e ∈ (hfin j (n + 1)).toFinset, MvPolynomial.monomial e (MvPowerSeries.coeff e (f j))
  have hT : ∀ n j e, (T n j).coeff e =
      if ordc r j e ≤ n then MvPowerSeries.coeff e (f j) else 0 := by
    intro n j e
    simp only [T, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    split_ifs with h1 h2 h2 <;> first | rfl | omega | (push Not at h1; exact (h1 h2 |>.elim)) |
      (exact (not_not.mp fun h => h1 ⟨h, by omega⟩).symm)
  -- the truncations agree on consecutive overlaps
  have hcons : ∀ n (i : Fin r), resS I n (inf_le_left : trS I n (V i.castSucc) ⊓
      trS I n (V i.succ) ≤ _) (chartPres sX I V x y i.castSucc n (T n i.castSucc)) =
      resS I n (inf_le_right : trS I n (V i.castSucc) ⊓ trS I n (V i.succ) ≤ _)
        (chartPres sX I V x y i.succ n (T n i.succ)) := by
    intro n i
    refine (resS_chartPres_eq_iff hker b haff hovx htrans i n _ _).mpr fun p c hc => ?_
    rcases lt_or_ge c 0 with hc0 | hc0
    · rw [coeffZ_of_neg_right _ _ hc0, coeffZ_of_neg_left _ hc0]
    have h1 : coeffZ (T n i.castSucc) p c = coeffZps (f i.castSucc) p c := by
      unfold coeffZ coeffZps
      split_ifs with h
      · rw [hT, if_pos]
        refine (ordc_le_right _ (by simp; omega) _).trans ?_
        simp; omega
      · rfl
    have h2 : coeffZ (T n i.succ) c ((b i : ℤ) * c - p) =
        coeffZps (f i.succ) c ((b i : ℤ) * c - p) := by
      unfold coeffZ coeffZps
      split_ifs with h
      · rw [hT, if_pos]
        refine (ordc_le_left _ (by simp) _).trans ?_
        simp; omega
      · rfl
    rw [h1, h2, hrel]
  have hcompat : ∀ n (j k : Fin (r + 1)), resS I n (inf_le_left : trS I n (V j) ⊓
      trS I n (V k) ≤ _) (chartPres sX I V x y j n (T n j)) =
      resS I n (inf_le_right : trS I n (V j) ⊓ trS I n (V k) ≤ _)
        (chartPres sX I V x y k n (T n k)) := by
    intro n
    have hle : ∀ j k : Fin (r + 1), j.val ≤ k.val → resS I n (inf_le_left : trS I n (V j) ⊓
        trS I n (V k) ≤ _) (chartPres sX I V x y j n (T n j)) =
        resS I n (inf_le_right : trS I n (V j) ⊓ trS I n (V k) ≤ _)
          (chartPres sX I V x y k n (T n k)) := by
      intro j k hjk
      rcases Nat.lt_or_ge (k.val) (j.val + 2) with h | h
      · rcases Nat.lt_or_ge j.val k.val with h' | h'
        · obtain ⟨i, rfl, rfl⟩ : ∃ i : Fin r, j = i.castSucc ∧ k = i.succ :=
            ⟨⟨j.val, by omega⟩, Fin.ext rfl, Fin.ext (by simp; omega)⟩
          exact hcons n i
        · obtain rfl : j = k := Fin.ext (by omega)
          rfl
      · have : Subsingleton Γ((I ^ (n + 1)).subscheme, trS I n (V j) ⊓ trS I n (V k)) := by
          rw [hemp j k n h]; infer_instance
        exact Subsingleton.elim _ _
    intro j k
    rcases le_total j.val k.val with h | h
    · exact hle j k h
    · have := congrArg (resS I n ((inf_comm _ _).le : trS I n (V j) ⊓ trS I n (V k) ≤
        trS I n (V k) ⊓ trS I n (V j))) (hle k j h)
      rw [resS_resS, resS_resS] at this
      exact this.symm
  have hglue : ∀ n, ∃ s : Γ(I.thickening n, ⊤), ∀ j,
      resS I n le_top s = chartPres sX I V x y j n (T n j) := fun n =>
    exists_map_eq_of_le_iSup (fun j => trS I n (V j)) (hcovS n) _ (hcompat n)
  choose sN hsN using hglue
  have hsucc : ∀ n, I.thickeningRestriction n (sN (n + 1)) = sN n := by
    intro n
    refine eq_of_map_eq_of_le_iSup (fun j => trS I n (V j)) (hcovS n) _ _ fun j => ?_
    change resS I n le_top _ = resS I n le_top _
    rw [← ρS_resS_top, hsN (n + 1) j, ρS_chartPres sX I V x y hcomp, hsN n j, ← sub_eq_zero,
      ← map_sub, chartPres_eq_zero_iff hker]
    intro e he
    rw [mem_support_iff, coeff_sub, hT, hT] at he
    by_contra hlt
    rw [if_pos (by omega), if_pos (by omega), sub_self] at he
    exact he rfl
  refine ⟨⟨sN, hsucc⟩, funext fun j => MvPowerSeries.ext fun e => ?_⟩
  change MvPowerSeries.coeff e (chartCoeffs hsurj ⟨sN, hsucc⟩ j) = _
  rw [coeff_chartCoeffs hcomp hsurj hker _ j le_rfl]
  have : chartPres sX I V x y j (ordc r j e)
      (repc sX I V x y hsurj j (ordc r j e) (sN (ordc r j e))) =
      chartPres sX I V x y j (ordc r j e) (T (ordc r j e) j) := by
    rw [chartPres_repc, hsN]
  rw [coeff_eq_of_chartPres_eq hker this le_rfl, hT, if_pos le_rfl]

end XiRange

end PlumbingCharts

/-! ### Assembly -/

section Assembly

private theorem C_mem_cyclicInvariants {K : Type*} [Field K] (m : ℕ) (q : ℤ) (c : K) :
    MvPowerSeries.C c ∈ cyclicInvariants K m q := by
  rw [mem_cyclicInvariants_iff]
  intro ζ
  ext e
  rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
  split_ifs with h
  · subst h; simp
  · rw [mul_zero]

/-- **Assembly.** A ring isomorphism `Θ : R̂ ≃ A` onto a ring `A` of formal functions and an
injective map `Ξ` from `A` onto the compatible families of the plumbing give, through the
plumbing description of the cyclic invariants, a `K`-isomorphism `K[[u, v]]^{μ_m} ≃ R̂` under
which the end-marking conditions `P₀`, `P₁` become the invariants in `(u)`, `(v)` and
`(u) ∩ (v)`. -/
private theorem exists_ringEquiv_cyclicInvariants_of_plumbing
    {K : Type v} [Field K] [IsAlgClosed K] [CharZero K]
    {R Rh A : Type v} [CommRing R] [CommRing Rh] [CommRing A] [Algebra K R] [Algebra R Rh]
    {r : ℕ} (hr : 1 ≤ r) (b : Fin r → ℕ) (hb : ∀ i, 2 ≤ b i)
    (Θ : Rh ≃+* A) (Ξ : A →+* (Fin (r + 1) → MvPowerSeries (Fin 2) K))
    (hΞi : Function.Injective Ξ) (hΞr : Set.range Ξ = plumbingSet r b)
    (hc : ∀ c : K, Ξ (Θ (algebraMap R Rh (algebraMap K R c))) = fun _ => MvPowerSeries.C c)
    (P₀ P₁ : A → Prop)
    (hP₀ : ∀ a, Ξ a 0 ∈ Ideal.span {MvPowerSeries.X 0} ↔ P₀ a)
    (hP₁ : ∀ a, Ξ a (Fin.last r) ∈ Ideal.span {MvPowerSeries.X 1} ↔ P₁ a) :
    ∃ (m : ℕ) (_ : 2 ≤ m) (q : ℤ) (_ : Int.gcd q m = 1) (φ : cyclicInvariants K m q ≃+* Rh),
      (∀ c : K, ((φ.symm (algebraMap R Rh (algebraMap K R c)) : cyclicInvariants K m q) :
          MvPowerSeries (Fin 2) K) = MvPowerSeries.C c) ∧
      (∀ g : cyclicInvariants K m q, P₀ (Θ (φ g)) ↔
        (g : MvPowerSeries (Fin 2) K) ∈ Ideal.span {MvPowerSeries.X 0}) ∧
      (∀ g : cyclicInvariants K m q, P₁ (Θ (φ g)) ↔
        (g : MvPowerSeries (Fin 2) K) ∈ Ideal.span {MvPowerSeries.X 1}) ∧
      (∀ g : cyclicInvariants K m q, (P₀ (Θ (φ g)) ∧ P₁ (Θ (φ g))) ↔
        (g : MvPowerSeries (Fin 2) K) ∈
          Ideal.span {MvPowerSeries.X 0} ⊓ Ideal.span {MvPowerSeries.X 1}) := by
  obtain ⟨m, hm, q, hq, ψ, hψi, hψr, hψc, hψ0, hψ1, hψ01⟩ :=
    exists_ringHom_cyclicInvariants_chainPlumbing K hr b hb 1
  have hψr' : Set.range ψ = Set.range Ξ := by rw [hΞr]; exact hψr
  -- the isomorphism `cyclicInvariants ≃ A`
  have hex : ∀ g : cyclicInvariants K m q, ∃ a : A, Ξ a = ψ g := fun g =>
    (hψr' ▸ Set.mem_range_self g : ψ g ∈ Set.range Ξ)
  have hex' : ∀ a : A, ∃ g : cyclicInvariants K m q, ψ g = Ξ a := fun a =>
    (hψr' ▸ Set.mem_range_self a : Ξ a ∈ Set.range ψ)
  choose u hu using hex
  let e : cyclicInvariants K m q ≃+* A :=
    { toFun := u
      invFun := fun a => (hex' a).choose
      left_inv := fun g => hψi (by rw [(hex' _).choose_spec, hu])
      right_inv := fun a => hΞi (by rw [hu, (hex' a).choose_spec])
      map_mul' := fun g g' => hΞi (by rw [hu, map_mul, map_mul, hu, hu])
      map_add' := fun g g' => hΞi (by rw [hu, map_add, map_add, hu, hu]) }
  have he : ∀ g, Ξ (e g) = ψ g := hu
  have hsymm : ∀ t : Rh, ψ ((e.trans Θ.symm).symm t) = Ξ (Θ t) := fun t => by
    rw [← he]
    simp
  have hΘ : ∀ g, Ξ (Θ ((e.trans Θ.symm) g)) = ψ g := fun g => by
    rw [← he]
    simp
  refine ⟨m, hm, q, hq, e.trans Θ.symm, fun c => ?_, fun g => ?_, fun g => ?_, fun g => ?_⟩
  · -- constants
    have key : (e.trans Θ.symm).symm (algebraMap R Rh (algebraMap K R c)) =
        ⟨MvPowerSeries.C c, C_mem_cyclicInvariants m q c⟩ := by
      apply hψi
      rw [hsymm, hc, hψc c ⟨MvPowerSeries.C c, C_mem_cyclicInvariants m q c⟩ rfl]
    rw [key]
  · rw [← hP₀, hΘ, hψ0]
    rfl
  · rw [← hP₁, hΘ, hψ1]
    rfl
  · rw [← hP₀, ← hP₁, hΘ, hψ01]
    rfl

/-- Vanishing on a marking supported in `U` can be tested after restricting to the trace of `U`. -/
private theorem inclusion_app_resS_eq_zero_iff {X : Scheme.{v}} (I Z : X.IdealSheafData) (n : ℕ)
    (h : I ^ (n + 1) ≤ Z) {U : X.Opens} (hU : (Z.support : Set X) ⊆ U)
    (s : Γ((I ^ (n + 1)).subscheme, ⊤)) :
    ((Scheme.IdealSheafData.inclusion h).app (trS I n U)).hom (resS I n le_top s) = 0 ↔
      (Scheme.IdealSheafData.inclusion h).appTop.hom s = 0 := by
  have hpre : (⊤ : Z.subscheme.Opens) ≤ Scheme.IdealSheafData.inclusion h ⁻¹ᵁ trS I n U := by
    intro t _
    change (I ^ (n + 1)).subschemeι (Scheme.IdealSheafData.inclusion h t) ∈ U
    rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
    exact hU (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨t, rfl⟩)
  have hnat : ((Scheme.IdealSheafData.inclusion h).app (trS I n U)).hom (resS I n le_top s) =
      (Z.subscheme.presheaf.map (homOfLE (le_top :
        Scheme.IdealSheafData.inclusion h ⁻¹ᵁ trS I n U ≤ ⊤)).op).hom
        ((Scheme.IdealSheafData.inclusion h).appTop.hom s) := by
    simp only [resS, ← CommRingCat.comp_apply]
    rw [Scheme.Hom.naturality]
    rfl
  rw [hnat]
  have hiso : IsIso (homOfLE (le_top : Scheme.IdealSheafData.inclusion h ⁻¹ᵁ trS I n U ≤ ⊤)) :=
    ⟨⟨homOfLE hpre, rfl, rfl⟩⟩
  have hinj : Function.Injective (Z.subscheme.presheaf.map (homOfLE (le_top :
      Scheme.IdealSheafData.inclusion h ⁻¹ᵁ trS I n U ≤ ⊤)).op).hom :=
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  exact ⟨fun h0 => hinj (h0.trans (map_zero _).symm), fun h0 => by rw [h0, map_zero]⟩

end Assembly

/-! ### The exceptional curve -/

/-- The support of a finite product of ideal sheaves is the union of their supports. -/
private theorem coe_support_prod {X : Scheme.{v}} {ι : Type*} (s : Finset ι)
    (F : ι → X.IdealSheafData) :
    ((∏ i ∈ s, F i).support : Set X) = ⋃ i ∈ s, ((F i).support : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul,
      TopologicalSpace.Closeds.coe_sup, ih, Finset.set_biUnion_insert]

/-- On a scheme with regular local rings, the product of the ideal sheaves of distinct prime
divisors is their intersection. -/
private theorem prod_idealSheaf_eq_finsetInf {X : Scheme.{v}} [IsLocallyNoetherian X]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) {r : ℕ}
    (E : Fin r → Mori.PrimeDivisor X) (hinj : Function.Injective E) :
    ∏ i, (E i).idealSheaf = Finset.univ.inf fun i => (E i).idealSheaf := by
  classical
  refine IdealSheafData.eq_of_stalk_eq _ _ fun x => ?_
  have := hreg x
  have : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  have : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain _
  have hπ : ∀ i, ∃ π : X.presheaf.stalk x, IdealSheafData.stalk (E i).idealSheaf x =
      Ideal.span {π} ∧ (x ∈ (E i).support → Prime π) ∧ (x ∉ (E i).support → π = 1) := by
    intro i
    by_cases hx : x ∈ (E i).support
    · obtain ⟨q, -, hq, hq1⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support (E i) hx
      have hq0 : q.asIdeal ≠ ⊥ := by
        intro h0
        rw [h0, Ideal.height_bot] at hq1
        exact zero_ne_one hq1
      obtain ⟨π, hπq, hπ⟩ := q.isPrime.exists_mem_prime_of_ne_bot hq0
      exact ⟨π, hq.trans (Ideal.eq_span_singleton_of_height_eq_one hq1 hπq hπ),
        fun _ => hπ, fun h => absurd hx h⟩
    · exact ⟨1, by rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support _ hx,
        Ideal.span_singleton_one], fun h => absurd h hx, fun _ => rfl⟩
  choose π hπ using hπ
  set T := Finset.univ.filter fun i => x ∈ (E i).support
  have hprod : ∏ i, π i = ∏ i ∈ T, π i := by
    rw [Finset.prod_filter_of_ne]
    intro i _ hi
    by_contra hx
    exact hi ((hπ i).2.2 hx)
  rw [MMP.Resolution.Aux.stalk_prod, MMP.Intersection.stalk_finsetInf]
  simp_rw [fun i => (hπ i).1]
  rw [Ideal.prod_span_singleton, hprod,
    ← MMP.Intersection.finsetInf_span_singleton_eq_span_prod T π
      (fun i hi => (hπ i).2.1 (Finset.mem_filter.mp hi).2)
      (fun i hi j hj hass => hinj (MMP.Intersection.eq_of_stalk_idealSheaf_eq
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
        (by rw [(hπ i).1, (hπ j).1]; exact Ideal.span_singleton_eq_span_singleton.mpr hass)))]
  refine le_antisymm (Finset.le_inf fun i _ => ?_)
    (Finset.le_inf fun i hi => Finset.inf_le (Finset.mem_univ i))
  by_cases hx : x ∈ (E i).support
  · exact Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩)
  · rw [(hπ i).2.2 hx, Ideal.span_singleton_one]
    exact le_top

/-- A finite intersection of ideal sheaves of prime divisors is the ideal of the union of their
supports. -/
private theorem finsetInf_idealSheaf_eq_vanishingIdeal {X : Scheme.{v}} {ι : Type*}
    (s : Finset ι) (E : ι → Mori.PrimeDivisor X) :
    (s.inf fun i => (E i).idealSheaf) =
      Scheme.IdealSheafData.vanishingIdeal (s.sup fun i => (E i).idealSheaf.support) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.sup_insert, Scheme.IdealSheafData.vanishingIdeal_sup, ih,
      MMP.Intersection.vanishingIdeal_support_idealSheaf (E a)]

/-! ### The contraction of the marked chain -/

/-- The support of each marking trace is the marked point. -/
private theorem support_eq_support_zero_of_eq_sup_pow {X : Scheme.{v}} (I : X.IdealSheafData)
    (Z : ℕ → X.IdealSheafData) (hZ : ∀ n, I ^ (n + 1) ≤ Z n)
    (hZ_succ : ∀ n, Z n = Z (n + 1) ⊔ I ^ (n + 1)) (n : ℕ) :
    (Z n).support = (Z 0).support := by
  have hs := I.support_pow_succ
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih, hZ_succ n, Scheme.IdealSheafData.support_sup]
    refine (inf_eq_left.mpr ?_).symm
    rw [hs n, ← hs (n + 1)]
    exact Scheme.IdealSheafData.support_antitone (hZ (n + 1))

@[expose] public section

open Scheme.IdealSheafData in
/-- **Contracting a doubly marked negative chain gives a cyclic quotient** (FA 16.6.3). Let
`f : X ⟶ Y` be a contraction of a smooth surface onto a normal surface over an algebraically
closed field `K` of characteristic `0`, and `y ∈ Y` a closed point whose fibre is the chain
`E₀, …, E_{r-1}` of smooth rational curves with `(Eᵢ · Eᵢ) = -bᵢ`, `bᵢ ≥ 2`, marked at its ends
by smooth transverse formal germs with traces `ZL n`, `ZR n` on the thickenings `(n+1)E`. Then
there are `m ≥ 2`, `q` prime to `m`, a `K`-isomorphism
`φ : MMP.Flips.cyclicInvariants K m q ≃+* 𝒪̂_{Y,y}`, and the formal-functions comparison maps
`ψ n : 𝒪̂_{Y,y} → Γ((n+1)E, 𝒪)`, such that `φ` carries the invariants in `(u)`, `(v)` and
`(u) ∩ (v)` onto the ideals of formal functions vanishing on `Z_L`, on `Z_R`, and on both. -/
@[mmp "lem_mmp_foundation_fa16_marked_chain_contraction"]
public theorem exists_ringEquiv_cyclicInvariants_of_isSNCChain_fibre
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) (f : X ⟶ Y)
    (hf : IsContraction K sY sX f) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [IsNormal Y] (hY : topologicalKrullDim Y = 2)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    {r : ℕ} (hr : 0 < r) (E : Fin r → Mori.PrimeDivisor X) (b : Fin r → ℕ)
    (hb : ∀ i, 2 ≤ b i)
    (hfib : f.base ⁻¹' {y} = ⋃ i, ((E i).support : Set X))
    (hinj : Function.Injective E)
    (hrat : ∀ i, IsSmoothRationalCurve sX (E i).idealSheaf)
    (hself : ∀ i, IsIntersectionNumber sX (Finsupp.single (E i) 1) (E i).idealSheaf (-(b i : ℤ)))
    (hadj : ∀ i j : Fin r, i.val + 1 = j.val →
      IsIntersectionNumber sX (Finsupp.single (E i) 1) (E j).idealSheaf 1)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → Disjoint (E i).support (E j).support)
    (pL pR : X) (hpLR : pL ≠ pR)
    (hpL : pL ∈ (E ⟨0, hr⟩).support) (hpL' : ∀ i, i ≠ ⟨0, hr⟩ → pL ∉ (E i).support)
    (hpR : pR ∈ (E ⟨r - 1, by omega⟩).support)
    (hpR' : ∀ i, i ≠ ⟨r - 1, by omega⟩ → pR ∉ (E i).support)
    (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZR_succ : ∀ n, ZR n = ZR (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZL_zero : ((ZL 0).support : Set X) = {pL}) (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX) :
    letI := Mori.stalkAlgebra sY y
    let I := ∏ i, (E i).idealSheaf
    -- the completed local ring `𝒪̂_{Y,y}`
    let R := Y.presheaf.stalk y
    let Rhat := AdicCompletion (maximalIdeal R) R
    -- the thickening `(n+1)E ⟶ X ⟶ Y`
    let g : ∀ n, (I ^ (n + 1)).subscheme ⟶ Y := fun n => (I ^ (n + 1)).subschemeι ≫ f
    ∃ (m : ℕ) (_ : 2 ≤ m) (q : ℤ) (_ : Int.gcd q m = 1)
      (φ : cyclicInvariants K m q ≃+* Rhat)
      (ψ : ∀ n, Rhat →+* Γ((I ^ (n + 1)).subscheme, ⊤)),
      -- `φ` is a `K`-isomorphism
      (∀ c : K, ((φ.symm (algebraMap R Rhat (algebraMap K R c)) : cyclicInvariants K m q) :
          MvPowerSeries (Fin 2) K) = MvPowerSeries.C c) ∧
      -- `ψ n` is the formal-functions comparison `𝒪̂_{Y,y} → Γ((n+1)E, 𝒪)`
      (∀ n (U : Y.Opens) (hyU : y ∈ U) (hU : ⊤ ≤ g n ⁻¹ᵁ U) (s : Γ(Y, U)),
        ψ n (algebraMap R Rhat (Y.presheaf.germ U y hyU s)) = ((g n).appLE U ⊤ hU).hom s) ∧
      -- `φ` carries the invariants in `(u)` onto `I_{Z_L}`
      (∀ a : cyclicInvariants K m q,
        (∀ n, ((Scheme.IdealSheafData.inclusion (hZL n)).app ⊤).hom (ψ n (φ a)) = 0) ↔
          (a : MvPowerSeries (Fin 2) K) ∈ Ideal.span {MvPowerSeries.X 0}) ∧
      -- `φ` carries the invariants in `(v)` onto `I_{Z_R}`
      (∀ a : cyclicInvariants K m q,
        (∀ n, ((Scheme.IdealSheafData.inclusion (hZR n)).app ⊤).hom (ψ n (φ a)) = 0) ↔
          (a : MvPowerSeries (Fin 2) K) ∈ Ideal.span {MvPowerSeries.X 1}) ∧
      -- `φ` carries the invariants in `(u) ∩ (v)` onto `I_{Z_L} ∩ I_{Z_R}`
      (∀ a : cyclicInvariants K m q,
        ((∀ n, ((Scheme.IdealSheafData.inclusion (hZL n)).app ⊤).hom (ψ n (φ a)) = 0) ∧
          ∀ n, ((Scheme.IdealSheafData.inclusion (hZR n)).app ⊤).hom (ψ n (φ a)) = 0) ↔
          (a : MvPowerSeries (Fin 2) K) ∈
            Ideal.span {MvPowerSeries.X 0} ⊓ Ideal.span {MvPowerSeries.X 1}) := by
  letI := Mori.stalkAlgebra sY y
  obtain ⟨hYv, hXv, hfs, hfp, hfiso⟩ := hf
  subst hfs
  -- finiteness and the structure sheaf
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : QuasiCompact sY := hYv.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := ⟨⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ sY)
  have : IsNoetherian X := ⟨⟩
  have : IsProper f := hfp
  have : IsIso f.c := by
    have : ∀ U, IsIso (f.c.app U) := fun U => hfiso U.unop
    exact NatIso.isIso_of_isIso_app _
  -- the reduced exceptional curve
  set I := ∏ i, (E i).idealSheaf with hI
  have : Smooth (f ≫ sY) := SmoothOfRelativeDimension.smooth 2 _
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    ((isRegular_iff_regular_stalks X).1
      (MMP.Resolution.Bridges.isRegular_of_isSmoothScheme (f ≫ sY)
        ((isSmoothScheme_iff _).mpr inferInstance))).2
  have : IsReduced I.subscheme := by
    rw [hI, prod_idealSheaf_eq_finsetInf hreg E hinj, finsetInf_idealSheaf_eq_vanishingIdeal]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hsuppI : (I.support : Set X) = f.base ⁻¹' {y} := by
    rw [hI, coe_support_prod, hfib]
    simp
  have hmaps : ∀ x ∈ (I.support : Set X), f.base x = y := fun x hx => by
    rw [hsuppI] at hx
    exact hx
  have hZLs : ∀ n, ((ZL n).support : Set X) = {pL} := fun n => by
    rw [support_eq_support_zero_of_eq_sup_pow I ZL hZL hZL_succ n, hZL_zero]
  have hZRs : ∀ n, ((ZR n).support : Set X) = {pR} := fun n => by
    rw [support_eq_support_zero_of_eq_sup_pow I ZR hZR hZR_succ n, hZR_zero]
  -- the formal plumbing charts
  obtain ⟨V, x, y', hcov, hcomp, hpres, ⟨hpL0, hpR0, hmark⟩, hov, hdisj, hinit⟩ :=
    MMP.Mori.exists_formalPlumbingCharts_of_isSNCChain (f ≫ sY) hr E b hb hinj hrat hself hadj
      hfar pL pR hpLR hpL hpL' hpR hpR' ZL ZR hZL hZR hZL_succ hZR_succ hZL_zero hZR_zero
      hZL_curvilinear hZR_curvilinear
  have hsurj : ∀ j n, Function.Surjective (chartPres (f ≫ sY) I V x y' j n) :=
    fun j n => (hpres j n).2.1
  have hker : ∀ j n, RingHom.ker (chartPres (f ≫ sY) I V x y' j n) = chartIdeal r j ^ (n + 1) :=
    fun j n => (hpres j n).2.2
  have haff : ∀ j n, IsAffineOpen (trS I n (V j)) := fun j n => (hpres j n).1
  have hmapsupp : ∀ n (t : (I ^ (n + 1)).subscheme), (I ^ (n + 1)).subschemeι t ∈ I.support := by
    intro n t
    have : (I ^ (n + 1)).subschemeι t ∈ ((I ^ (n + 1)).support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨t, rfl⟩
    rwa [I.support_pow_succ n] at this
  have hcovS : ∀ n, ⊤ ≤ ⨆ j, trS I n (V j) := by
    intro n t _
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov (hmapsupp n t))
    exact (TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩)
  have hovx : ∀ (i : Fin r) n, trS I n (V i.castSucc) ⊓ trS I n (V i.succ) =
      (I ^ (n + 1)).subscheme.basicOpen (x i.castSucc n) := fun i n => ((hov i).2 n).1
  have hemp : ∀ (j k : Fin (r + 1)) n, j.val + 2 ≤ k.val →
      trS I n (V j) ⊓ trS I n (V k) = ⊥ := by
    intro j k n hjk
    refine eq_bot_iff.mpr fun t ht => ?_
    have h1 : (I ^ (n + 1)).subschemeι t ∈ (((V j ⊓ V k : X.Opens) : Set X) ∩ I.support) :=
      ⟨ht, hmapsupp n t⟩
    rw [hdisj j k hjk] at h1
    exact h1.elim
  -- the plumbing charts
  let Ξ := chartCoeffsHom hcomp hsurj hker
  have hΞi : Function.Injective Ξ := chartCoeffsHom_injective hcomp hsurj hker hcovS
  have hΞr : Set.range Ξ = plumbingSet r b :=
    (range_chartCoeffsHom_subset (hcomp := hcomp) (hsurj := hsurj) (hker := hker) (b := b)
      (haff := haff) (hovx := hovx) (htrans := hinit)).antisymm
    (plumbingSet_subset_range_chartCoeffsHom (hcomp := hcomp) (hsurj := hsurj) (hker := hker)
      (hcovS := hcovS) (b := b) (haff := haff) (hovx := hovx) (hemp := hemp) (htrans := hinit))
  -- the theorem on formal functions
  have hK := exists_pow_succ_le_ker_infinitesimalι I f y hy hsuppI.ge
  let Θ : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+*
      I.formalNeighborhoodRing :=
    RingEquiv.ofBijective (I.completionToFormalNeighborhood f y hmaps)
      (@bijective_completionToFormalNeighborhood X Y I f y hmaps hK ‹_› ‹_› ‹_›
        (inferInstance : IsNoetherian Y).toIsLocallyNoetherian)
  have hc : ∀ c : K, Ξ (Θ (algebraMap (Y.presheaf.stalk y) _
      (algebraMap K (Y.presheaf.stalk y) c))) = fun _ => MvPowerSeries.C c := by
    intro c
    refine chartCoeffsHom_const hcomp hsurj hker c _ fun n => ?_
    have h1 : (Θ (algebraMap (Y.presheaf.stalk y) _ (algebraMap K (Y.presheaf.stalk y) c))).1 n =
        (stalkToThickening I f y hmaps n).hom (algebraMap K (Y.presheaf.stalk y) c) := by
      change (I.completionToFormalNeighborhood f y hmaps (AdicCompletion.of _ _ _)).1 n = _
      rw [completionToFormalNeighborhood_of]
      rfl
    rw [h1]
    change (stalkToThickening I f y hmaps n).hom ((Y.presheaf.germ ⊤ y
      (TopologicalSpace.Opens.mem_top y)).hom (sY.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom c)))
        = _
    rw [stalkToThickening, Scheme.Hom.stalkToΓ_germ]
    simp only [σS, CommRingCat.comp_apply]
    rw [Scheme.Hom.comp_appLE]
    rfl
  -- the end markings, read in the end charts
  have hP₀ : ∀ a, Ξ a 0 ∈ Ideal.span {MvPowerSeries.X 0} ↔
      ∀ n, (Scheme.IdealSheafData.inclusion (hZL n)).appTop.hom (a.1 n) = 0 := fun a => by
    rw [chartCoeffsHom_first_mem_span_iff hcomp hsurj hker]
    refine forall_congr' fun n => ?_
    rw [← (hmark n).1, RingHom.mem_ker]
    exact inclusion_app_resS_eq_zero_iff I (ZL n) n (hZL n)
      (by rw [hZLs n]; exact Set.singleton_subset_iff.mpr hpL0) (a.1 n)
  have hP₁ : ∀ a, Ξ a (Fin.last r) ∈ Ideal.span {MvPowerSeries.X 1} ↔
      ∀ n, (Scheme.IdealSheafData.inclusion (hZR n)).appTop.hom (a.1 n) = 0 := fun a => by
    rw [chartCoeffsHom_last_mem_span_iff hcomp hsurj hker hr]
    refine forall_congr' fun n => ?_
    rw [← (hmark n).2, RingHom.mem_ker]
    exact inclusion_app_resS_eq_zero_iff I (ZR n) n (hZR n)
      (by rw [hZRs n]; exact Set.singleton_subset_iff.mpr hpR0) (a.1 n)
  obtain ⟨m, hm, q, hq, φ, hφc, hL, hR, hLR⟩ :=
    exists_ringEquiv_cyclicInvariants_of_plumbing hr b hb Θ Ξ hΞi hΞr hc _ _ hP₀ hP₁
  refine ⟨m, hm, q, hq, φ,
    fun n => (Pi.evalRingHom _ n).comp (I.formalNeighborhoodRing.subtype.comp Θ.toRingHom),
    hφc, fun n U hyU hU s => ?_, hL, hR, hLR⟩
  change (I.completionToFormalNeighborhood f y hmaps (AdicCompletion.of _ _ _)).1 n = _
  rw [completionToFormalNeighborhood_of]
  exact Scheme.Hom.stalkToΓ_germ _ _ _ _ _ _

end

end MMP.Flips
