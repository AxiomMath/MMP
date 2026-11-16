module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Logarithmic forms along a tamely ramified extension of discrete valuation rings

Let `k` be a field of characteristic zero and `A → B` a local homomorphism of local
`k`-algebras whose maximal ideals are principal, `𝔪_A = (t)` and `𝔪_B = (s)`, with
`t = u sᵉ` in `B`, `u` a unit and `e ≥ 1`, and with residue extension `κ_B / κ_A` separable.
Suppose `Ω_{A/k}` is free with basis `dt, dx₁, …, dxₙ` and `Ω_{B/k}` free with basis
`ds, dy₁, …, dyₙ`. Then

`ω₀ = e u ds + s du, dx₁, …, dxₙ`

is again a basis of `Ω_{B/k}`. Since `dt = s^{e-1} ω₀`, this says that the forms pulled back
from `A` generate the forms of `B` up to the expected power of `s`: on the logarithmic lattices,
`B · dt/t + ∑ B dxᵢ = B · ds/s + ∑ B dyⱼ`, the tame comparison of logarithmic differentials of
a finite cover at a branch divisor in characteristic zero.

The proof is by Nakayama's lemma. In `κ_B ⊗ Ω_{B/k}` the class of `ω₀` is `e ū (1 ⊗ ds)`, a
non-zero multiple of a basis vector, and the conormal sequence
`𝔪_B/𝔪_B² → κ_B ⊗ Ω_{B/k} → Ω_{κ_B/k} → 0` kills `1 ⊗ ds` and sends `1 ⊗ dxᵢ` to `d x̄ᵢ`. The
`d x̄ᵢ` are linearly independent in `Ω_{κ_A/k}` by the conormal sequence of `A`, and stay so in
`Ω_{κ_B/k} = κ_B ⊗ Ω_{κ_A/k}` since `κ_B / κ_A` is formally étale. So the classes of the family
are a basis of `κ_B ⊗ Ω_{B/k}`; the family spans `Ω_{B/k}` by Nakayama, and a spanning family of
the size of a basis of a free module of finite rank is a basis.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.linearIndependent_D_residue`: the differentials of
  the residues of `x₁, …, xₙ` are linearly independent in `Ω_{κ_A/k}`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_basis_tame`: `e u ds + s du, dx₁, …, dxₙ` is a
  basis of `Ω_{B/k}`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.span_log_eq`: the tame comparison of logarithmic
  lattices, `B · s⁻¹ds + ∑ B dyⱼ = B · t⁻¹dt + ∑ B dxᵢ` in `Ω_{L/k}`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.span_regular_eq`: the analogue for the regular
  lattices.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exteriorPower_repr_mem_range_of_mem_span`: wedges of
  forms with integral coordinates have integral coordinates in `⋀^p`.

## References

* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992], §3
-/

@[expose] public section

open TensorProduct KaehlerDifferential IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

section Conormal

variable (k : Type*) [Field k] {A : Type*} [CommRing A] [IsLocalRing A] [Algebra k A]

/-- The class in `κ_A ⊗ Ω_{A/k}` of the differential of an element of the maximal ideal `(t)` is a
multiple of `1 ⊗ dt`. -/
theorem exists_tmul_D_eq_smul_of_mem {t : A} (hm : maximalIdeal A = Ideal.span {t})
    {w : A} (hw : w ∈ maximalIdeal A) :
    ∃ a : ResidueField A, (1 : ResidueField A) ⊗ₜ[A] D k A w =
      a • ((1 : ResidueField A) ⊗ₜ[A] D k A t) := by
  rw [hm, Ideal.mem_span_singleton] at hw
  obtain ⟨a, rfl⟩ := hw
  refine ⟨residue A a, ?_⟩
  have ht : residue A t = 0 := (residue_eq_zero_iff t).2 (hm ▸ Ideal.mem_span_singleton_self t)
  rw [Derivation.leibniz, tmul_add, tmul_smul, tmul_smul,
    ← algebraMap_smul (ResidueField A) t, ← algebraMap_smul (ResidueField A) a]
  simp [ht]

/-- **The conormal sequence of `A → κ_A`.** If `𝔪_A = (t)` and `dt, dx₁, …, dxₙ` is a basis of
`Ω_{A/k}`, the differentials of the residues `x̄ᵢ` are linearly independent in `Ω_{κ_A/k}`. -/
theorem linearIndependent_D_residue {n : ℕ} {t : A} (hm : maximalIdeal A = Ideal.span {t})
    (x : Fin n → A) (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k])
    (hbA : ∀ i, bA i = D k A ((Fin.cons t x : Fin (n + 1) → A) i)) :
    LinearIndependent (ResidueField A) fun i => D k (ResidueField A) (residue A (x i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let b' := bA.baseChange (ResidueField A)
  set z : ResidueField A ⊗[A] Ω[A⁄k] :=
    ∑ i, g i • ((1 : ResidueField A) ⊗ₜ[A] D k A (x i)) with hz
  have hz0 : KaehlerDifferential.mapBaseChange k A (ResidueField A) z = 0 := by
    rw [hz, map_sum]
    simp only [map_smul, mapBaseChange_tmul, one_smul, map_D]
    exact hg
  obtain ⟨c, hc⟩ :=
    (exact_kerCotangentToTensor_mapBaseChange k A (ResidueField A) residue_surjective z).1 hz0
  obtain ⟨w, rfl⟩ := Ideal.toCotangent_surjective _ c
  rw [kerCotangentToTensor_toCotangent] at hc
  have hw : (w : A) ∈ maximalIdeal A := (residue_eq_zero_iff _).1 (RingHom.mem_ker.1 w.2)
  obtain ⟨a, ha⟩ := exists_tmul_D_eq_smul_of_mem k hm hw
  rw [ha] at hc
  have hli := (Fintype.linearIndependent_iff.1 b'.linearIndependent) (Fin.cons (-a) g) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, b', Module.Basis.baseChange_apply, hbA]
    rw [← hz, ← hc, neg_smul, neg_add_cancel])
  intro i
  simpa using hli i.succ

end Conormal

section BaseChange

variable {K L M N : Type*} [CommRing K] [CommRing L] [Algebra K L] [Module.Flat K L]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [Module L N] [IsScalarTower K L N]

/-- A linearly independent family stays linearly independent after a flat base change. -/
theorem _root_.LinearIndependent.map_of_isBaseChange {f : M →ₗ[K] N} (hf : IsBaseChange L f)
    {ι : Type*} {v : ι → M} (hv : LinearIndependent K v) : LinearIndependent L (f ∘ v) := by
  have h := (Module.Flat.linearIndependent_one_tmul (S := L) hv).map' hf.equiv.toLinearMap
    (LinearEquiv.ker _)
  have e : (⇑hf.equiv.toLinearMap ∘ fun x ↦ (1 : L) ⊗ₜ[K] v x) = f ∘ v := by
    funext i; simp [IsBaseChange.equiv_tmul]
  rwa [e] at h

/-- A spanning family indexed by the same finite type as a basis of a module over a commutative
ring is linearly independent. -/
theorem linearIndependent_of_span_eq_top_of_basis {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Finite ι] (b : Module.Basis ι R M) {v : ι → M}
    (hspan : Submodule.span R (Set.range v) = ⊤) : LinearIndependent R v := by
  nontriviality R
  have := Fintype.ofFinite ι
  have := Module.Finite.of_basis b
  have := Module.Free.of_basis b
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
    (Module.finrank_eq_card_basis b).symm

/-- Over a local ring, if the class of `m` in `κ ⊗ M` is a multiple of the class of the basis
vector `c i₀`, then the other coordinates of `m` lie in the maximal ideal. -/
theorem repr_mem_maximalIdeal_of_one_tmul_eq_smul {R M ι : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (c : Module.Basis ι R M) {m : M} {i₀ : ι} {a : ResidueField R}
    (h : (1 : ResidueField R) ⊗ₜ[R] m = a • ((1 : ResidueField R) ⊗ₜ[R] c i₀))
    {i : ι} (hi : i ≠ i₀) : c.repr m i ∈ maximalIdeal R := by
  classical
  have := congrArg (fun z => (c.baseChange (ResidueField R)).repr z i) h
  simp only [Module.Basis.baseChange_repr_tmul, map_smul, Finsupp.coe_smul, Pi.smul_apply,
    Module.Basis.repr_self, ne_eq, hi.symm, not_false_eq_true, Finsupp.single_eq_of_ne',
    zero_smul, smul_eq_mul, mul_zero] at this
  rw [Algebra.smul_def, mul_one] at this
  exact (residue_eq_zero_iff _).1 this

end BaseChange

section Tame

variable (k : Type*) [Field k] {A B : Type*} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B] [Algebra k A] [Algebra k B] [Algebra A B]
  [IsScalarTower k A B] [IsLocalHom (algebraMap A B)]

/-- For `s` in the maximal ideal, the class of `e u ds + s du` in `κ_B ⊗ Ω_{B/k}` is
`e ū (1 ⊗ ds)`. -/
theorem one_tmul_tame_eq {s : B} (hs : s ∈ maximalIdeal B) (u : B) (e : ℕ) :
    (1 : ResidueField B) ⊗ₜ[B] ((e : B) • u • D k B s + s • D k B u) =
      ((e : ResidueField B) * residue B u) • ((1 : ResidueField B) ⊗ₜ[B] D k B s) := by
  have h1 : algebraMap B (ResidueField B) s = 0 := (residue_eq_zero_iff s).2 hs
  simp only [tmul_add, tmul_smul]
  rw [← algebraMap_smul (ResidueField B) s, ← algebraMap_smul (ResidueField B) u,
    ← algebraMap_smul (ResidueField B) (e : B), h1, zero_smul, add_zero, smul_smul, map_natCast]
  rfl

/-- The differentials of the residues of `x₁, …, xₙ` stay linearly independent in
`Ω_{κ_B/k}`. -/
theorem linearIndependent_D_residue_algebraMap
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    {n : ℕ} {t : A} (hmA : maximalIdeal A = Ideal.span {t}) (x : Fin n → A)
    (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k])
    (hbA : ∀ i, bA i = D k A ((Fin.cons t x : Fin (n + 1) → A) i)) :
    LinearIndependent (ResidueField B) fun i =>
      D k (ResidueField B) (residue B (algebraMap A B (x i))) := by
  have := Algebra.FormallyEtale.of_isSeparable (ResidueField A) (ResidueField B)
  convert LinearIndependent.map_of_isBaseChange
    (KaehlerDifferential.isBaseChange_of_formallyEtale k (ResidueField A) (ResidueField B))
    (linearIndependent_D_residue k hmA x bA hbA) using 1
  funext i
  exact ((KaehlerDifferential.map_D k k (ResidueField A) (ResidueField B) _).trans
    (by rw [ResidueField.algebraMap_residue])).symm

/-- The classes of `e u ds + s du, dx₁, …, dxₙ` in `κ_B ⊗ Ω_{B/k}` are linearly independent. -/
theorem linearIndependent_one_tmul_tame [CharZero k]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    {n : ℕ} {t : A} (hmA : maximalIdeal A = Ideal.span {t}) (x : Fin n → A)
    (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k])
    (hbA : ∀ i, bA i = D k A ((Fin.cons t x : Fin (n + 1) → A) i))
    {s : B} (hs : s ∈ maximalIdeal B) (bB : Module.Basis (Fin (n + 1)) B Ω[B⁄k])
    (hbB : bB 0 = D k B s) {u : B} (hu : IsUnit u) {e : ℕ} (he : e ≠ 0) :
    LinearIndependent (ResidueField B) fun j => (1 : ResidueField B) ⊗ₜ[B]
      (Fin.cons ((e : B) • u • D k B s + s • D k B u) fun i => D k B (algebraMap A B (x i)) :
        Fin (n + 1) → Ω[B⁄k]) j := by
  set v : Fin (n + 1) → Ω[B⁄k] :=
    Fin.cons ((e : B) • u • D k B s + s • D k B u) fun i => D k B (algebraMap A B (x i)) with hv
  have h1 : algebraMap B (ResidueField B) s = 0 := (residue_eq_zero_iff s).2 hs
  have : CharZero (ResidueField B) :=
    charZero_of_injective_algebraMap (algebraMap k (ResidueField B)).injective
  have hκ := linearIndependent_D_residue_algebraMap k (B := B) hmA x bA hbA
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hz0 : KaehlerDifferential.mapBaseChange k B (ResidueField B)
      ((1 : ResidueField B) ⊗ₜ[B] v 0) = 0 := by
    simp only [hv, Fin.cons_zero, mapBaseChange_tmul, one_smul, map_add, map_smul,
      KaehlerDifferential.map_D]
    rw [h1, map_zero, smul_zero, smul_zero, ← algebraMap_smul (ResidueField B) s, h1, zero_smul,
      add_zero]
  have hzs : ∀ i : Fin n, KaehlerDifferential.mapBaseChange k B (ResidueField B)
      ((1 : ResidueField B) ⊗ₜ[B] v i.succ) = D k (ResidueField B)
        (residue B (algebraMap A B (x i))) := by
    intro i
    simp only [hv, Fin.cons_succ, mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
    rfl
  have hΦ := congrArg (KaehlerDifferential.mapBaseChange k B (ResidueField B)) hg
  rw [map_sum, Fin.sum_univ_succ, map_zero, map_smul, hz0, smul_zero, zero_add] at hΦ
  simp only [map_smul, hzs] at hΦ
  have hsucc : ∀ i : Fin n, g i.succ = 0 := Fintype.linearIndependent_iff.1 hκ _ hΦ
  have h0 : g 0 • ((1 : ResidueField B) ⊗ₜ[B] v 0) = 0 := by
    rw [Fin.sum_univ_succ] at hg
    simpa [hsucc] using hg
  rw [hv, Fin.cons_zero, one_tmul_tame_eq k hs u e, smul_smul] at h0
  have hne := (bB.baseChange (ResidueField B)).ne_zero 0
  rw [Module.Basis.baseChange_apply, hbB] at hne
  intro j
  refine Fin.cases ?_ hsucc j
  exact (mul_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hne)).resolve_right
    (mul_ne_zero (Nat.cast_ne_zero.2 he) (hu.map (residue B)).ne_zero)

/-- **The tame basis.** Let `A → B` be a local homomorphism of local `k`-algebras, `k` of
characteristic zero, with `𝔪_A = (t)`, `𝔪_B = (s)` and `κ_B / κ_A` separable. If
`dt, dx₁, …, dxₙ` is a basis of `Ω_{A/k}` and `ds, dy₁, …, dyₙ` a basis of `Ω_{B/k}`, then for
every unit `u` of `B` and `e ≠ 0` the forms `e u ds + s du, dx₁, …, dxₙ` are a basis of
`Ω_{B/k}`, and the coordinates of `ds` along `dx₁, …, dxₙ` in this basis lie in `𝔪_B`. -/
theorem exists_basis_tame [CharZero k] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    {n : ℕ} {t : A} (hmA : maximalIdeal A = Ideal.span {t}) (x : Fin n → A)
    (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k])
    (hbA : ∀ i, bA i = D k A ((Fin.cons t x : Fin (n + 1) → A) i))
    {s : B} (hmB : maximalIdeal B = Ideal.span {s}) (y : Fin n → B)
    (bB : Module.Basis (Fin (n + 1)) B Ω[B⁄k])
    (hbB : ∀ i, bB i = D k B ((Fin.cons s y : Fin (n + 1) → B) i))
    {u : B} (hu : IsUnit u) {e : ℕ} (he : e ≠ 0) :
    ∃ c : Module.Basis (Fin (n + 1)) B Ω[B⁄k],
      c 0 = (e : B) • u • D k B s + s • D k B u ∧
        (∀ i : Fin n, c i.succ = D k B (algebraMap A B (x i))) ∧
        ∀ i : Fin n, c.repr (D k B s) i.succ ∈ maximalIdeal B := by
  classical
  let v : Fin (n + 1) → Ω[B⁄k] :=
    Fin.cons ((e : B) • u • D k B s + s • D k B u) fun i => D k B (algebraMap A B (x i))
  have hs : s ∈ maximalIdeal B := hmB ▸ Ideal.mem_span_singleton_self s
  have hred : LinearIndependent (ResidueField B) fun j => (1 : ResidueField B) ⊗ₜ[B] v j :=
    linearIndependent_one_tmul_tame k hmA x bA hbA hs bB (by rw [hbB, Fin.cons_zero]) hu he
  have : Module.Finite B Ω[B⁄k] := Module.Finite.of_basis bB
  let bred := basisOfLinearIndependentOfCardEqFinrank hred
    (by rw [Module.finrank_eq_card_basis (bB.baseChange (ResidueField B))])
  have hspan : Submodule.span B (Set.range v) = ⊤ :=
    span_eq_top_of_tmul_eq_basis v bred fun i => by
      simp [bred, coe_basisOfLinearIndependentOfCardEqFinrank]
  let c := Module.Basis.mk (linearIndependent_of_span_eq_top_of_basis bB hspan) hspan.ge
  have hc0 : c 0 = (e : B) • u • D k B s + s • D k B u := by simp [c, v]
  refine ⟨c, hc0, fun i => by simp [c, v], fun i => ?_⟩
  have : CharZero (ResidueField B) :=
    charZero_of_injective_algebraMap (algebraMap k (ResidueField B)).injective
  have hne : (e : ResidueField B) * residue B u ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 he) (hu.map (residue B)).ne_zero
  refine repr_mem_maximalIdeal_of_one_tmul_eq_smul c
    (a := ((e : ResidueField B) * residue B u)⁻¹) ?_ (Fin.succ_ne_zero i)
  rw [hc0, one_tmul_tame_eq k hs u e, smul_smul, inv_mul_cancel₀ hne, one_smul]

end Tame

section Lattice

variable (k : Type*) [Field k] {A B L : Type*} [CommRing A] [CommRing B] [CommRing L]
  [Algebra k B] [Algebra k L] [Algebra A B] [Algebra A L] [Algebra B L]
  [IsScalarTower k B L] [IsScalarTower A B L]

/-- The pull-back of `dt` for `t = u sᵉ`: `t (e u ds + s du) = u s dt` in `Ω_{L/k}`. -/
theorem smul_D_eq_of_eq_mul_pow {t : A} {s u : B} {e : ℕ} (he : e ≠ 0)
    (hts : algebraMap A B t = u * s ^ e) :
    algebraMap A L t • KaehlerDifferential.map k k B L ((e : B) • u • D k B s + s • D k B u) =
      (algebraMap B L u * algebraMap B L s) • D k L (algebraMap A L t) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.pos_of_ne_zero he)
  rw [IsScalarTower.algebraMap_apply A B L, hts]
  simp only [map_add, map_smul, KaehlerDifferential.map_D, map_mul, map_pow, zero_add,
    Derivation.leibniz, Derivation.leibniz_pow, smul_add, smul_smul, Nat.add_sub_cancel]
  match_scalars <;> ring

/-- `t⁻¹ dt = e s⁻¹ ds + u⁻¹ du` for `t = u sᵉ`. -/
theorem inv_smul_D_eq_of_eq_mul_pow {t : A} {s u : B} {e : ℕ} (hu : IsUnit u)
    (hts : algebraMap A B t = u * s ^ e) {s' t' : L} (hs' : s' * algebraMap B L s = 1)
    (ht' : t' * algebraMap A L t = 1) :
    t' • D k L (algebraMap A L t) =
      (e : B) • s' • D k L (algebraMap B L s) +
        (↑hu.unit⁻¹ : B) • D k L (algebraMap B L u) := by
  have hu' : algebraMap B L (↑hu.unit⁻¹ : B) * algebraMap B L u = 1 := by
    rw [← map_mul, IsUnit.val_inv_mul hu, map_one]
  have hta : algebraMap A L t = algebraMap B L u * algebraMap B L s ^ e := by
    rw [IsScalarTower.algebraMap_apply A B L, hts, map_mul, map_pow]
  have ht'' : t' = algebraMap B L (↑hu.unit⁻¹ : B) * s' ^ e := by
    have h2 : (algebraMap B L (↑hu.unit⁻¹ : B) * s' ^ e) * algebraMap A L t = 1 := by
      rw [hta]
      calc _ = (algebraMap B L (↑hu.unit⁻¹ : B) * algebraMap B L u) *
          (s' * algebraMap B L s) ^ e := by ring
        _ = 1 := by rw [hu', hs', one_pow, one_mul]
    calc t' = t' * ((algebraMap B L (↑hu.unit⁻¹ : B) * s' ^ e) * algebraMap A L t) := by
            rw [h2, mul_one]
      _ = (t' * algebraMap A L t) * (algebraMap B L (↑hu.unit⁻¹ : B) * s' ^ e) := by ring
      _ = _ := by rw [ht', one_mul]
  rw [hta, ht'']
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp only [pow_zero, mul_one, Nat.cast_zero, zero_smul, zero_add, algebraMap_smul]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt he
  have hP : s' ^ e * algebraMap B L s ^ e = 1 := by rw [← mul_pow, hs', one_pow]
  simp only [Derivation.leibniz, Derivation.leibniz_pow, zero_add, Nat.add_sub_cancel]
  match_scalars
  · linear_combination (s' * ((e : L) + 1) * algebraMap B L (↑hu.unit⁻¹ : B) *
      algebraMap B L u) * hP + (s' * ((e : L) + 1)) * hu'
  · linear_combination (algebraMap B L (↑hu.unit⁻¹ : B) * s' * algebraMap B L s) * hP +
      algebraMap B L (↑hu.unit⁻¹ : B) * hs'

/-- `e u ds + s du = u s t⁻¹ dt` in `Ω_{L/k}`, for `t = u sᵉ` invertible in `L`. -/
theorem map_tame_eq {t : A} {s u : B} {e : ℕ} (he : e ≠ 0) (hts : algebraMap A B t = u * s ^ e)
    {t' : L} (ht' : t' * algebraMap A L t = 1) :
    KaehlerDifferential.map k k B L ((e : B) • u • D k B s + s • D k B u) =
      (u * s) • (t' • D k L (algebraMap A L t)) := by
  calc KaehlerDifferential.map k k B L ((e : B) • u • D k B s + s • D k B u) =
      (t' * algebraMap A L t) • KaehlerDifferential.map k k B L
        ((e : B) • u • D k B s + s • D k B u) := by rw [ht', one_smul]
    _ = t' • ((algebraMap B L u * algebraMap B L s) • D k L (algebraMap A L t)) := by
      rw [mul_smul, smul_D_eq_of_eq_mul_pow k (L := L) he hts]
    _ = _ := by
      rw [smul_smul, ← algebraMap_smul L (u * s), smul_smul, map_mul]
      congr 1
      ring

/-- The image of `Ω_{B/k}` in `Ω_{L/k}` is spanned by the image of any basis. -/
theorem map_mem_span_of_basis {ι : Type*} (b : Module.Basis ι B Ω[B⁄k])
    (ω : Ω[B⁄k]) : KaehlerDifferential.map k k B L ω ∈
      Submodule.span B (Set.range (KaehlerDifferential.map k k B L ∘ b)) := by
  rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top]
  exact LinearMap.mem_range_self _ _

/-- The `B`-span of the image in `Ω_{L/k}` of a basis of `Ω_{B/k}` does not depend on the basis. -/
theorem span_map_basis_eq {ι ι' : Type*}
    (b : Module.Basis ι B Ω[B⁄k]) (b' : Module.Basis ι' B Ω[B⁄k]) :
    Submodule.span B (Set.range (KaehlerDifferential.map k k B L ∘ b)) =
      Submodule.span B (Set.range (KaehlerDifferential.map k k B L ∘ b')) := by
  apply le_antisymm <;> rw [Submodule.span_le] <;> rintro _ ⟨j, rfl⟩
  · exact map_mem_span_of_basis k b' _
  · exact map_mem_span_of_basis k b _

/-- A `B`-submodule of `Ω_{L/k}` containing the image of a basis of `Ω_{B/k}` contains the image
of `Ω_{B/k}`. -/
theorem map_mem_of_forall_map_basis_mem {ι : Type*} (b : Module.Basis ι B Ω[B⁄k])
    {N : Submodule B Ω[L⁄k]} (hN : ∀ j, KaehlerDifferential.map k k B L (b j) ∈ N)
    (ω : Ω[B⁄k]) : KaehlerDifferential.map k k B L ω ∈ N :=
  Submodule.span_le.2 (Set.range_subset_iff.2 hN) (map_mem_span_of_basis k b ω)

/-- The pulled-back logarithmic forms `t⁻¹ dt, dx₁, …, dxₙ` of `A` lie in the `B`-span of the
logarithmic forms `s⁻¹ ds, dy₁, …, dyₙ` of `B`, for `t = u sᵉ`. -/
theorem span_log_le_of_eq_mul_pow {n : ℕ} {t : A} (x : Fin n → A) {s : B} (y : Fin n → B)
    (bB : Module.Basis (Fin (n + 1)) B Ω[B⁄k])
    (hbB : ∀ i, bB i = D k B ((Fin.cons s y : Fin (n + 1) → B) i))
    {u : B} (hu : IsUnit u) {e : ℕ} (hts : algebraMap A B t = u * s ^ e)
    {s' t' : L} (hs' : s' * algebraMap B L s = 1) (ht' : t' * algebraMap A L t = 1) :
    Submodule.span B (Set.range (Fin.cons (t' • D k L (algebraMap A L t))
        fun i => D k L (algebraMap A L (x i)) : Fin (n + 1) → Ω[L⁄k])) ≤
      Submodule.span B (Set.range (Fin.cons (s' • D k L (algebraMap B L s))
        fun j => D k L (algebraMap B L (y j)) : Fin (n + 1) → Ω[L⁄k])) := by
  set ι := KaehlerDifferential.map k k B L
  have hι : ∀ b : B, ι (D k B b) = D k L (algebraMap B L b) := fun b =>
    KaehlerDifferential.map_D k k B L b
  set S := Submodule.span B (Set.range (Fin.cons (s' • D k L (algebraMap B L s))
    fun j => D k L (algebraMap B L (y j)) : Fin (n + 1) → Ω[L⁄k]))
  have hS0 : s' • D k L (algebraMap B L s) ∈ S := Submodule.subset_span ⟨0, rfl⟩
  have hss' : ∀ z : Ω[L⁄k], s • (s' • z) = z := fun z => by
    rw [← algebraMap_smul L s, smul_smul, mul_comm, hs', one_smul]
  have hbS : ∀ j, ι (bB j) ∈ S := fun j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [hbB, Fin.cons_zero, hι, ← hss' (D k L (algebraMap B L s))]
      exact S.smul_mem _ hS0
    · rw [hbB, Fin.cons_succ, hι]
      exact Submodule.subset_span ⟨j.succ, by simp⟩
  have hιS : ∀ ω, ι ω ∈ S := map_mem_of_forall_map_basis_mem k bB hbS
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.cons_zero]
    rw [inv_smul_D_eq_of_eq_mul_pow k hu hts hs' ht']
    refine S.add_mem (S.smul_mem _ hS0) (S.smul_mem _ ?_)
    rw [← hι]
    exact hιS _
  · simp only [Fin.cons_succ]
    rw [IsScalarTower.algebraMap_apply A B L, ← hι]
    exact hιS _

/-- The logarithmic forms `s⁻¹ ds, dy₁, …, dyₙ` of `B` lie in the `B`-span of the pulled-back
logarithmic forms `t⁻¹ dt, dx₁, …, dxₙ` of `A`, given a basis `e u ds + s du, dx₁, …, dxₙ` of
`Ω_{B/k}` in which `ds` has its other coordinates in `(s)`. -/
theorem span_log_le_of_basis [IsLocalRing B] {n : ℕ} {t : A} (x : Fin n → A) {s : B}
    (hmB : maximalIdeal B = Ideal.span {s}) (y : Fin n → B) {u : B} {e : ℕ} (he : e ≠ 0)
    (hts : algebraMap A B t = u * s ^ e) (c : Module.Basis (Fin (n + 1)) B Ω[B⁄k])
    (hc0 : c 0 = (e : B) • u • D k B s + s • D k B u)
    (hcs : ∀ i : Fin n, c i.succ = D k B (algebraMap A B (x i)))
    (hcm : ∀ i : Fin n, c.repr (D k B s) i.succ ∈ maximalIdeal B)
    {s' t' : L} (hs' : s' * algebraMap B L s = 1) (ht' : t' * algebraMap A L t = 1) :
    Submodule.span B (Set.range (Fin.cons (s' • D k L (algebraMap B L s))
        fun j => D k L (algebraMap B L (y j)) : Fin (n + 1) → Ω[L⁄k])) ≤
      Submodule.span B (Set.range (Fin.cons (t' • D k L (algebraMap A L t))
        fun i => D k L (algebraMap A L (x i)) : Fin (n + 1) → Ω[L⁄k])) := by
  set ι := KaehlerDifferential.map k k B L
  have hι : ∀ b : B, ι (D k B b) = D k L (algebraMap B L b) := fun b =>
    KaehlerDifferential.map_D k k B L b
  have hxA : ∀ a : A, D k L (algebraMap A L a) = ι (D k B (algebraMap A B a)) := fun a => by
    rw [hι, ← IsScalarTower.algebraMap_apply]
  set T := Submodule.span B (Set.range (Fin.cons (t' • D k L (algebraMap A L t))
    fun i => D k L (algebraMap A L (x i)) : Fin (n + 1) → Ω[L⁄k]))
  have hT0 : t' • D k L (algebraMap A L t) ∈ T := Submodule.subset_span ⟨0, rfl⟩
  have hTs : ∀ i, D k L (algebraMap A L (x i)) ∈ T := fun i =>
    Submodule.subset_span ⟨i.succ, by simp⟩
  have hss' : ∀ z : Ω[L⁄k], s • (s' • z) = z := fun z => by
    rw [← algebraMap_smul L s, smul_smul, mul_comm, hs', one_smul]
  have hω₀ : ι (c 0) = (u * s) • (t' • D k L (algebraMap A L t)) := by
    rw [hc0]
    exact map_tame_eq k he hts ht'
  have hcT : ∀ j, ι (c j) ∈ T := fun j => by
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [hω₀]
      exact T.smul_mem _ hT0
    · rw [hcs, ← hxA]
      exact hTs i
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero]
    have hsum : D k L (algebraMap B L s) = ∑ j, c.repr (D k B s) j • ι (c j) := by
      rw [← hι]
      conv_lhs => rw [← c.sum_repr (D k B s)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
    rw [hsum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_comm]
    refine Fin.cases ?_ (fun i => ?_) j
    · refine T.smul_mem _ ?_
      rw [hω₀, smul_comm, mul_smul, hss']
      exact T.smul_mem _ hT0
    · obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 (hmB ▸ hcm i)
      rw [hq, mul_smul, smul_comm, hss', hcs, ← hxA]
      exact T.smul_mem _ (hTs i)
  · simp only [Fin.cons_succ]
    rw [← hι]
    exact map_mem_of_forall_map_basis_mem k c hcT _

variable [Algebra k A] [IsScalarTower k A B]
  [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]

/-- **The tame comparison of logarithmic lattices.** In the situation of `exists_basis_tame`, with
`t = u sᵉ`, the logarithmic forms `s⁻¹ ds, dy₁, …, dyₙ` of `B` and the pulled-back logarithmic
forms `t⁻¹ dt, dx₁, …, dxₙ` of `A` span the same `B`-submodule of `Ω_{L/k}`, for any `B`-algebra
`L` in which `s` and `t` are invertible. -/
theorem span_log_eq [CharZero k] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    {n : ℕ} {t : A} (hmA : maximalIdeal A = Ideal.span {t}) (x : Fin n → A)
    (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k])
    (hbA : ∀ i, bA i = D k A ((Fin.cons t x : Fin (n + 1) → A) i))
    {s : B} (hmB : maximalIdeal B = Ideal.span {s}) (y : Fin n → B)
    (bB : Module.Basis (Fin (n + 1)) B Ω[B⁄k])
    (hbB : ∀ i, bB i = D k B ((Fin.cons s y : Fin (n + 1) → B) i))
    {u : B} (hu : IsUnit u) {e : ℕ} (he : e ≠ 0) (hts : algebraMap A B t = u * s ^ e)
    {s' t' : L} (hs' : s' * algebraMap B L s = 1) (ht' : t' * algebraMap A L t = 1) :
    Submodule.span B (Set.range (Fin.cons (s' • D k L (algebraMap B L s))
        fun j => D k L (algebraMap B L (y j)) : Fin (n + 1) → Ω[L⁄k])) =
      Submodule.span B (Set.range (Fin.cons (t' • D k L (algebraMap A L t))
        fun i => D k L (algebraMap A L (x i)) : Fin (n + 1) → Ω[L⁄k])) := by
  obtain ⟨c, hc0, hcs, hcm⟩ := exists_basis_tame k hmA x bA hbA hmB y bB hbB hu he
  exact le_antisymm (span_log_le_of_basis k x hmB y he hts c hc0 hcs hcm hs' ht')
    (span_log_le_of_eq_mul_pow k x y bB hbB hu hts hs' ht')

/-- **The tame comparison of regular lattices.** In the situation of `span_log_eq`, the
forms `ds, dy₁, …, dyₙ` of `B` and the forms `u s t⁻¹ dt, dx₁, …, dxₙ` (so `s^{1-e} dt` in place of
`dt`) span the same `B`-submodule of `Ω_{L/k}`. -/
theorem span_regular_eq [CharZero k] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    {n : ℕ} {t : A} (hmA : maximalIdeal A = Ideal.span {t}) (x : Fin n → A)
    (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k])
    (hbA : ∀ i, bA i = D k A ((Fin.cons t x : Fin (n + 1) → A) i))
    {s : B} (hmB : maximalIdeal B = Ideal.span {s}) (y : Fin n → B)
    (bB : Module.Basis (Fin (n + 1)) B Ω[B⁄k])
    (hbB : ∀ i, bB i = D k B ((Fin.cons s y : Fin (n + 1) → B) i))
    {u : B} (hu : IsUnit u) {e : ℕ} (he : e ≠ 0) (hts : algebraMap A B t = u * s ^ e)
    {t' : L} (ht' : t' * algebraMap A L t = 1) :
    Submodule.span B (Set.range fun j => D k L (algebraMap B L
        ((Fin.cons s y : Fin (n + 1) → B) j))) =
      Submodule.span B (Set.range (Fin.cons ((u * s) • (t' • D k L (algebraMap A L t)))
        fun i => D k L (algebraMap A L (x i)) : Fin (n + 1) → Ω[L⁄k])) := by
  obtain ⟨c, hc0, hcs, -⟩ := exists_basis_tame k hmA x bA hbA hmB y bB hbB hu he
  have h1 : (fun j => D k L (algebraMap B L ((Fin.cons s y : Fin (n + 1) → B) j))) =
      KaehlerDifferential.map k k B L ∘ bB := by
    funext j
    rw [Function.comp_apply, hbB, KaehlerDifferential.map_D]
  have h2 : (Fin.cons ((u * s) • (t' • D k L (algebraMap A L t)))
      fun i => D k L (algebraMap A L (x i)) : Fin (n + 1) → Ω[L⁄k]) =
      KaehlerDifferential.map k k B L ∘ c := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [Function.comp_apply, hc0, map_tame_eq k he hts ht', Fin.cons_zero]
    · rw [Function.comp_apply, hcs, Fin.cons_succ, KaehlerDifferential.map_D,
        ← IsScalarTower.algebraMap_apply]
  rw [h1, h2]
  exact span_map_basis_eq k bB c

end Lattice

section Wedge

variable {R L M : Type*} [CommRing R] [CommRing L] [Algebra R L] [AddCommGroup M] [Module L M]
  [Module R M] [IsScalarTower R L M]

/-- A wedge of vectors of the `R`-span of `β` lies in the `R`-span of the wedges of the `β`. -/
theorem ιMulti_mem_span_of_mem {m p : ℕ} (β : Fin m → M) (w : Fin p → M)
    (hw : ∀ i, w i ∈ Submodule.span R (Set.range β)) :
    exteriorPower.ιMulti L p w ∈ Submodule.span R
      (Set.range fun f : Fin p → Fin m => exteriorPower.ιMulti L p (β ∘ f)) := by
  classical
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun R).1 (hw i)
  have hw' : w = fun i => ∑ j, algebraMap R L (c i j) • β j := by
    funext i
    rw [← hc i]
    exact Finset.sum_congr rfl fun j _ => (algebraMap_smul L _ _).symm
  have hsum := MultilinearMap.map_sum (exteriorPower.ιMulti L p).toMultilinearMap
    fun i j => algebraMap R L (c i j) • β j
  simp only [AlternatingMap.coe_multilinearMap] at hsum
  rw [hw', hsum]
  refine Submodule.sum_mem _ fun f _ => ?_
  rw [(exteriorPower.ιMulti L p).map_smul_univ (fun i => algebraMap R L (c i (f i)))
      (fun i => β (f i)), ← map_prod, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)

/-- Equal `R`-spans in degree one give equal `R`-spans of wedges in every degree. -/
theorem span_ιMulti_eq_of_span_eq {m m' p : ℕ} {β : Fin m → M} {β' : Fin m' → M}
    (h : Submodule.span R (Set.range β) = Submodule.span R (Set.range β')) :
    Submodule.span R (Set.range fun f : Fin p → Fin m => exteriorPower.ιMulti L p (β ∘ f)) =
      Submodule.span R (Set.range fun f : Fin p → Fin m' =>
        exteriorPower.ιMulti L p (β' ∘ f)) := by
  apply le_antisymm <;> rw [Submodule.span_le] <;> rintro _ ⟨f, rfl⟩
  · exact ιMulti_mem_span_of_mem β' _ fun i => h ▸ Submodule.subset_span ⟨f i, rfl⟩
  · exact ιMulti_mem_span_of_mem β _ fun i => h.symm ▸ Submodule.subset_span ⟨f i, rfl⟩

omit [Module R M] [IsScalarTower R L M] in
/-- **Coordinates of integral wedges.** Let `b` be a basis of the `L`-module `M`, `R → L`. If
every vector `w i` has its `b`-coordinates in (the image of) `R`, so do the coordinates of
`w₁ ∧ ⋯ ∧ w_p` in the basis of `⋀^p M` induced by `b`. -/
theorem exteriorPower_repr_ιMulti_mem_range {ι : Type*} [LinearOrder ι] (b : Module.Basis ι L M)
    {p : ℕ} (w : Fin p → M) (hw : ∀ i j, b.repr (w i) j ∈ (algebraMap R L).range)
    (s : Set.powersetCard ι p) :
    (b.exteriorPower p).repr (exteriorPower.ιMulti L p w) s ∈ (algebraMap R L).range := by
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  choose c hc using fun i j => hw i (Set.powersetCard.ofFinEmbEquiv.symm s j)
  have : (Matrix.of fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (w i)) =
      (Matrix.of c).map (algebraMap R L) := by
    ext i j
    simp [hc]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact ⟨_, rfl⟩

/-- **Coordinates of the lattice spanned by integral wedges.** If every `1`-form of the
`R`-submodule `N` of `M` has its `b`-coordinates in `R`, then every element of the `R`-span of the
`p`-fold wedges of elements of `N` has its coordinates in `R` in the induced basis of `⋀^p M`. -/
theorem exteriorPower_repr_mem_range_of_mem_span {ι : Type*} [LinearOrder ι]
    (b : Module.Basis ι L M) {p : ℕ} (N : Submodule R M)
    (hN : ∀ v ∈ N, ∀ j, b.repr v j ∈ (algebraMap R L).range) {ω : ⋀[L]^p M}
    (hω : ω ∈ Submodule.span R {η | ∃ w : Fin p → M, (∀ i, w i ∈ N) ∧
      η = exteriorPower.ιMulti L p w})
    (s : Set.powersetCard ι p) :
    (b.exteriorPower p).repr ω s ∈ (algebraMap R L).range := by
  induction hω using Submodule.span_induction with
  | mem η hη =>
    obtain ⟨w, hwN, rfl⟩ := hη
    exact exteriorPower_repr_ιMulti_mem_range b w (fun i j => hN _ (hwN i) j) s
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, Finsupp.add_apply]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul L a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ ⟨a, rfl⟩ hx

end Wedge

end MMP.FourfoldProofs.FractionalLogComplexProof
