module

public import StacksFrontier.RingTheory.DeRham.PolynomialHomotopy
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Defs

/-!
# The trace of differential forms along a finite separable field extension

Let `k ⊆ K ⊆ L` be fields with `L / K` finite separable. Then `L / K` is formally étale, so
`Ω_{L/k} = L ⊗_K Ω_{K/k}` and, taking exterior powers, `Ω^p_{L/k} = L ⊗_K Ω^p_{K/k}`. The
*trace of forms* `Tr : Ω^p_{L/k} → Ω^p_{K/k}` is `Tr_{L/K} ⊗ id`: it is `K`-linear and
characterized by `Tr(b · ω) = Tr_{L/K}(b) · ω` for `b ∈ L` and `ω ∈ Ω^p_{K/k}` (forms of `K` are
read in `L` through the pull-back `KaehlerDifferential.mapExteriorPower`).

The trace of forms commutes with the de Rham differentials. In degree zero this is the identity
`Tr_{L/K}(δ b) = δ(Tr_{L/K} b)` for every derivation `δ` of `L` preserving `K`: for a `K`-basis
`(eᵢ)` of `L` write `b eᵢ = ∑ⱼ Aⱼᵢ eⱼ` and `δ eᵢ = ∑ⱼ Gⱼᵢ eⱼ`; applying `δ` gives
`M_{δ b} = δ(A) + [G, A]`, and the trace of a commutator vanishes. A `K`-linear form `φ` on
`Ω_{K/k}` gives the derivation `φ ∘ d` of `K`, which extends to `L` through `φ ⊗ id`, so the
identity reads `Tr(d b) = d Tr(b)` in `Ω_{K/k}`; the general degree follows on the generators
`b · d c₁ ∧ ⋯ ∧ d c_p`, `cᵢ ∈ K`. The trace is also linear for the wedge product with forms of
`K`: `Tr(η ∧ α) = Tr(η) ∧ α`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace`: `Tr : Ω^p_{L/k} → Ω^p_{K/k}`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.trace_map_of_leibniz`: `δ (Tr x) = Tr (δ x)` for a
  derivation-like map `δ` of a finite free algebra.
* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_smul_mapExteriorPower`:
  `Tr(b · ω) = Tr_{L/K}(b) · ω`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_mapExteriorPower`: `Tr(ω) = [L : K] ω` for
  a form of `K`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_deRhamDifferential`: `Tr ∘ d = d ∘ Tr`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_ιMulti_cons_map`: `Tr(η ∧ α) = Tr(η) ∧ α`
  for a `1`-form `η` of `L` and forms `α` of `K`.

## References

* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992], §3
-/

@[expose] public section

open TensorProduct KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

/-! ### The trace of a derivation -/

section DerivationTrace

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The trace of a free finite algebra in terms of the coordinates of a basis:
`Tr x = ∑ᵢ (x eᵢ)ᵢ`. -/
theorem trace_eq_sum_repr {ι : Type*} [Fintype ι] (b : Module.Basis ι R S)
    (x : S) : Algebra.trace R S x = ∑ i, b.repr (x * b i) i := by
  classical
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rfl

/-- **The trace commutes with derivations.** Let `S` be a finite free `R`-algebra, `δ : R → R`
additive and `D : S → S` additive with `D (c x) = δ(c) x + c D(x)` and the Leibniz rule. Then
`δ (Tr x) = Tr (D x)`. -/
theorem trace_map_of_leibniz [Module.Free R S] [Module.Finite R S] (δ : R →+ R) (D : S →+ S)
    (hsmul : ∀ (c : R) (x : S), D (c • x) = δ c • x + c • D x)
    (hmul : ∀ x y : S, D (x * y) = D x * y + x * D y) (x : S) :
    δ (Algebra.trace R S x) = Algebra.trace R S (D x) := by
  classical
  let b := Module.Free.chooseBasis R S
  let A : _ → _ → R := fun i j => b.repr (x * b j) i
  let G : _ → _ → R := fun i j => b.repr (D (b j)) i
  have key : ∀ j, b.repr (D x * b j) j + ∑ l, G l j * A j l =
      δ (A j j) + ∑ i, A i j * G j i := by
    intro j
    have h1 : D (x * b j) = D (∑ i, A i j • b i) := congrArg D (b.sum_repr (x * b j)).symm
    rw [hmul, map_sum] at h1
    have h2 : x * D (b j) = ∑ l, G l j • (x * b l) := by
      rw [← b.sum_repr (D (b j)), Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => mul_smul_comm _ _ _
    rw [h2] at h1
    have h3 := congrArg (fun y => b.repr y j) h1
    simp only [map_add, map_sum, map_smul, Finsupp.add_apply, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, hsmul, b.repr_self] at h3
    rw [h3, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [hij]
      · simp
  rw [trace_eq_sum_repr b, trace_eq_sum_repr b, map_sum]
  have hsum := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => key j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hswap : ∑ j, ∑ l, G l j * A j l = ∑ j, ∑ i, A i j * G j i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hswap] at hsum
  exact (add_right_cancel hsum).symm

end DerivationTrace

/-- A property of the target of a base change `N = S ⊗_R M` holding for `0`, for the products
`s · f m`, and stable under sums, holds everywhere. -/
theorem isBaseChange_induction {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (h : IsBaseChange S f) {P : N → Prop} (h0 : P 0)
    (hgen : ∀ (s : S) (m : M), P (s • f m)) (hadd : ∀ x y, P x → P y → P (x + y)) (x : N) :
    P x := by
  obtain ⟨t, rfl⟩ := h.equiv.surjective x
  induction t using TensorProduct.induction_on with
  | zero => rwa [map_zero]
  | tmul s m => rw [IsBaseChange.equiv_tmul]; exact hgen s m
  | add t t' ht ht' => rw [map_add]; exact hadd _ _ ht ht'

/-! ### The trace of forms -/

section FormsTrace

universe u

variable (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

omit [FiniteDimensional K L] in
/-- `Ω_{L/k} = L ⊗_K Ω_{K/k}` for a finite separable extension `L / K`. -/
theorem isBaseChange_kaehler : IsBaseChange L (KaehlerDifferential.map k k K L) :=
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  KaehlerDifferential.isBaseChange_of_formallyEtale k K L

omit [FiniteDimensional K L] in
/-- `Ω^p_{L/k} = L ⊗_K Ω^p_{K/k}` for a finite separable extension `L / K`. -/
theorem isBaseChange_mapExteriorPower (p : ℕ) :
    IsBaseChange L (KaehlerDifferential.mapExteriorPower k K L p) :=
  DeRhamBaseChange.isBaseChange_exteriorPower (isBaseChange_kaehler k K L) _
    (fun v => KaehlerDifferential.mapExteriorPower_ιMulti k K L p v)

/-- **The trace of forms** `Tr = Tr_{L/K} ⊗ id : Ω^p_{L/k} = L ⊗_K Ω^p_{K/k} → Ω^p_{K/k}`. -/
noncomputable def formsTrace (p : ℕ) : ⋀[L]^p (Ω[L⁄k]) →ₗ[K] ⋀[K]^p (Ω[K⁄k]) :=
  (TensorProduct.lid K _).toLinearMap ∘ₗ
    LinearMap.rTensor _ (Algebra.trace K L) ∘ₗ
      ((isBaseChange_mapExteriorPower k K L p).equiv.symm.toLinearMap.restrictScalars K)

variable {k K L}

omit [FiniteDimensional K L] in
/-- `Tr(b · ω) = Tr_{L/K}(b) · ω` for `b ∈ L` and a form `ω` of `K`. -/
theorem formsTrace_smul_mapExteriorPower (p : ℕ) (b : L) (ω : ⋀[K]^p (Ω[K⁄k])) :
    formsTrace k K L p (b • KaehlerDifferential.mapExteriorPower k K L p ω) =
      Algebra.trace K L b • ω := by
  have h := (isBaseChange_mapExteriorPower k K L p).equiv_tmul b ω
  simp only [formsTrace, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.coe_restrictScalars]
  rw [← h, LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

/-- `Tr(ω) = [L : K] · ω` for a form `ω` of `K`. -/
theorem formsTrace_mapExteriorPower (p : ℕ) (ω : ⋀[K]^p (Ω[K⁄k])) :
    formsTrace k K L p (KaehlerDifferential.mapExteriorPower k K L p ω) =
      Module.finrank K L • ω := by
  have h := formsTrace_smul_mapExteriorPower (L := L) p 1 ω
  rw [one_smul] at h
  rw [h, ← map_one (algebraMap K L), Algebra.trace_algebraMap, smul_assoc, one_smul]

omit [FiniteDimensional K L] in
/-- A property of forms of `L` holding for `0`, for the products `b · ω` with `ω` a form of `K`,
and stable under sums, holds for every form of `L`. -/
theorem smul_mapExteriorPower_induction (p : ℕ) {P : ⋀[L]^p (Ω[L⁄k]) → Prop} (h0 : P 0)
    (hgen : ∀ (b : L) (ω : ⋀[K]^p (Ω[K⁄k])),
      P (b • KaehlerDifferential.mapExteriorPower k K L p ω))
    (hadd : ∀ x y, P x → P y → P (x + y)) (x : ⋀[L]^p (Ω[L⁄k])) : P x :=
  isBaseChange_induction (isBaseChange_mapExteriorPower k K L p) h0 hgen hadd x

/-- The trace of `1`-forms `Tr_{L/K} ⊗ id : Ω_{L/k} = L ⊗_K Ω_{K/k} → Ω_{K/k}`. -/
noncomputable def formsTraceOne : Ω[L⁄k] →ₗ[K] Ω[K⁄k] :=
  (TensorProduct.lid K _).toLinearMap ∘ₗ
    LinearMap.rTensor _ (Algebra.trace K L) ∘ₗ
      ((isBaseChange_kaehler k K L).equiv.symm.toLinearMap.restrictScalars K)

omit [FiniteDimensional K L] in
/-- `Tr(b · ω) = Tr_{L/K}(b) · ω` for `b ∈ L` and a `1`-form `ω` of `K`. -/
theorem formsTraceOne_smul_map (b : L) (ω : Ω[K⁄k]) :
    formsTraceOne (b • KaehlerDifferential.map k k K L ω) = Algebra.trace K L b • ω := by
  have h := (isBaseChange_kaehler k K L).equiv_tmul b ω
  simp only [formsTraceOne, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.coe_restrictScalars]
  rw [← h, LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

omit [FiniteDimensional K L] in
/-- A property of `1`-forms of `L` holding for `0`, for the products `b · ω` with `ω` a `1`-form
of `K`, and stable under sums, holds for every `1`-form of `L`. -/
theorem smul_map_induction {P : Ω[L⁄k] → Prop} (h0 : P 0)
    (hgen : ∀ (b : L) (ω : Ω[K⁄k]), P (b • KaehlerDifferential.map k k K L ω))
    (hadd : ∀ x y, P x → P y → P (x + y)) (x : Ω[L⁄k]) : P x :=
  isBaseChange_induction (isBaseChange_kaehler k K L) h0 hgen hadd x

/-- **The trace of the differential of a function**: `Tr(d b) = d Tr_{L/K}(b)` in `Ω_{K/k}`. -/
theorem formsTraceOne_D (b : L) :
    formsTraceOne (KaehlerDifferential.D k L b) =
      KaehlerDifferential.D k K (Algebra.trace K L b) := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff K _).1 fun φ => ?_)
  rw [map_sub, sub_eq_zero]
  let φL : Ω[L⁄k] →ₗ[L] L := (isBaseChange_kaehler k K L).lift
    ((Algebra.linearMap K L).comp φ)
  have hφL : ∀ (c : L) (ω : Ω[K⁄k]),
      φL (c • KaehlerDifferential.map k k K L ω) = c * algebraMap K L (φ ω) := by
    intro c ω
    rw [map_smul, IsBaseChange.lift_eq]
    rfl
  have hφT : ∀ η : Ω[L⁄k], φ (formsTraceOne η) = Algebra.trace K L (φL η) := by
    intro η
    refine smul_map_induction (K := K) (P := fun η => φ (formsTraceOne η) = Algebra.trace K L (φL η))
      (by simp) (fun c ω => ?_) (fun η₁ η₂ h₁ h₂ => ?_) η
    · rw [formsTraceOne_smul_map, hφL, map_smul, smul_eq_mul, mul_comm c, ← Algebra.smul_def,
        map_smul, smul_eq_mul, mul_comm]
    · simp only [map_add, h₁, h₂]
  let δ : K →+ K := AddMonoidHom.mk' (fun c => φ (KaehlerDifferential.D k K c))
    (fun a b => by rw [map_add, map_add])
  let DL : L →+ L := AddMonoidHom.mk' (fun c => φL (KaehlerDifferential.D k L c))
    (fun a b => by rw [map_add, map_add])
  have hsmul : ∀ (c : K) (x : L), DL (c • x) = δ c • x + c • DL x := by
    intro c x
    simp only [DL, δ, AddMonoidHom.mk'_apply]
    have h1 := hφL 1 (KaehlerDifferential.D k K c)
    rw [one_smul, one_mul] at h1
    rw [Algebra.smul_def, Derivation.leibniz, ← KaehlerDifferential.map_D k k K L c, map_add,
      map_smul, map_smul, h1, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def,
      add_comm, mul_comm x]
  have hmul : ∀ x y : L, DL (x * y) = DL x * y + x * DL y := by
    intro x y
    simp only [DL, AddMonoidHom.mk'_apply]
    rw [Derivation.leibniz, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, add_comm,
      mul_comm y]
  have := trace_map_of_leibniz δ DL hsmul hmul b
  simp only [δ, DL, AddMonoidHom.mk'_apply] at this
  rw [hφT, this]

/-- `ιMulti (η, v₁, …, v_p)` is additive and `L`-homogeneous in `η`. -/
theorem ιMulti_cons_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (p : ℕ)
    (b : R) (η : M) (v : Fin p → M) :
    exteriorPower.ιMulti R (p + 1) (Fin.cons (b • η) v) =
      b • exteriorPower.ιMulti R (p + 1) (Fin.cons η v) := by
  have := (exteriorPower.ιMulti R (p + 1)).map_update_smul (Fin.cons η v) 0 b η
  rwa [Fin.update_cons_zero, Fin.update_cons_zero] at this

/-- `ιMulti (η + η', v₁, …, v_p) = ιMulti (η, v₁, …, v_p) + ιMulti (η', v₁, …, v_p)`. -/
theorem ιMulti_cons_add {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (p : ℕ)
    (η η' : M) (v : Fin p → M) :
    exteriorPower.ιMulti R (p + 1) (Fin.cons (η + η') v) =
      exteriorPower.ιMulti R (p + 1) (Fin.cons η v) +
        exteriorPower.ιMulti R (p + 1) (Fin.cons η' v) := by
  have := (exteriorPower.ιMulti R (p + 1)).map_update_add (Fin.cons η v) 0 η η'
  rwa [Fin.update_cons_zero, Fin.update_cons_zero, Fin.update_cons_zero] at this

omit [FiniteDimensional K L] in
/-- **The trace is linear for forms of `K`**: `Tr(η ∧ v₁ ∧ ⋯ ∧ v_p) = Tr(η) ∧ v₁ ∧ ⋯ ∧ v_p` for a
`1`-form `η` of `L` and `1`-forms `vᵢ` of `K`. -/
theorem formsTrace_ιMulti_cons_map (p : ℕ) (η : Ω[L⁄k]) (v : Fin p → Ω[K⁄k]) :
    formsTrace k K L (p + 1) (exteriorPower.ιMulti L (p + 1)
        (Fin.cons η fun i => KaehlerDifferential.map k k K L (v i))) =
      exteriorPower.ιMulti K (p + 1) (Fin.cons (formsTraceOne η) v) := by
  refine smul_map_induction (K := K) (P := fun η => formsTrace k K L (p + 1)
      (exteriorPower.ιMulti L (p + 1)
        (Fin.cons η fun i => KaehlerDifferential.map k k K L (v i))) =
      exteriorPower.ιMulti K (p + 1) (Fin.cons (formsTraceOne η) v)) ?_ ?_ ?_ η
  · rw [(exteriorPower.ιMulti L (p + 1)).map_coord_zero 0 rfl, map_zero, map_zero,
      (exteriorPower.ιMulti K (p + 1)).map_coord_zero 0 rfl]
  · intro b ω
    have hm : (Fin.cons (KaehlerDifferential.map k k K L ω)
        fun i => KaehlerDifferential.map k k K L (v i) : Fin (p + 1) → Ω[L⁄k]) =
        fun i => KaehlerDifferential.map k k K L ((Fin.cons ω v : Fin (p + 1) → Ω[K⁄k]) i) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [ιMulti_cons_smul, hm, ← KaehlerDifferential.mapExteriorPower_ιMulti,
      formsTrace_smul_mapExteriorPower, formsTraceOne_smul_map]
    exact (ιMulti_cons_smul p _ ω v).symm
  · intro η₁ η₂ h₁ h₂
    rw [ιMulti_cons_add, map_add, h₁, h₂, map_add, ιMulti_cons_add]

/-- `Tr ∘ d = d ∘ Tr` on the generators `b · c₀ dc₁ ∧ ⋯ ∧ dc_p` of the forms of `L`. -/
theorem formsTrace_deRhamDifferential_smul_ιMulti_D (p : ℕ) (b : L) (c : Fin (p + 1) → K) :
    formsTrace k K L (p + 1) (KaehlerDifferential.deRhamDifferential (A := k) p
      (b • KaehlerDifferential.mapExteriorPower k K L p
        (c 0 • exteriorPower.ιMulti K p fun i => KaehlerDifferential.D k K (c i.succ)))) =
      KaehlerDifferential.deRhamDifferential (A := k) p (formsTrace k K L p
        (b • KaehlerDifferential.mapExteriorPower k K L p
          (c 0 • exteriorPower.ιMulti K p fun i => KaehlerDifferential.D k K (c i.succ)))) := by
  set x : L := b * algebraMap K L (c 0)
  set y : Fin p → L := fun i => algebraMap K L (c i.succ)
  have hy' : (exteriorPower.ιMulti L p fun i => KaehlerDifferential.D k L (y i)) =
      KaehlerDifferential.mapExteriorPower k K L p
        (exteriorPower.ιMulti K p fun i => KaehlerDifferential.D k K (c i.succ)) := by
    rw [KaehlerDifferential.mapExteriorPower_ιMulti]
    simp only [y, KaehlerDifferential.map_D]
  have hgen : b • KaehlerDifferential.mapExteriorPower k K L p
      (c 0 • exteriorPower.ιMulti K p fun i => KaehlerDifferential.D k K (c i.succ)) =
      x • exteriorPower.ιMulti L p fun i => KaehlerDifferential.D k L (y i) := by
    rw [hy', map_smul, ← algebraMap_smul L (c 0), smul_smul]
  have hd : KaehlerDifferential.deRhamDifferential (A := k) p
      (x • exteriorPower.ιMulti L p fun i => KaehlerDifferential.D k L (y i)) =
      exteriorPower.ιMulti L (p + 1) (Fin.cons (KaehlerDifferential.D k L x)
        fun i => KaehlerDifferential.map k k K L (KaehlerDifferential.D k K (c i.succ))) := by
    have := KaehlerDifferential.deRhamDifferential_smul_ιMulti_D (A := k) p
      (Fin.cons x y : Fin (p + 1) → L)
    simp only [Fin.cons_zero, Fin.cons_succ] at this
    rw [this]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [y, KaehlerDifferential.map_D]
  have htr : formsTrace k K L p
      (x • exteriorPower.ιMulti L p fun i => KaehlerDifferential.D k L (y i)) =
      Algebra.trace K L x •
        exteriorPower.ιMulti K p fun i => KaehlerDifferential.D k K (c i.succ) := by
    rw [hy', formsTrace_smul_mapExteriorPower]
  rw [hgen, hd, formsTrace_ιMulti_cons_map, formsTraceOne_D, htr]
  have h3 := KaehlerDifferential.deRhamDifferential_smul_ιMulti_D (A := k) p
    (Fin.cons (Algebra.trace K L x) (fun i => c i.succ) : Fin (p + 1) → K)
  simp only [Fin.cons_zero, Fin.cons_succ] at h3
  rw [h3]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- **The trace of forms commutes with the de Rham differential**: `Tr(dω) = d Tr(ω)`. -/
theorem formsTrace_deRhamDifferential (p : ℕ) (ω : ⋀[L]^p (Ω[L⁄k])) :
    formsTrace k K L (p + 1) (KaehlerDifferential.deRhamDifferential (A := k) p ω) =
      KaehlerDifferential.deRhamDifferential (A := k) p (formsTrace k K L p ω) := by
  refine smul_mapExteriorPower_induction (K := K) p (P := fun ω => formsTrace k K L (p + 1)
      (KaehlerDifferential.deRhamDifferential (A := k) p ω) =
      KaehlerDifferential.deRhamDifferential (A := k) p (formsTrace k K L p ω)) ?_ ?_ ?_ ω
  · simp only [map_zero]
  · intro b θ
    have hθ : θ ∈ Submodule.span k (Set.range fun c : Fin (p + 1) → K =>
        c 0 • exteriorPower.ιMulti K p fun i => KaehlerDifferential.D k K (c i.succ)) := by
      rw [Crystalline.span_range_smul_ιMulti_eq_top (R := k) (KaehlerDifferential.D k K)
        (KaehlerDifferential.span_range_derivation k K) p]
      trivial
    revert b
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hθ
    · rintro _ ⟨c, rfl⟩ b
      exact formsTrace_deRhamDifferential_smul_ιMulti_D p b c
    · intro b
      simp only [map_zero, smul_zero]
    · intro θ θ' _ _ h h' b
      rw [map_add, smul_add, map_add, map_add, h, h', map_add, map_add]
    · intro a θ _ h b
      have e : b • KaehlerDifferential.mapExteriorPower k K L p (a • θ) =
          (b * algebraMap K L (algebraMap k K a)) •
            KaehlerDifferential.mapExteriorPower k K L p θ := by
        rw [← algebraMap_smul K a θ, map_smul, ← algebraMap_smul L (algebraMap k K a), smul_smul]
      rw [e]
      exact h _
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, map_add, map_add]

end FormsTrace

end MMP.FourfoldProofs.FractionalLogComplexProof
