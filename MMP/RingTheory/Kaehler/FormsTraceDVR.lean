module

public import MMP.RingTheory.Kaehler.FormsTrace
public import MMP.RingTheory.Kaehler.TraceAdaptedBasis
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# The trace of forms over a discrete valuation ring

Let `A` be a local domain with maximal ideal `(t)`, `t ≠ 0`, with fraction field `K`, and let `B`
be a domain which is a finite free `A`-algebra, with fraction field `L ⊇ K` finite separable over
`K`. Fix a basis `(βᵢ)` of `Ω_{K/k}`; its pull-back is a basis of `Ω_{L/k}`, and the wedges of
both are bases of `Ω^p_{K/k}` and `Ω^p_{L/k}`. The trace of forms
(`MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace`) acts on coordinates in these bases as the
trace `Tr_{L/K}`. Hence, by the tame trace estimate
(`MMP.FourfoldProofs.FractionalLogComplexProof.exists_algebraMap_eq_trace_of_forall_isMaximal`), a
`p`-form `ω` of `L` such that every coordinate of `t ω` lies in the maximal ideal of `B_Q` for
every maximal ideal `Q` of `B` has a trace whose coordinates lie in `A`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_repr`: the coordinates of `Tr ω` are the
  traces of the coordinates of `ω`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_algebraMap_eq_formsTrace_repr`: the
  codimension-one regularity of the trace of forms.
-/

@[expose] public section

open KaehlerDifferential IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

section Coordinates

variable {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The pull-back to `L` of a basis of `Ω_{K/k}` is a basis of `Ω_{L/k}`. -/
noncomputable def pullbackBasis {ι : Type*} (b : Module.Basis ι K Ω[K⁄k]) :
    Module.Basis ι L Ω[L⁄k] :=
  IsBaseChange.basis b (isBaseChange_kaehler k K L)

omit [FiniteDimensional K L] in
/-- The `i`-th vector of the pulled-back basis is the pull-back of the `i`-th vector of `b`. -/
theorem pullbackBasis_apply {ι : Type*} (b : Module.Basis ι K Ω[K⁄k]) (i : ι) :
    pullbackBasis (L := L) b i = KaehlerDifferential.map k k K L (b i) :=
  IsBaseChange.basis_apply _ _ _

omit [FiniteDimensional K L] in
/-- The wedges of the pulled-back basis are the pull-backs of the wedges. -/
theorem exteriorPower_pullbackBasis_apply {ι : Type*} [LinearOrder ι]
    (b : Module.Basis ι K Ω[K⁄k]) (p : ℕ) (s : Set.powersetCard ι p) :
    (pullbackBasis (L := L) b).exteriorPower p s =
      KaehlerDifferential.mapExteriorPower k K L p (b.exteriorPower p s) := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.ιMulti_family, mapExteriorPower_ιMulti]
  congr 1
  funext i
  simp [pullbackBasis_apply]

omit [FiniteDimensional K L] in
/-- **The trace of forms in coordinates**: the coordinates of `Tr ω` in the wedges of a basis of
`Ω_{K/k}` are the traces of the coordinates of `ω` in the pulled-back wedges. -/
theorem formsTrace_repr {ι : Type*} [LinearOrder ι] [Finite ι] (b : Module.Basis ι K Ω[K⁄k])
    (p : ℕ) (ω : ⋀[L]^p (Ω[L⁄k])) (s : Set.powersetCard ι p) :
    (b.exteriorPower p).repr (formsTrace k K L p ω) s =
      Algebra.trace K L (((pullbackBasis (L := L) b).exteriorPower p).repr ω s) := by
  classical
  have := Fintype.ofFinite ι
  conv_lhs => rw [← ((pullbackBasis (L := L) b).exteriorPower p).sum_repr ω]
  simp only [map_sum, exteriorPower_pullbackBasis_apply, formsTrace_smul_mapExteriorPower,
    map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Coordinates

section LocalTrace

variable {k A K B L : Type u} [Field k] [CommRing A] [IsLocalRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K] [CommRing B] [IsDomain B] [Algebra A B] [Module.Free A B]
  [Module.Finite A B] [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [Algebra k K] [Algebra k L] [IsScalarTower k K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

omit [FiniteDimensional K L] in
/-- **Codimension-one regularity of the trace of forms.** Let `A` be a local domain with maximal
ideal `(t)`, `t ≠ 0`, and `B` a domain finite free over `A`, with fraction fields `K ⊆ L`. If
every coordinate of `t ω` in the pulled-back wedges of a basis of `Ω_{K/k}` lies in the maximal
ideal of `B_Q`, for every maximal ideal `Q` of `B`, then the `s`-th coordinate of `Tr ω` lies in
`A`. -/
theorem exists_algebraMap_eq_formsTrace_repr (hinj : Function.Injective (algebraMap A B))
    {t : A} (ht : t ≠ 0) (hm : maximalIdeal A = Ideal.span {t}) {ι : Type*} [LinearOrder ι]
    [Finite ι] (b : Module.Basis ι K Ω[K⁄k]) (p : ℕ) (ω : ⋀[L]^p (Ω[L⁄k]))
    (hω : ∀ Q : Ideal B, Q.IsMaximal → ∀ s, ∃ x ∈ Q, ∃ c ∉ Q,
      algebraMap B L c * (algebraMap A L t *
        ((pullbackBasis (L := L) b).exteriorPower p).repr ω s) = algebraMap B L x)
    (s : Set.powersetCard ι p) :
    ∃ a : A, algebraMap A K a = (b.exteriorPower p).repr (formsTrace k K L p ω) s := by
  rw [formsTrace_repr]
  exact exists_algebraMap_eq_trace_of_forall_isMaximal hinj ht hm _ fun Q hQ => hω Q hQ s

omit [IsDomain B] [IsFractionRing B L] in
/-- An element of `L` which is the image of an element of the maximal ideal of the localization
`B_Q` is a fraction `x / c` with `x ∈ Q` and `c ∉ Q`. -/
theorem exists_mul_algebraMap_eq_of_mem_maximalIdeal {Q : Ideal B} [Q.IsPrime] {R : Type*}
    [CommRing R] [Algebra B R] [IsLocalization.AtPrime R Q] [IsLocalRing R] [Algebra R L]
    [IsScalarTower B R L] {r : R} (hr : r ∈ maximalIdeal R) :
    ∃ x ∈ Q, ∃ c ∉ Q, algebraMap B L c * algebraMap R L r = algebraMap B L x := by
  obtain ⟨⟨x, c⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl r
  refine ⟨x, (IsLocalization.AtPrime.mk'_mem_maximal_iff R Q x c).1 hr, c, c.2, ?_⟩
  rw [IsScalarTower.algebraMap_apply B R L, IsScalarTower.algebraMap_apply B R L x, ← map_mul,
    mul_comm, IsLocalization.mk'_spec]

end LocalTrace

end MMP.FourfoldProofs.FractionalLogComplexProof
