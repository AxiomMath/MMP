module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Points of a finite algebra over a polynomial ring

Let `k` be an algebraically closed field, `A` a finitely generated `k`-algebra and
`g : k[x₁, …, xₛ] → A` a finite injective `k`-algebra map (a Noether normalization). A `k`-point
`ψ : A → k` of `A` lies over the point `π(ψ) = (ψ(g xᵢ))ᵢ ∈ kˢ`. This file collects the
algebraic facts about this projection used to show that the regular points of a complex variety
are dense in the classical topology:

* every maximal ideal of `A` is the kernel of a `k`-point (Nullstellensatz);
* *lying over*: if `A` is a domain and `a ∈ A`, every root `t` of the minimal polynomial of `a`
  over `k[x]`, specialised at `z ∈ kˢ`, is the value `ψ(a)` of a point `ψ` over `z`;
* the fibres of `π` are finite, and one element `a ∈ A` separates the points of a fibre.

## Main results

* `MMP.RegularPartDense.exists_algHom_ker_eq`: the Nullstellensatz.
* `MMP.RegularPartDense.exists_algHom_lyingOver`: lying over.
* `MMP.RegularPartDense.finite_fibre`,
  `MMP.RegularPartDense.exists_separating`: fibres are finite and separated by a
  single element.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [I. R. Shafarevich, *Basic Algebraic Geometry 1*], Chapter II, §5.
-/

@[expose] public noncomputable section

open Polynomial

namespace MMP.RegularPartDense

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- **Nullstellensatz.** Every maximal ideal of a finitely generated algebra over an
algebraically closed field `k` is the kernel of a `k`-point. -/
theorem exists_algHom_ker_eq [IsAlgClosed k] [Algebra.FiniteType k A] (Q : Ideal A)
    [Q.IsMaximal] : ∃ ψ : A →ₐ[k] k, ∀ x, ψ x = 0 ↔ x ∈ Q := by
  let : Field (A ⧸ Q) := Ideal.Quotient.field Q
  have : Module.Finite k (A ⧸ Q) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ Q)
  let e : k ≃ₐ[k] A ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ Q))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k Q), fun x ↦ ?_⟩
  simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h ↦ by simpa using congrArg e h, fun h ↦ by simp [h]⟩

section Projection

variable {σ : Type*} [Algebra (MvPolynomial σ k) A] [IsScalarTower k (MvPolynomial σ k) A]

variable (σ) in
/-- The projection of a `k`-point `ψ` of an algebra `A` over `k[xᵢ]` to `kˢ`: the point
`(ψ(xᵢ))ᵢ` over which `ψ` lies. -/
def proj (ψ : A →ₐ[k] k) : σ → k :=
  fun i ↦ ψ (algebraMap (MvPolynomial σ k) A (MvPolynomial.X i))

/-- A `k`-point `ψ` of `A` restricts on `k[xᵢ]` to evaluation at `proj σ ψ`. -/
theorem apply_algebraMap (ψ : A →ₐ[k] k) (r : MvPolynomial σ k) :
    ψ (algebraMap (MvPolynomial σ k) A r) = MvPolynomial.eval (proj σ ψ) r := by
  have : ψ.comp (IsScalarTower.toAlgHom k (MvPolynomial σ k) A) =
      MvPolynomial.aeval (proj σ ψ) :=
    MvPolynomial.algHom_ext fun i ↦ by simp [proj]
  rw [← MvPolynomial.coe_aeval_eq_eval, ← this]
  rfl

/-- The value of `ψ` on `p(x)`, for a polynomial `p` over `k[xᵢ]`, is the value at `ψ(x)` of `p`
specialised at `proj σ ψ`. -/
theorem apply_aeval (ψ : A →ₐ[k] k) (p : (MvPolynomial σ k)[X]) (x : A) :
    ψ (aeval x p) = (p.map (MvPolynomial.eval (proj σ ψ))).eval (ψ x) := by
  rw [aeval_def, eval_map, ← ψ.coe_toRingHom, hom_eval₂]
  congr 1
  ext r <;> simp [apply_algebraMap]

/-- **Lying over.** Let `A` be a domain, integral and torsion-free over `k[xᵢ]`, and finitely
generated over the algebraically closed field `k`. If `t` is a root of the minimal polynomial of
`a ∈ A` over `k[xᵢ]` specialised at `z ∈ kˢ`, then some `k`-point `ψ` of `A` over `z` has
`ψ(a) = t`. -/
theorem exists_algHom_lyingOver [IsAlgClosed k] [Algebra.FiniteType k A] [IsDomain A]
    [IsIntegrallyClosed (MvPolynomial σ k)] [Algebra.IsIntegral (MvPolynomial σ k) A]
    [Module.IsTorsionFree (MvPolynomial σ k) A] (a : A) (z : σ → k) (t : k)
    (ht : ((minpoly (MvPolynomial σ k) a).map (MvPolynomial.eval z)).eval t = 0) :
    ∃ ψ : A →ₐ[k] k, proj σ ψ = z ∧ ψ a = t := by
  set R := MvPolynomial σ k
  set R' := Algebra.adjoin R ({a} : Set A)
  let e := minpoly.equivAdjoin (Algebra.IsIntegral.isIntegral (R := R) a)
  have ht' : eval₂ (MvPolynomial.eval z) t (minpoly R a) = 0 := by rwa [← eval_map]
  let χ : R' →+* k := (AdjoinRoot.lift (MvPolynomial.eval z) t ht').comp
    (e.symm : R' →ₐ[R] AdjoinRoot (minpoly R a)).toRingHom
  have hχR : ∀ r : R, χ (algebraMap R R' r) = MvPolynomial.eval z r := by
    intro r
    change AdjoinRoot.lift (MvPolynomial.eval z) t ht' (e.symm (algebraMap R R' r)) = _
    rw [AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
  have hχa : χ ⟨a, Algebra.self_mem_adjoin_singleton R a⟩ = t := by
    have : e.symm ⟨a, Algebra.self_mem_adjoin_singleton R a⟩ = AdjoinRoot.root _ := by
      rw [AlgEquiv.symm_apply_eq]
      apply Subtype.ext
      simp [e, minpoly.equivAdjoin, AdjoinRoot.Minpoly.toAdjoin]
    change AdjoinRoot.lift (MvPolynomial.eval z) t ht' (e.symm _) = _
    rw [this, AdjoinRoot.lift_root]
  have hχsurj : Function.Surjective χ := fun c ↦
    ⟨algebraMap R R' (MvPolynomial.C c), by rw [hχR, MvPolynomial.eval_C]⟩
  have hP : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hχsurj
  have : Algebra.IsIntegral R' A := Algebra.IsIntegral.tower_top R
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker χ)
    (⊥ : Ideal A) fun y hy ↦ by
      rw [RingHom.mem_ker, show y = 0 from Subtype.ext (hy : (y : A) = 0), map_zero]
  have : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R') Q (hQ ▸ hP)
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq (k := k) Q
  have key : ∀ y : R', χ y = 0 → ψ y = 0 := fun y hy ↦
    (hψ _).2 (show y ∈ Q.under R' from hQ ▸ hy)
  have hconst : ∀ c : k, ψ (algebraMap R A (MvPolynomial.C c)) = c := by
    intro c
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    rfl
  refine ⟨ψ, funext fun i ↦ ?_, ?_⟩
  · have h := key (algebraMap R R' (MvPolynomial.X i - MvPolynomial.C (z i)))
      (by simp [hχR])
    rwa [show ((algebraMap R R' (MvPolynomial.X i - MvPolynomial.C (z i)) : R') : A) =
      algebraMap R A (MvPolynomial.X i - MvPolynomial.C (z i)) from rfl, map_sub, map_sub,
      hconst, sub_eq_zero] at h
  · have h := key (⟨a, Algebra.self_mem_adjoin_singleton R a⟩ -
      algebraMap R R' (MvPolynomial.C t)) (by simp [hχR, hχa])
    rwa [show ((⟨a, Algebra.self_mem_adjoin_singleton R a⟩ - algebraMap R R' (MvPolynomial.C t) :
      R') : A) = a - algebraMap R A (MvPolynomial.C t) from rfl, map_sub, hconst,
      sub_eq_zero] at h

/-- The fibres of the projection `proj σ` of the `k`-points of a finitely generated algebra `A`,
integral over `k[xᵢ]`, are finite. -/
theorem finite_fibre [Algebra.FiniteType k A] [Algebra.IsIntegral (MvPolynomial σ k) A]
    (z : σ → k) : {ψ : A →ₐ[k] k | proj σ ψ = z}.Finite := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  let f : (A →ₐ[k] k) → s → k := fun ψ x ↦ ψ x
  have hinj : Set.InjOn f (f ⁻¹' Set.univ.pi fun x : s ↦
      {t | ((minpoly (MvPolynomial σ k) (x : A)).map (MvPolynomial.eval z)).IsRoot t}) :=
    fun ψ _ ψ' _ h ↦ AlgHom.ext_of_adjoin_eq_top hs fun x hx ↦ congrFun h ⟨x, hx⟩
  refine ((Set.Finite.pi fun x : s ↦ finite_setOfPred_isRoot ?_).preimage hinj).subset ?_
  · exact ((minpoly.monic (Algebra.IsIntegral.isIntegral (R := MvPolynomial σ k) (x : A))).map
      _).ne_zero
  · rintro ψ rfl x -
    simp only [Set.mem_ofPred_eq, IsRoot.def, f]
    rw [← apply_aeval, minpoly.aeval, map_zero]

/-- A single element `a ∈ A` separates a `k`-point `φ` from the other points of its fibre:
a point `ψ` over `proj σ φ` with `ψ(a) = φ(a)` is `φ`. -/
theorem exists_separating [Infinite k] [Algebra.FiniteType k A]
    [Algebra.IsIntegral (MvPolynomial σ k) A] (φ : A →ₐ[k] k) :
    ∃ a : A, ∀ ψ : A →ₐ[k] k, proj σ ψ = proj σ φ → ψ a = φ a → ψ = φ := by
  set F := {ψ : A →ₐ[k] k | proj σ ψ = proj σ φ ∧ ψ ≠ φ}
  have : Finite F := ((finite_fibre (proj σ φ)).subset fun ψ hψ ↦ hψ.1).to_subtype
  let p : F → Submodule k A := fun ψ ↦ LinearMap.ker (ψ.1.toLinearMap - φ.toLinearMap)
  have hp : ∀ ψ, p ψ ≠ ⊤ := by
    intro ψ h
    refine ψ.2.2 (AlgHom.ext fun x ↦ ?_)
    have hx : x ∈ p ψ := h ▸ Submodule.mem_top
    simpa [p, sub_eq_zero] using hx
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨a, fun ψ hψ hψa ↦ ?_⟩
  by_contra hne
  exact ha ⟨ψ, hψ, hne⟩ (by simp [p, hψa])

end Projection

end MMP.RegularPartDense
