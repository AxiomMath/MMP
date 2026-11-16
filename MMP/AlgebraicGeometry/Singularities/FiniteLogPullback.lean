module

public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Morphisms.FiniteFunctionField
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo

/-!
# Log discrepancies under finite log pull-back

Let `h : Y ⟶ X` be a finite surjective morphism of normal varieties of dimension `n` over a
field `k` of characteristic zero, `B_X`, `B_Y` `ℚ`-divisors with `K_X + B_X` `ℚ`-Cartier and
`K_Y + B_Y = h^*(K_X + B_X)`, and `v'` a divisorial valuation over `Y` whose restriction to
`k(X)` is `e · v`. Then `a(v'; Y, B_Y) = e · a(v; X, B_X)`.

Write `v = ord_E` for a prime divisor `E` of a normal model `X' ⟶ X` and `v' = ord_{E'}` for a
prime divisor `E'` of a normal model `Y' ⟶ Y`. Since `v'` restricts to `e · v`, the local ring
`𝒪_{X',E}` is carried into `𝒪_{Y',E'}` by `k(X') ≅ k(X) ⊆ k(Y) ≅ k(Y')`, as a local extension of
discrete valuation rings with ramification index `e`, and the residue extension is algebraic. The
tame computation of the top differentials of such an extension in characteristic zero gives
`ord_{E'}(ω) = e · ord_E(ω) + (e - 1)` for every nonzero rational top form `ω` of `X`. A local
equation `φ` of a Cartier divisor `C` near the centre `c_X(v)` pulls back to one of `h^*C` near
the centre `c_Y(v')`, which lies over `c_X(v)`, so `coeff_{E'}(h^*C) = v'(φ) = e · v(φ)`. Finally
`K_Y + B_Y = h^*(K_X + B_X)` gives, along every prime divisor of `Y`, the relation between the
Cartier presentation of `K_X + B_X` and its pull-back, by algebraic Hartogs.

## Main results

* `MMP.Intersection.isLogDiscrepancy_natCast_mul_of_isFinite`: if `a` is the log discrepancy of
  `v` with respect to `(X, B_X)`, then `e · a` is that of `v'` with respect to `(Y, B_Y)`.

## Implementation notes

The source realizes `v'` on the normalization of the model of `v` in `k(Y)`, where the tame
formula applies to a finite morphism. Here the same formula is proved directly for the local
extension `𝒪_{X',E} → 𝒪_{Y',E'}` of discrete valuation rings, which is all the computation of the
top differentials uses; no common model is built. The canonical divisor of `Y` is the divisor of
`h^*ω`, linearly equivalent to any canonical divisor of the normal variety `Y`.

## References

* [Kollár, Mori, *Birational geometry of algebraic varieties*][kollar-mori], Proposition 5.20.
-/

@[expose] public section

open CategoryTheory

namespace MMP.Intersection

section FiniteLogPullback

universe u

open MMP.Mori
open AlgebraicGeometry hiding PrimeDivisor IsVariety

/-! ### Discrete valuation rings -/

section Algebra

open IsLocalRing KaehlerDifferential TensorProduct

/-- A field map `ι : K₁ → K₂` carrying the image of `A₁` into that of `A₂` restricts to a ring
map `A₁ → A₂`, for `A₂ ⊆ K₂` (a fraction ring). -/
private theorem exists_ringHom_of_range {K₁ K₂ A₁ A₂ : Type*} [Field K₁] [Field K₂] [CommRing A₁]
    [CommRing A₂] [Algebra A₁ K₁] [Algebra A₂ K₂] [IsFractionRing A₂ K₂] (ι : K₁ →+* K₂)
    (h : ∀ a₁ : A₁, ∃ a₂ : A₂, algebraMap A₂ K₂ a₂ = ι (algebraMap A₁ K₁ a₁)) :
    ∃ φ : A₁ →+* A₂, ∀ a, algebraMap A₂ K₂ (φ a) = ι (algebraMap A₁ K₁ a) := by
  choose φ hφ using h
  have inj : Function.Injective (algebraMap A₂ K₂) := IsFractionRing.injective A₂ K₂
  exact ⟨{ toFun := φ
           map_one' := inj (by rw [hφ]; simp)
           map_mul' := fun a b => inj (by rw [hφ]; simp [hφ])
           map_zero' := inj (by rw [hφ]; simp)
           map_add' := fun a b => inj (by rw [hφ]; simp [hφ]) }, hφ⟩

open Polynomial in
/-- **The residue extension of an algebraic extension from a discrete valuation ring into a
local domain is algebraic.** Let `A → B` be a local homomorphism from a discrete valuation ring
`A` to a local domain `B`, with fraction fields `K` of `A` and `L ⊇ B`, compatibly with an
algebraic extension `K → L`. Then `κ(B)` is algebraic over `κ(A)`. -/
private theorem isAlgebraic_residueField_of_isAlgebraic {A B K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (hBL : Function.Injective (algebraMap B L))
    (hcomp : ∀ a, algebraMap B L (algebraMap A B a) = algebraMap K L (algebraMap A K a)) :
    Algebra.IsAlgebraic (ResidueField A) (ResidueField B) := by
  classical
  letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := A)
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid A
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hAB : Function.Injective (algebraMap A B) := by
    intro x y hxy
    apply hAL
    rw [IsScalarTower.algebraMap_apply A B L, hxy, ← IsScalarTower.algebraMap_apply]
  refine ⟨fun y => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨p, hp0, hpb⟩ : IsAlgebraic A (algebraMap B L b) :=
    (IsFractionRing.isAlgebraic_iff A K L).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  have hp : aeval b p = 0 := hBL (by rw [map_zero, ← aeval_algebraMap_apply]; exact hpb)
  set q := p.primPart
  have hq : aeval b q = 0 := by
    have h1 := hp
    rw [p.eq_C_content_mul_primPart, map_mul, aeval_C] at h1
    refine (mul_eq_zero.mp h1).resolve_left ?_
    rw [map_eq_zero_iff _ hAB]
    exact (content_eq_zero_iff).not.mpr hp0
  have hqprim := p.isPrimitive_primPart
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hex : ∃ j, q.coeff j ∉ maximalIdeal A := by
    by_contra hcon
    push Not at hcon
    have hdvd : C ϖ ∣ q := by
      rw [C_dvd_iff_dvd_coeff]
      intro j
      have := hcon j
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
        Ideal.mem_span_singleton] at this
      exact this
    exact hϖ.not_isUnit (hqprim ϖ hdvd)
  obtain ⟨j, hj⟩ := hex
  refine ⟨q.map (residue A), fun h0 => hj ?_, ?_⟩
  · have := congrArg (fun r => r.coeff j) h0
    simp only [coeff_map, coeff_zero] at this
    exact (residue_eq_zero_iff _).mp this
  · have key : ∀ x : A, algebraMap (ResidueField A) (ResidueField B) (residue A x) =
        residue B (algebraMap A B x) := fun x => rfl
    rw [aeval_def, eval₂_map]
    have : (algebraMap (ResidueField A) (ResidueField B)).comp (residue A) =
        (residue B).comp (algebraMap A B) := RingHom.ext key
    rw [this, ← hom_eval₂, ← aeval_def, hq, map_zero]

/-- If `f` is onto modulo `x₀` (its kernel lies in `R ∙ x₀`) and the `f (y i)` span, then `x₀` and
the `y i` span. -/
private theorem span_cons_eq_top_of_ker_le {R V Q : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [AddCommGroup Q] [Module R Q] (f : V →ₗ[R] Q) (x₀ : V)
    (hker : LinearMap.ker f ≤ R ∙ x₀)
    {r : ℕ} (y : Fin r → V) (hy : Submodule.span R (Set.range (f ∘ y)) = ⊤) :
    Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have hv : f v ∈ (Submodule.span R (Set.range y)).map f := by
    rw [Submodule.map_span, ← Set.range_comp, hy]
    trivial
  obtain ⟨w, hw, hfw⟩ := hv
  have hsub : Submodule.span R (Set.range y) ≤
      Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, by simp⟩)
  have h0 : R ∙ x₀ ≤ Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) :=
    Submodule.span_mono (by rintro _ rfl; exact ⟨0, by simp⟩)
  simpa using Submodule.add_mem _ (h0 (hker (by simp [hfw] : v - w ∈ LinearMap.ker f))) (hsub hw)

/-- Changing the first vector by an element of the span of the others, and scaling it, scales the
wedge. -/
private theorem ιMulti_cons_eq_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {r : ℕ} (y : Fin r → M) {x x' : M} (c : R) (hx : x - c • x' ∈ Submodule.span R (Set.range y)) :
    exteriorPower.ιMulti R (r + 1) (Fin.cons x y) =
      c • exteriorPower.ιMulti R (r + 1) (Fin.cons x' y) := by
  let L : M →ₗ[R] ⋀[R]^(r + 1) M :=
    (exteriorPower.ιMulti R (r + 1)).toMultilinearMap.toLinearMap (Fin.cons 0 y) 0
  have hL : ∀ z, L z = exteriorPower.ιMulti R (r + 1) (Fin.cons z y) := fun z => by
    simp [L, MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]
  have hker : Submodule.span R (Set.range y) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hL]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := i.succ) (by simp)
      (Fin.succ_ne_zero i).symm
  have := hker hx
  rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  rw [← hL, ← hL, this]

/-- For a local ring with principal maximal ideal `(π)`, the kernel of
`κ ⊗ Ω_{R/k} → Ω_{κ/k}` is spanned by `1 ⊗ dπ`. -/
private theorem ker_mapBaseChange_le {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [Algebra k R] {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    LinearMap.ker (mapBaseChange k R (ResidueField R)) ≤
      (ResidueField R) ∙ ((1 : ResidueField R) ⊗ₜ[R] D k R π) := by
  intro y hy
  obtain ⟨z, rfl⟩ := (exact_kerCotangentToTensor_mapBaseChange k R _ (residue_surjective) y).mp hy
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ z
  have hx' : x ∈ Ideal.span {π} := by
    rwa [← hπ, ← ker_residue]
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  rw [kerCotangentToTensor_toCotangent, Derivation.leibniz, tmul_add, tmul_smul, tmul_smul,
    ← algebraMap_smul (ResidueField R) π, ← algebraMap_smul (ResidueField R) a]
  have : algebraMap R (ResidueField R) π = 0 := by
    rw [← RingHom.mem_ker, IsLocalRing.ResidueField.algebraMap_eq, ker_residue, hπ]
    exact Ideal.mem_span_singleton_self π
  rw [this, zero_smul, add_zero]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- If `R` and its residue field are formally smooth over `k`, then `1 ⊗ dπ ≠ 0` in
`κ ⊗ Ω_{R/k}` for `π ∈ 𝔪 \ 𝔪²`. -/
private theorem tmul_D_ne_zero {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [Algebra k R] [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (ResidueField R)]
    {π : R} (hπ : π ∈ maximalIdeal R) (hπ2 : π ∉ maximalIdeal R ^ 2) :
    ((1 : ResidueField R) ⊗ₜ[R] D k R π) ≠ 0 := by
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := R)
    (A := ResidueField R) residue_surjective).mp inferInstance
  intro h0
  have hker : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, ker_residue]
  have hmem : π ∈ RingHom.ker (algebraMap R (ResidueField R)) := hker ▸ hπ
  have h1 : kerCotangentToTensor k R (ResidueField R)
      ((RingHom.ker (algebraMap R (ResidueField R))).toCotangent ⟨π, hmem⟩) = 0 := by
    rwa [kerCotangentToTensor_toCotangent]
  have h2 := congrArg l h1
  rw [← LinearMap.comp_apply, hl, LinearMap.id_apply, map_zero, Ideal.toCotangent_eq_zero] at h2
  apply hπ2
  rwa [← hker]

/-- Nakayama for a free module of rank `r`: `r` vectors spanning `κ ⊗ M` span `M`. -/
private theorem span_eq_top_of_span_tmul {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Free R M] {r : ℕ} (hr : Module.finrank R M = r)
    (v : Fin r → M)
    (hv : Submodule.span (ResidueField R) (Set.range fun i => (1 : ResidueField R) ⊗ₜ[R] v i) = ⊤) :
    Submodule.span R (Set.range v) = ⊤ := by
  have hfr : Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) = r := by
    rw [Module.finrank_baseChange, hr]
  let b := basisOfTopLeSpanOfCardEqFinrank _ hv.ge (by simp [hfr])
  exact span_eq_top_of_tmul_eq_basis v b (fun i => by simp [b])

/-- A uniformizer of a local domain is not in `𝔪²`. -/
private theorem notMem_maximalIdeal_sq_of_irreducible {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] {t : R} (ht : Irreducible t) (hm : maximalIdeal R = Ideal.span {t}) :
    t ∉ maximalIdeal R ^ 2 := by
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have : t * (1 - t * c) = 0 := by linear_combination hc
  rcases mul_eq_zero.mp this with h | h
  · exact ht.ne_zero h
  · exact ht.not_isUnit (isUnit_iff_exists_inv.mpr ⟨c, by linear_combination -h⟩)

/-- Nakayama for a free module of rank `r + 1`: if `1 ⊗ x₀` and the `1 ⊗ y i` span `κ ⊗ M`, then
`x₀` and the `y i` span `M`. -/
private theorem span_cons_eq_top_of_span_tmul_cons {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M] {r : ℕ}
    (hr : Module.finrank R M = r + 1) (x₀ : M) (y : Fin r → M)
    (h : Submodule.span (ResidueField R) (Set.range (Fin.cons ((1 : ResidueField R) ⊗ₜ[R] x₀)
      fun i => (1 : ResidueField R) ⊗ₜ[R] y i : Fin (r + 1) → ResidueField R ⊗[R] M)) = ⊤) :
    Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → M)) = ⊤ := by
  have : (fun i => (1 : ResidueField R) ⊗ₜ[R] (Fin.cons x₀ y : Fin (r + 1) → M) i) =
      Fin.cons ((1 : ResidueField R) ⊗ₜ[R] x₀) fun i => (1 : ResidueField R) ⊗ₜ[R] y i := by
    funext i
    cases i using Fin.cases <;> simp
  exact span_eq_top_of_span_tmul hr _ (by rwa [this])

/-- `Ω_{κ(A)/k}` has a basis of differentials `d ū_i` of elements of `A`. -/
private theorem exists_basis_D_residue {k A : Type*} [CommRing k] [CommRing A] [IsLocalRing A]
    [Algebra k A] [Module.Finite (ResidueField A) Ω[ResidueField A⁄k]] {r : ℕ}
    (hQ : Module.finrank (ResidueField A) Ω[ResidueField A⁄k] = r) :
    ∃ (u : Fin r → A) (bQ : Module.Basis (Fin r) (ResidueField A) Ω[ResidueField A⁄k]),
      ∀ i, bQ i = D k (ResidueField A) (algebraMap A (ResidueField A) (u i)) := by
  classical
  have hspanQ : Submodule.span (ResidueField A)
      (Set.range fun x : A => D k (ResidueField A) (algebraMap A (ResidueField A) x)) = ⊤ := by
    refine eq_top_iff.mpr ((span_range_derivation k (ResidueField A)).symm.le.trans
      (Submodule.span_mono ?_))
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact ⟨x, rfl⟩
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (ResidueField A)
    (Set.range fun x : A => D k (ResidueField A) (algebraMap A (ResidueField A) x))
  let bb := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspanQ])
  have : Fintype b := @Fintype.ofFinite b (Module.Finite.finite_basis bb)
  let eqv : Fin r ≃ b :=
    (Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis bb, hQ])).symm
  have hu : ∀ i, ∃ x : A, D k (ResidueField A) (algebraMap A (ResidueField A) x) = (eqv i).1 :=
    fun i => hbs (eqv i).2
  choose u hu using hu
  refine ⟨u, bb.reindex eqv.symm, fun i => ?_⟩
  simp only [bb, Module.Basis.reindex_apply, Module.Basis.mk_apply, Equiv.symm_symm]
  exact (hu i).symm

/-- For a uniformizer `t` of `A` and lifts `u_i` of a basis `d ū_i` of `Ω_{κ(A)/k}`, the forms
`dt, du_1, …, du_r` generate the free module `Ω_{A/k}` of rank `n = r + 1`. -/
private theorem exists_span_cons_D_eq_top {k A : Type*} [Field k] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra k A] [Algebra.FormallySmooth k A]
    [Algebra.FormallySmooth k (ResidueField A)] [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]
    {n : ℕ} (hA : Module.finrank A Ω[A⁄k] = n) {t : A} (ht : Irreducible t) :
    ∃ r, n = r + 1 ∧ ∃ (u : Fin r → A)
      (bQ : Module.Basis (Fin r) (ResidueField A) Ω[ResidueField A⁄k]),
      (∀ i, bQ i = D k (ResidueField A) (algebraMap A (ResidueField A) (u i))) ∧
      Submodule.span A
        (Set.range (Fin.cons (D k A t) fun i => D k A (u i) : Fin (r + 1) → Ω[A⁄k])) = ⊤ := by
  have htm : t ∈ maximalIdeal A := (mem_maximalIdeal t).mpr ht.not_isUnit
  have hmA : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  have hx₀ := tmul_D_ne_zero (k := k) htm (notMem_maximalIdeal_sq_of_irreducible ht hmA)
  have hV : Module.finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄k]) = n := by
    rw [Module.finrank_baseChange, hA]
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 => by
    rw [h0, Module.finrank_zero_iff] at hV
    exact hx₀ (Subsingleton.elim _ _)
  let fA := mapBaseChange k A (ResidueField A)
  have hfA : Function.Surjective fA := mapBaseChange_surjective k A _ residue_surjective
  have hfx₀ : fA ((1 : ResidueField A) ⊗ₜ[A] D k A t) = 0 := by
    simp [fA, mapBaseChange_tmul, (residue_eq_zero_iff t).mpr htm]
  have hkerA : LinearMap.ker fA = ResidueField A ∙ ((1 : ResidueField A) ⊗ₜ[A] D k A t) :=
    le_antisymm (ker_mapBaseChange_le hmA) ((Submodule.span_singleton_le_iff_mem _ _).mpr hfx₀)
  have hQ : Module.finrank (ResidueField A) Ω[ResidueField A⁄k] = r := by
    have h := LinearMap.finrank_range_add_finrank_ker fA
    rw [LinearMap.range_eq_top.mpr hfA, finrank_top, hkerA, finrank_span_singleton hx₀, hV] at h
    omega
  have : Module.Finite (ResidueField A) Ω[ResidueField A⁄k] := Module.Finite.of_surjective fA hfA
  obtain ⟨u, bQ, hbQ⟩ := exists_basis_D_residue (k := k) hQ
  have hu' : Submodule.span (ResidueField A)
      (Set.range (fA ∘ fun i => (1 : ResidueField A) ⊗ₜ[A] D k A (u i))) = ⊤ := by
    rw [← bQ.span_eq]
    congr 1
    ext x
    simp [fA, mapBaseChange_tmul, hbQ]
  exact ⟨r, rfl, u, bQ, hbQ, span_cons_eq_top_of_span_tmul_cons hA _ _
    (span_cons_eq_top_of_ker_le fA _ hkerA.le _ hu')⟩

/-- For a uniformizer `s` of `B` and lifts `u_i ∈ A` of a basis `d ū_i` of `Ω_{κ(A)/k}`, with
separable residue extension, `ds` and the `d u_i` generate `Ω_{B/k}`. -/
private theorem span_cons_D_algebraMap_eq_top {k A B : Type*} [CommRing k] [CommRing A]
    [IsLocalRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra k A]
    [Algebra k B] [Algebra A B] [IsScalarTower k A B] [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    [Module.Free B Ω[B⁄k]] [Module.Finite B Ω[B⁄k]] {r : ℕ}
    (hB : Module.finrank B Ω[B⁄k] = r + 1) {s : B} (hs : Irreducible s) (u : Fin r → A)
    (bQ : Module.Basis (Fin r) (ResidueField A) Ω[ResidueField A⁄k])
    (hbQ : ∀ i, bQ i = D k (ResidueField A) (algebraMap A (ResidueField A) (u i))) :
    Submodule.span B (Set.range (Fin.cons (D k B s) fun i => D k B (algebraMap A B (u i)) :
      Fin (r + 1) → Ω[B⁄k])) = ⊤ := by
  have : Algebra.FormallyEtale (ResidueField A) (ResidueField B) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  let fB := mapBaseChange k B (ResidueField B)
  let bQ' := (KaehlerDifferential.isBaseChange_of_formallyEtale k (ResidueField A)
    (ResidueField B)).basis bQ
  have hu'B : Submodule.span (ResidueField B)
      (Set.range (fB ∘ fun i => (1 : ResidueField B) ⊗ₜ[B] D k B (algebraMap A B (u i)))) = ⊤ := by
    rw [← bQ'.span_eq]
    congr 1
    ext x
    simp [fB, bQ', mapBaseChange_tmul, hbQ, IsBaseChange.basis_apply]
  exact span_cons_eq_top_of_span_tmul_cons hB _ _ (span_cons_eq_top_of_ker_le fB _
    (ker_mapBaseChange_le (k := k)
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer s).mp hs)) _ hu'B)

/-- **The tame computation.** For a local extension `A → B` of discrete valuation rings over a
field `k` of characteristic zero, with `A` and `κ(A)` formally smooth over `k`, `Ω_{A/k}` and
`Ω_{B/k}` free of rank `n` and separable residue extension, if `t ↦ a s^e` for uniformizers `t`,
`s` and a unit `a`, then some generators of the top forms satisfy that the image of `σ_A` in
`⋀^n Ω_{B/k}` is `w s^{e-1} σ_B` for a unit `w`. -/
private theorem exists_topFormsMap_eq_unit_mul_pow_smul {k A B : Type*} [Field k] [CharZero k]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [IsLocalHom (algebraMap A B)]
    [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k (ResidueField A)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]] [Module.Free B Ω[B⁄k]] [Module.Finite B Ω[B⁄k]]
    {n : ℕ} (hA : Module.finrank A Ω[A⁄k] = n) (hB : Module.finrank B Ω[B⁄k] = n)
    {t : A} (ht : Irreducible t) {s : B} (hs : Irreducible s) {a : Bˣ} {e : ℕ}
    (he : algebraMap A B t = a * s ^ e) :
    ∃ σA : ⋀[A]^n Ω[A⁄k], Submodule.span A {σA} = ⊤ ∧
      ∃ σB : ⋀[B]^n Ω[B⁄k], Submodule.span B {σB} = ⊤ ∧
        ∃ w : Bˣ, topFormsMap k A B n σA = ((w : B) * s ^ (e - 1)) • σB := by
  classical
  obtain ⟨r, rfl, u, bQ, hbQ, hvA⟩ := exists_span_cons_D_eq_top hA ht
  have hvB := span_cons_D_algebraMap_eq_top hB hs u bQ hbQ
  set vA : Fin (r + 1) → Ω[A⁄k] := Fin.cons (D k A t) fun i => D k A (u i)
  set vB : Fin (r + 1) → Ω[B⁄k] := Fin.cons (D k B s) fun i => D k B (algebraMap A B (u i))
  refine ⟨_, ExteriorAlgebra.span_singleton_ιMulti_eq_top vA hvA, _,
    ExteriorAlgebra.span_singleton_ιMulti_eq_top vB hvB, ?_⟩
  rw [topFormsMap_ιMulti]
  have hcomp : (fun i => KaehlerDifferential.map k k A B (vA i)) =
      Fin.cons (D k B (algebraMap A B t)) fun i => D k B (algebraMap A B (u i)) := by
    funext i
    cases i using Fin.cases <;> simp [vA]
  rw [hcomp]
  obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 => by
    rw [h0, pow_zero, mul_one] at he
    exact ht.not_isUnit ((isUnit_map_iff (algebraMap A B) t).mp (he ▸ a.isUnit))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp
    (hvB ▸ Submodule.mem_top : D k B (a : B) ∈ Submodule.span B (Set.range vB))
  have hsm : s * c 0 ∈ maximalIdeal B :=
    Ideal.mul_mem_right _ _ ((mem_maximalIdeal s).mpr hs.not_isUnit)
  have hek : IsUnit ((e + 1 : ℕ) : B) := by
    have : ((e + 1 : ℕ) : B) = algebraMap k B ((e + 1 : ℕ) : k) := by simp
    rw [this]
    exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero e))).map _
  have hw : IsUnit ((a : B) * ((e + 1 : ℕ) : B) + s * c 0) := by
    by_contra h
    have := (maximalIdeal B).sub_mem ((mem_maximalIdeal _).mpr h) hsm
    rw [add_sub_cancel_right, mem_maximalIdeal] at this
    exact this (a.isUnit.mul hek)
  refine ⟨hw.unit, ?_⟩
  rw [IsUnit.unit_spec, Nat.add_sub_cancel]
  apply ιMulti_cons_eq_smul
  rw [he, Derivation.leibniz, Derivation.leibniz_pow, ← hc, Fin.sum_univ_succ]
  have hv0 : vB 0 = D k B s := rfl
  have hvs : ∀ i, vB i.succ = D k B (algebraMap A B (u i)) := fun i => rfl
  simp only [hv0, hvs, Nat.add_sub_cancel]
  have : (a : B) • ((e + 1) • s ^ e • D k B s) +
      s ^ (e + 1) • (c 0 • D k B s + ∑ i : Fin r, c i.succ • D k B (algebraMap A B (u i))) -
      ((↑a * ((e + 1 : ℕ) : B) + s * c 0) * s ^ e) • D k B s =
      s ^ (e + 1) • ∑ i : Fin r, c i.succ • D k B (algebraMap A B (u i)) := by
    rw [← Nat.cast_smul_eq_nsmul B]
    module
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

end Algebra

/-- Pulling a form back along `A → K → K'` agrees with pulling it back along `A → B → K'` when
the two composites `A → K'` agree. -/
private theorem topFormsMap_topFormsMap_eq {k A B K K' : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Field K] [Field K'] [Algebra k A] [Algebra k B] [Algebra k K] [Algebra k K']
    [Algebra A B] [Algebra A K] [Algebra B K'] [Algebra K K'] [IsScalarTower k A B]
    [IsScalarTower k A K] [IsScalarTower k B K'] [IsScalarTower k K K']
    (hφ : ∀ x : A, algebraMap B K' (algebraMap A B x) = algebraMap K K' (algebraMap A K x))
    {n : ℕ} (σ : ⋀[A]^n Ω[A⁄k]) :
    topFormsMap k K K' n (topFormsMap k A K n σ) =
      topFormsMap k B K' n (topFormsMap k A B n σ) := by
  have hΩ : ∀ y : Ω[A⁄k], KaehlerDifferential.map k k K K' (KaehlerDifferential.map k k A K y) =
      KaehlerDifferential.map k k B K' (KaehlerDifferential.map k k A B y) := by
    intro y
    have hy : y ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      simp [hφ]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul a x _ hx =>
      have e1 : KaehlerDifferential.map k k A K (a • x) =
          algebraMap A K a • KaehlerDifferential.map k k A K x := by
        rw [map_smul, algebraMap_smul]
      have e2 : KaehlerDifferential.map k k A B (a • x) =
          algebraMap A B a • KaehlerDifferential.map k k A B x := by
        rw [map_smul, algebraMap_smul]
      rw [e1, e2, map_smul, map_smul, hx, ← algebraMap_smul K' (algebraMap A K a),
        ← algebraMap_smul K' (algebraMap A B a), hφ]
  have hs : σ ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    simp only [topFormsMap_ιMulti, hΩ]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    have e1 : topFormsMap k A K n (a • x) = algebraMap A K a • topFormsMap k A K n x := by
      rw [map_smul, algebraMap_smul]
    have e2 : topFormsMap k A B n (a • x) = algebraMap A B a • topFormsMap k A B n x := by
      rw [map_smul, algebraMap_smul]
    rw [e1, e2, map_smul, map_smul, hx, ← algebraMap_smul K' (algebraMap A K a),
      ← algebraMap_smul K' (algebraMap A B a), hφ]

/-- The order along a prime divisor of `u ϖ^n`, for a unit `u` and a uniformizer `ϖ`, is `n`. -/
private theorem ord_algebraMap_unit_mul_pow {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : PrimeDivisor Y) {ϖ : E.localRing} (hϖ : Irreducible ϖ)
    (w : E.localRingˣ) (n : ℕ) :
    Y.ord (algebraMap E.localRing Y.functionField (w * ϖ ^ n)) E.genericPoint = n := by
  have := E.isDiscreteValuationRing_localRing
  have hϖ0 : algebraMap E.localRing Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have h1 : Y.ord (algebraMap E.localRing Y.functionField ϖ) E.genericPoint = 1 := by
    have := E.divisorialValuation_algebraMap_of_irreducible hϖ
    rw [E.divisorialValuation_eq_exp_neg_ord hϖ0] at this
    have := WithZero.exp_injective this
    omega
  have hw0 : algebraMap E.localRing Y.functionField w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr w.ne_zero
  rw [map_mul, map_pow, Scheme.ord_mul hw0 (pow_ne_zero _ hϖ0),
    E.ord_algebraMap_of_isUnit w.isUnit, ← zpow_natCast, ord_zpow _ hϖ0, h1]
  ring

/-- If one valuation is the `e`-th power of another along a ring map, then `e ≠ 0`. -/
private theorem ne_zero_of_valuation_eq_pow {K K' Γ : Type*} [Ring K] [Ring K']
    [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ} {v' : Valuation K' Γ} {ι : K →+* K'}
    {e : ℕ} (he : ∀ g, v' (ι g) = v g ^ e) : e ≠ 0 := by
  rintro rfl
  simpa using he 0

/-- If `v_{E'}(x') = v_E(x) ^ e` for nonzero rational functions `x`, `x'`, then
`ord_{E'}(x') = e · ord_E(x)`. -/
private theorem ord_eq_mul_of_divisorialValuation_eq_pow {Y Y' : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (E : PrimeDivisor Y) (E' : PrimeDivisor Y') {x : Y.functionField} {x' : Y'.functionField}
    {e : ℕ} (h : E'.divisorialValuation x' = E.divisorialValuation x ^ e) (hx : x ≠ 0)
    (hx' : x' ≠ 0) : Y'.ord x' E'.genericPoint = e * Y.ord x E.genericPoint := by
  rw [E'.divisorialValuation_eq_exp_neg_ord hx', E.divisorialValuation_eq_exp_neg_ord hx,
    ← WithZero.exp_nsmul, WithZero.exp_inj, smul_neg, nsmul_eq_mul] at h
  linear_combination -h

/-! ### Function fields and forms -/

section Forms

/-- A finite dominant morphism of integral schemes induces a finite extension of function
fields. -/
private theorem finite_functionField {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (h : Y ⟶ X)
    [IsFinite h] [IsDominant h] :
    letI := functionFieldMapAlgebra h
    Module.Finite X.functionField Y.functionField := by
  have := MMP.moduleFinite_functionField_of_isFinite h
  convert this using 3
  exact congrArg RingHom.toAlgebra (dominantFunctionFieldMap_eq_functionFieldMap h).symm

/-- The pull-back of a nonzero form along a pull-back generator is nonzero. -/
private theorem pullbackForms_ne_zero {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) {m : ℤ} {τ : PluriForms k K d m}
    (hτ : τ ≠ 0) : pullbackForms (K' := K') m τ ≠ 0 := by
  intro h0
  have h1 := repr_pullbackFormsAlong hω m τ
  rw [← pullbackForms_eq hω m τ, h0] at h1
  simp only [map_zero, Finsupp.zero_apply] at h1
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap K K').injective).mp h1.symm)

/-- The pull-back `ι^*τ` of rational `m`-canonical forms along a `k`-embedding
`ι : k(Y) → k(Y')` of function fields. -/
private noncomputable def pullbackAlong {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sY' : Y' ⟶ Spec (.of k)) [IsIntegral Y] [IsIntegral Y']
    (ι : Y.functionField →+* Y'.functionField)
    (hι : letI := functionFieldAlgebra sY; letI := functionFieldAlgebra sY'
      ∀ c : k, algebraMap k Y'.functionField c = ι (algebraMap k Y.functionField c))
    {d : ℕ} {m : ℤ} (τ : RationalPluriForms sY d m) : RationalPluriForms sY' d m :=
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra sY'
  letI := ι.toAlgebra
  haveI : IsScalarTower k Y.functionField Y'.functionField := IsScalarTower.of_algebraMap_eq hι
  pullbackForms (K := Y.functionField) (K' := Y'.functionField) m τ

/-- **The tame canonical-order formula along an extension of discrete valuations.** Let `Y`,
`Y'` be normal varieties of dimension `n` over a field `k` of characteristic zero, `ι` a
`k`-embedding `k(Y) → k(Y')` of their function fields, and `E`, `E'` prime divisors with
`v_{E'} ∘ ι = v_E ^ e`. Then every nonzero rational `m`-canonical form `τ` of `Y` satisfies
`ord_{E'}(ι^* τ) = e · ord_E(τ) + m (e - 1)`. -/
private theorem ordForm_pullbackAlong_eq {k : Type u} [Field k] [CharZero k]
    {Y Y' : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sY' : Y' ⟶ Spec (.of k))
    [IsIntegral Y] [IsIntegral Y'] [IsLocallyNoetherian Y] [IsLocallyNoetherian Y']
    [IsNormal Y] [IsNormal Y'] (hY : Mori.IsNormalVariety k sY) (hY' : Mori.IsNormalVariety k sY')
    {n : ℕ} (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = n)
    (hd' : letI := functionFieldAlgebra sY'; (Algebra.trdeg k Y'.functionField).toNat = n)
    (htr : letI := functionFieldAlgebra sY; letI := functionFieldAlgebra sY'
      Algebra.trdeg k Y.functionField = Algebra.trdeg k Y'.functionField)
    (ι : Y.functionField →+* Y'.functionField)
    (hι : letI := functionFieldAlgebra sY; letI := functionFieldAlgebra sY'
      ∀ c : k, algebraMap k Y'.functionField c = ι (algebraMap k Y.functionField c))
    (E : PrimeDivisor Y) (E' : PrimeDivisor Y') {e : ℕ}
    (he : ∀ g, E'.divisorialValuation (ι g) = E.divisorialValuation g ^ e)
    {m : ℤ} {τ : RationalPluriForms sY n m} (hτ : τ ≠ 0) :
    E'.ordForm (pullbackAlong sY sY' ι hι τ) = e * E.ordForm τ + m * (e - 1) := by
  classical
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra sY'
  letI := ι.toAlgebra
  haveI : IsScalarTower k Y.functionField Y'.functionField := IsScalarTower.of_algebraMap_eq hι
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sY' := hY'.1.toLocallyOfFiniteType
  haveI := essFiniteType_functionField (sX := sY)
  haveI : Algebra.IsAlgebraic Y.functionField Y'.functionField := isAlgebraic_of_trdeg_eq k htr
  letI := stalkAlgebra sY E.genericPoint
  letI := stalkAlgebra sY' E'.genericPoint
  haveI := isScalarTower_stalk_functionField sY E.genericPoint
  haveI := isScalarTower_stalk_functionField sY' E'.genericPoint
  haveI := E.isDiscreteValuationRing_localRing
  haveI := E'.isDiscreteValuationRing_localRing
  obtain ⟨_, _⟩ := E.formallySmooth_localRing (sX := sY)
  obtain ⟨_, _⟩ := E.free_kaehlerDifferential_localRing (sX := sY)
  obtain ⟨_, _⟩ := E'.free_kaehlerDifferential_localRing (sX := sY')
  have hrkA := (E.finrank_kaehlerDifferential_localRing (sX := sY)).trans hd
  have hrkB := (E'.finrank_kaehlerDifferential_localRing (sX := sY')).trans hd'
  have he0 : e ≠ 0 := ne_zero_of_valuation_eq_pow he
  have hord : ∀ g : Y.functionField, g ≠ 0 →
      Y'.ord (algebraMap Y.functionField Y'.functionField g) E'.genericPoint =
        e * Y.ord g E.genericPoint := fun g hg =>
    ord_eq_mul_of_divisorialValuation_eq_pow E E' (he g) hg ((map_ne_zero _).mpr hg)
  -- the local extension `𝒪_{Y,E} → 𝒪_{Y',E'}`
  obtain ⟨φ, hφ⟩ := exists_ringHom_of_range (A₁ := E.localRing) (A₂ := E'.localRing)
    (algebraMap Y.functionField Y'.functionField) fun a => by
      have h1 : E.divisorialValuation (algebraMap E.localRing Y.functionField a) ≤ 1 :=
        (E.divisorialValuation_le_one_iff _).mpr ⟨a, rfl⟩
      have h2 : E'.divisorialValuation (algebraMap Y.functionField Y'.functionField
          (algebraMap E.localRing Y.functionField a)) ≤ 1 := by
        change E'.divisorialValuation (ι _) ≤ 1
        rw [he]
        exact (pow_le_one_iff he0).mpr h1
      obtain ⟨b, hb⟩ := (E'.divisorialValuation_le_one_iff _).mp h2
      exact ⟨b, hb⟩
  letI : Algebra E.localRing E'.localRing := φ.toAlgebra
  have hφ' : ∀ x : E.localRing, algebraMap E'.localRing Y'.functionField
      (algebraMap E.localRing E'.localRing x) =
        algebraMap Y.functionField Y'.functionField (algebraMap E.localRing Y.functionField x) :=
    hφ
  haveI : IsScalarTower k E.localRing E'.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c =>
      IsFractionRing.injective E'.localRing Y'.functionField ?_
    rw [hφ', ← IsScalarTower.algebraMap_apply k E.localRing Y.functionField,
      ← IsScalarTower.algebraMap_apply k Y.functionField Y'.functionField,
      ← IsScalarTower.algebraMap_apply k E'.localRing Y'.functionField]
  haveI : IsLocalHom (algebraMap E.localRing E'.localRing) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : E.divisorialValuation (algebraMap E.localRing Y.functionField a) < 1 :=
      (E.divisorialValuation_algebraMap_lt_one_iff a).mpr
        ((IsLocalRing.mem_maximalIdeal a).mpr hna)
    have h2 : E'.divisorialValuation (algebraMap E'.localRing Y'.functionField
        (algebraMap E.localRing E'.localRing a)) < 1 := by
      rw [hφ']
      change E'.divisorialValuation (ι _) < 1
      rw [he]
      exact (pow_lt_one_iff he0).mpr h1
    exact (IsLocalRing.mem_maximalIdeal _).mp
      ((E'.divisorialValuation_algebraMap_lt_one_iff _).mp h2) ha
  haveI : Algebra.FormallySmooth k (IsLocalRing.ResidueField E.localRing) := by
    haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField E.localRing) :=
      Algebra.EssFiniteType.comp k E.localRing _
    exact Algebra.FormallySmooth.of_perfectField
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField E.localRing)
      (IsLocalRing.ResidueField E'.localRing) :=
    isAlgebraic_residueField_of_isAlgebraic (K := Y.functionField) (L := Y'.functionField)
      (IsFractionRing.injective _ _) hφ'
  haveI : CharZero (IsLocalRing.ResidueField E.localRing) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField E.localRing)
      (IsLocalRing.ResidueField E'.localRing) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- uniformizers and the ramification index
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_irreducible E'.localRing
  have hϖ1 : Y.ord (algebraMap E.localRing Y.functionField ϖ) E.genericPoint = 1 := by
    simpa using ord_algebraMap_unit_mul_pow E hϖ 1 1
  have hϖ0 : algebraMap E.localRing Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have hφϖ : algebraMap E.localRing E'.localRing ϖ ≠ 0 := by
    intro h0
    have := hφ' ϖ
    rw [h0, map_zero, eq_comm, map_eq_zero_iff _ (RingHom.injective _)] at this
    exact hϖ0 this
  obtain ⟨e₀, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφϖ hs
  have he₀ : e₀ = e := by
    have h1 := hord _ hϖ0
    rw [← hφ', ha, ord_algebraMap_unit_mul_pow E' hs, hϖ1, mul_one] at h1
    exact_mod_cast h1
  -- the top forms
  obtain ⟨σA, hσA, σB, hσB, w, hw⟩ :=
    exists_topFormsMap_eq_unit_mul_pow_smul (k := k) hrkA hrkB hϖ hs ha
  have h0A := E.topFormsMap_ne_zero (sX := sY) hd hσA
  have h0B := E'.topFormsMap_ne_zero (sX := sY') hd' hσB
  rw [E.ordForm_eq τ hσA h0A, E'.ordForm_eq _ hσB h0B]
  set c : Y'.functionField := algebraMap E'.localRing Y'.functionField (w * s ^ (e₀ - 1))
    with hc_def
  have hc : c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (mul_ne_zero w.ne_zero (pow_ne_zero _ hs.ne_zero))
  have hcomp : topFormsMap k Y.functionField Y'.functionField n
      (topFormsMap k E.localRing Y.functionField n σA) =
      c • topFormsMap k E'.localRing Y'.functionField n σB := by
    rw [topFormsMap_topFormsMap_eq hφ', hw, map_smul, algebraMap_smul]
  have hωA : IsPullbackGenerator Y'.functionField
      (topFormsMap k E.localRing Y.functionField n σA) :=
    ⟨span_singleton_topFormsMap (nonZeroDivisors _) hσA, by
      rw [hcomp, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc),
        span_singleton_topFormsMap (nonZeroDivisors _) hσB], by
      rw [hcomp]; exact smul_ne_zero hc h0B⟩
  have hpb : pullbackAlong sY sY' ι hι τ = pullbackFormsAlong hωA m τ := pullbackForms_eq hωA m τ
  rw [hpb]
  have hb : basisOfSpanSingleton hωA.2.1 hωA.2.2 () =
      c • topFormsBasis E'.localRing hσB h0B () := by
    simp [hcomp]
  have hfB : formCoeff E'.localRing hσB h0B (pullbackFormsAlong hωA m τ) =
      c ^ m * algebraMap Y.functionField Y'.functionField
        (formCoeff E.localRing hσA h0A τ) := by
    have h1 : formCoeff E'.localRing hσB h0B (pullbackFormsAlong hωA m τ) =
        c ^ m * (ZTensorPower.basis (basisOfSpanSingleton hωA.2.1 hωA.2.2) m).repr
          (pullbackFormsAlong hωA m τ) () := by
      unfold formCoeff
      rw [ZTensorPower.basis_repr_of_eq_smul hb m (pullbackFormsAlong hωA m τ), ← mul_assoc,
        mul_inv_cancel₀ (zpow_ne_zero m hc), one_mul]
    rw [h1, repr_pullbackFormsAlong hωA m τ]
    rfl
  have hf : formCoeff E.localRing hσA h0A τ ≠ 0 := fun h0 =>
    hτ ((formCoeff_eq_zero_iff hσA h0A _).mp h0)
  rw [hfB, Scheme.ord_mul (zpow_ne_zero _ hc) ((map_ne_zero _).mpr hf), MMP.Mori.ord_zpow _ hc,
    hord _ hf, hc_def, ord_algebraMap_unit_mul_pow E' hs, he₀,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr he0)]
  push_cast
  ring

end Forms

/-! ### Centres and pull-backs of Cartier divisors -/

section Centre

/-- **The centre upstairs lies over the centre downstairs.** If `D'` is a divisor over `Y` and
`D` one over a variety `X`, with `v_{D'} ∘ h^* = v_D ^ e` for `e ≠ 0`, then `h` maps the centre
of `D'` on `Y` to the centre of `D` on `X`. -/
private theorem map_center_eq_of_valuation_eq_pow {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (h : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsDominant h]
    (hX : MMP.Mori.IsVariety k sX) {D : DivisorOver k sX} {D' : DivisorOver k (h ≫ sX)}
    {e : ℕ} (he0 : e ≠ 0)
    (he : ∀ g, D'.valuation (functionFieldMap h g) = D.valuation g ^ e) :
    h (D'.f D'.E.genericPoint) = D.f D.E.genericPoint := by
  haveI := hX.toIsSeparated
  refine (MMP.Positivity.DivisorOver.eq_of_dominates sX D.valuation (x := D.f D.E.genericPoint)
    (x' := h (D'.f D'.E.genericPoint))
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl) (fun a => ?_)
    (fun a ha => ?_)).symm
  · have h1 := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' _ rfl
      ((h.stalkMap (D'.f D'.E.genericPoint)).hom a)
    rw [← functionFieldMap_algebraMap_stalk, he] at h1
    exact (pow_le_one_iff he0).mp h1
  · have hmem : (h.stalkMap (D'.f D'.E.genericPoint)).hom a ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
    have h1 := MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D' _ rfl _ hmem
    rw [← functionFieldMap_algebraMap_stalk, he] at h1
    exact (pow_lt_one_iff he0).mp h1

/-- **The coefficient of an iterated pull-back.** Let `C` be a Cartier divisor on `X`, `C₁` its
pull-back along `h : Y ⟶ X` and `C₂` the pull-back of `C₁` along `f : Y' ⟶ Y`. If `φ` is a local
equation of `C` on an open `U` containing `h(f(η_E))`, then `coeff_E(C₂) = v_E(f^* h^* φ)`. -/
private theorem coeff_isPullback_isPullback_eq_ord_evalFF {X Y Y' : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] {h : Y ⟶ X} [IsDominant h]
    {f : Y' ⟶ Y} [IsDominant f] {C : Divisor X} (hCc : C.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ C.supp}
    {C₁ : Divisor Y} (h₁ : C.IsPullback h hB C₁)
    {hB₁ : ∀ Z : irreducibleComponents Y', f (componentGenericPoint Y' Z) ∉ C₁.supp}
    {C₂ : Divisor Y'} (h₂ : C₁.IsPullback f hB₁ C₂) {U : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : C.IsLocalEquation U φ) (E : PrimeDivisor Y')
    (hU : h (f E.genericPoint) ∈ U) (Z : irreducibleComponents X) :
    C₂.coeff E = Y'.ord (functionFieldMap f (functionFieldMap h
      (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X)))) E.genericPoint := by
  classical
  obtain ⟨W, hW, ψ, hψ⟩ := (h₁.isCartier hCc) (f E.genericPoint)
  let Z₁ := pointComponent (f E.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h₂ hψ E hW Z₁]
  set g₁ := MMP.Threefold.Mori.Helpers.evalFF Z₁ (ψ : RationalFunctions Y) with hg₁_def
  set g := functionFieldMap h (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X))
    with hg_def
  have hg₁ : g₁ ≠ 0 := (ψ.isUnit.map _).ne_zero
  have hg : g ≠ 0 := (map_ne_zero _).mpr (φ.isUnit.map _).ne_zero
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := f) E ![g₁, g]
    (by intro j; fin_cases j; exacts [hg₁, hg]) ![1, -1] fun Γ hΓ => by
      have hZ : Γ.component = Z₁ := Subsingleton.elim
        (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := Y)) _ _
      have e1 : Y.ord g₁ Γ.genericPoint = C₁.coeff Γ := by
        rw [hψ Γ ⟨_, hΓ, hW⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
      have hΓU : h Γ.genericPoint ∈ U :=
        (Γ.genericPoint_mem_iff (h ⁻¹ᵁ U)).mpr ⟨f E.genericPoint, hΓ, hU⟩
      have e2 : Y.ord g Γ.genericPoint = C₁.coeff Γ :=
        (MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h₁ hφ Γ hΓU Z).symm
      simp [Fin.sum_univ_two, e1, e2]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    mul_one, mul_neg] at key
  have : ((Y'.ord (functionFieldMap f g₁) E.genericPoint : ℤ) : ℝ) =
      (Y'.ord (functionFieldMap f g) E.genericPoint : ℝ) := by linarith
  exact_mod_cast this

end Centre

/-! ### Finite pull-back of divisors over `X` -/

section FinitePullback

/-- A finite dominant morphism of integral `k`-schemes preserves the transcendence degree of the
function field. -/
private theorem trdeg_functionField_eq_of_isFinite {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (h : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsFinite h]
    [IsDominant h] :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (h ≫ sX)
    Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (h ≫ sX)
  letI := functionFieldMapAlgebra h
  haveI := isScalarTower_functionFieldMap sX h
  haveI := finite_functionField h
  haveI : Algebra.IsAlgebraic X.functionField Y.functionField := Algebra.IsAlgebraic.of_finite _ _
  have h1 := trdeg_add_eq k X.functionField (A := Y.functionField)
  rwa [(trdeg_eq_zero_iff (R := X.functionField) (A := Y.functionField)).mpr inferInstance,
    add_zero] at h1

/-- A finite dominant morphism of integral schemes of finite type over a field preserves the
dimension. -/
private theorem topologicalKrullDim_eq_of_isFinite {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (h : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsFinite h]
    [IsDominant h] [LocallyOfFiniteType sX] :
    topologicalKrullDim Y = topologicalKrullDim X := by
  rw [← toENat_trdeg_functionField (sX := h ≫ sX), ← trdeg_functionField_eq_of_isFinite sX h,
    toENat_trdeg_functionField (sX := sX)]

/-- **The tame formula for divisors over a finite cover.** Let `h : Y ⟶ X` be a finite dominant
morphism of normal varieties of dimension `n` over a field of characteristic zero, `D` a divisor
over `X` and `D'` a divisor over `Y` with `v_{D'} ∘ h^* = v_D ^ e`. Then every nonzero rational
top form `ω` of `X` satisfies `ord_{D'}(h^* ω) = e · ord_D(ω) + (e - 1)`. -/
private theorem ordPullback_pullbackRationalPluriForms_eq {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {h : Y ⟶ X} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsFinite h] [IsDominant h] (hX : Mori.IsNormalVariety k sX)
    (hY : Mori.IsNormalVariety k (h ≫ sX)) {n : ℕ} (hn : topologicalKrullDim X = n)
    {D : DivisorOver k sX} {D' : DivisorOver k (h ≫ sX)} {e : ℕ}
    (he : ∀ g, D'.valuation (functionFieldMap h g) = D.valuation g ^ e)
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0) :
    D'.ordPullback (pullbackRationalPluriForms sX h ω) = e * D.ordPullback ω + (e - 1) := by
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isLocallyNoetherian
  have := D'.isNormal
  have := D'.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (h ≫ sX) := hY.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (h ≫ sX)
  let := functionFieldMapAlgebra h
  have := isScalarTower_functionFieldMap sX h
  have htrXY := trdeg_functionField_eq_of_isFinite sX h
  have hdimY : topologicalKrullDim Y = n := (topologicalKrullDim_eq_of_isFinite sX h).trans hn
  have hdX : (Algebra.trdeg k X.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hn
  have hdY : (Algebra.trdeg k Y.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimY
  obtain ⟨ωg, hωg⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq sX h hn hdimY
  let := functionFieldAlgebra (D.f ≫ sX)
  let := functionFieldAlgebra (D'.f ≫ h ≫ sX)
  let := functionFieldMapAlgebra D.f
  let := functionFieldMapAlgebra D'.f
  have := isScalarTower_functionFieldMap sX D.f
  have := isScalarTower_functionFieldMap (h ≫ sX) D'.f
  have hb1 := D.isBirationalMorphism.functionFieldMap_bijective
  have hb2 := D'.isBirationalMorphism.functionFieldMap_bijective
  let eD := RingEquiv.ofBijective (functionFieldMap D.f) hb1
  let ι : D.Y.functionField →+* D'.Y.functionField :=
    (functionFieldMap D'.f).comp ((functionFieldMap h).comp eD.symm.toRingHom)
  have hι1 : ∀ g, ι (functionFieldMap D.f g) = functionFieldMap D'.f (functionFieldMap h g) :=
    fun g => by
      simp only [ι, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      congr 2
      exact eD.symm_apply_apply g
  have hkY' : ∀ c : k, algebraMap k D'.Y.functionField c =
      functionFieldMap D'.f (functionFieldMap h (algebraMap k X.functionField c)) := fun c =>
    (IsScalarTower.algebraMap_apply k Y.functionField D'.Y.functionField c).trans
      (congrArg (functionFieldMap D'.f)
        (IsScalarTower.algebraMap_apply k X.functionField Y.functionField c))
  have hι0 : ∀ c : k, algebraMap k D'.Y.functionField c =
      ι (algebraMap k D.Y.functionField c) := fun c => by
    rw [hkY', show algebraMap k D.Y.functionField c =
        functionFieldMap D.f (algebraMap k X.functionField c) from
      IsScalarTower.algebraMap_apply k X.functionField D.Y.functionField c, hι1]
  have htr' : Algebra.trdeg k D.Y.functionField = Algebra.trdeg k D'.Y.functionField := by
    rw [← trdeg_functionField_eq_of_bijective sX D.f hb1, htrXY,
      trdeg_functionField_eq_of_bijective (h ≫ sX) D'.f hb2]
  have hdX' : (Algebra.trdeg k D.Y.functionField).toNat = n := by
    rwa [← trdeg_functionField_eq_of_bijective sX D.f hb1]
  have hdY' : (Algebra.trdeg k D'.Y.functionField).toNat = n := htr' ▸ hdX'
  have hval : ∀ g, D'.E.divisorialValuation (ι g) = D.E.divisorialValuation g ^ e := by
    intro g
    obtain ⟨g₀, rfl⟩ := hb1.2 g
    rw [hι1]
    exact he g₀
  -- the two factorizations of `k(X) → k(D'.Y)`
  letI := ι.toAlgebra
  haveI : IsScalarTower k D.Y.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq hι0
  letI : Algebra X.functionField D'.Y.functionField :=
    ((functionFieldMap D'.f).comp (functionFieldMap h)).toAlgebra
  haveI : IsScalarTower X.functionField Y.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower X.functionField D.Y.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun g => (hι1 g).symm
  haveI : IsScalarTower k X.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq hkY'
  have := essFiniteType_functionField (sX := D.f ≫ sX)
  obtain ⟨ω₂, hω₂⟩ := exists_isPullbackGenerator_of_bijective (h ≫ sX) D'.f hb2 hdY
  obtain ⟨ω₃, hω₃⟩ := exists_isPullbackGenerator_of_bijective sX D.f hb1 hdX
  obtain ⟨ω₄, hω₄⟩ := exists_isPullbackGenerator (k := k) (K := D.Y.functionField)
    (K' := D'.Y.functionField) htr' hdX'
  have hg1 : IsPullbackGenerator D'.Y.functionField
      (topFormsMap k X.functionField Y.functionField n ωg) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₂ hωg.2.1 hωg.2.2
  have hg2 : IsPullbackGenerator D.Y.functionField ωg :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₃ hωg.1 hωg.ne_zero
  have hg3 : IsPullbackGenerator D'.Y.functionField
      (topFormsMap k X.functionField D.Y.functionField n ωg) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₄ hg2.2.1 hg2.2.2
  have c1 := MMP.Threefold.Mori.Helpers.pullbackForms_comp (K := X.functionField)
    (K' := Y.functionField) (K'' := D'.Y.functionField) (m := 1) hωg hg1 ω
  have c2 := MMP.Threefold.Mori.Helpers.pullbackForms_comp (K := X.functionField)
    (K' := D.Y.functionField) (K'' := D'.Y.functionField) (m := 1) hg2 hg3 ω
  have hτ : pullbackRationalPluriForms sX D.f ω ≠ 0 := pullbackForms_ne_zero hg2 hω
  have key := ordForm_pullbackAlong_eq (D.f ≫ sX) (D'.f ≫ h ≫ sX) D.isNormalVariety
    D'.isNormalVariety hdX' hdY' htr' ι hι0 D.E D'.E hval hτ
  have hP : D'.ordPullback (pullbackRationalPluriForms sX h ω) =
      D'.E.ordForm (pullbackAlong (D.f ≫ sX) (D'.f ≫ h ≫ sX) ι hι0
        (pullbackRationalPluriForms sX D.f ω)) :=
    congrArg D'.E.ordForm (c1.trans c2.symm)
  rw [hP, key, one_mul]
  rfl

/-- The coefficients of an integral divisor `M` with `M = m (K + B)` as `ℚ`-divisors. -/
private theorem coeff_eq_of_toQDivisor_eq_smul {X : Scheme.{u}} {M K : Divisor X}
    {B : QDivisor X} {m : ℕ} (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B))
    (Γ : PrimeDivisor X) : (M.coeff Γ : ℝ) = m * ((K.coeff Γ : ℝ) + (B.coeff Γ : ℝ)) := by
  have h1 := congrArg (fun G : QDivisor X => G.coeff Γ) hM
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
    zsmul_eq_mul, Int.cast_natCast] at h1
  exact_mod_cast h1

/-- Pulling a scalar out of a weighted sum. -/
private theorem sum_mul_mul_eq_mul_sum {ι : Type*} [Fintype ι] (x r : ι → ℝ) (c : ℝ) :
    ∑ i, x i * (c * r i) = c * ∑ i, r i * x i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end FinitePullback

/-- **Finite log pull-back multiplies divisorial log discrepancies.** Let `h : Y ⟶ X` be a finite
surjective morphism of normal varieties of dimension `n` over a field `k` of characteristic zero,
`ω` a nonzero rational top form on `X`, `K_X = div ω` and `K_Y = div(h^*ω)`, and let `B_X`, `B_Y`
be `ℚ`-divisors with `K_X + B_X` `ℚ`-Cartier and `K_Y + B_Y = h^*(K_X + B_X)`. If `D'` is a
divisor over `Y` on a proper model and `D` a divisor over `X`, with
`v_{D'}(h^* g) = v_D(g)^e` for all `g ∈ k(X)`, then `a(D'; Y, B_Y) = e · a(D; X, B_X)`. -/
@[mmp "thm_mmp_finite_log_pullback_discrepancy"]
public theorem isLogDiscrepancy_natCast_mul_of_isFinite {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (h : Y ⟶ X) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsFinite h] [Surjective h]
    (hY : Mori.IsNormalVariety k (h ≫ sX)) {n : ℕ} {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    {KX : Divisor X} (hKX : ∀ Γ, KX.coeff Γ = Γ.ordForm ω) {KY : Divisor Y}
    (hKY : ∀ Γ, KY.coeff Γ = Γ.ordForm (pullbackRationalPluriForms sX h ω))
    {BX : QDivisor X} {BY : QDivisor Y}
    (hq : (Divisor.toQDivisor KX + BX).IsQCartier)
    (hpull : ∃ hB, (Divisor.toQDivisor KX + BX).IsPullback h hB (Divisor.toQDivisor KY + BY))
    {D : DivisorOver k sX} {D' : DivisorOver k (h ≫ sX)} (hD' : IsProper D'.f)
    {e : ℕ} (he : ∀ g : X.functionField, D'.valuation (functionFieldMap h g) = D.valuation g ^ e)
    {a : ℝ} (ha : IsLogDiscrepancy sX n (QDivisor.toRDivisor BX) D a) :
    IsLogDiscrepancy (h ≫ sX) n (QDivisor.toRDivisor BY) D' (e * a) := by
  classical
  obtain ⟨hX, -, ω₀, hω₀, ⟨K₀, hK₀, -⟩, m, r, C, C', hCc, hsum, hpb, rfl⟩ := ha
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isLocallyNoetherian
  have := D'.isNormal
  have := D'.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (h ≫ sX) := hY.1.toLocallyOfFiniteType
  have : CompactSpace Y := by
    have := hY.1
    exact QuasiCompact.compactSpace_of_compactSpace (h ≫ sX)
  have : CompactSpace D'.Y := by
    have := D'.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D'.f ≫ h ≫ sX)
  have hn : topologicalKrullDim X = n := hK₀.topologicalKrullDim_eq
  have hdimY : topologicalKrullDim Y = n := (topologicalKrullDim_eq_of_isFinite sX h).trans hn
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (h ≫ sX)
  let := functionFieldMapAlgebra h
  have := isScalarTower_functionFieldMap sX h
  have hdX : (Algebra.trdeg k X.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hn
  have hdY : (Algebra.trdeg k Y.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimY
  -- the pull-back of forms along `h`
  obtain ⟨ωg, hωg⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq sX h hn hdimY
  set b := basisOfSpanSingleton hωg.1 hωg.ne_zero
  set b' := basisOfSpanSingleton hωg.2.1 hωg.2.2
  have hrepr : ∀ τ : RationalPluriForms sX n 1,
      (ZTensorPower.basis b' 1).repr (pullbackRationalPluriForms sX h τ) () =
        functionFieldMap h ((ZTensorPower.basis b 1).repr τ ()) := fun τ => by
    rw [show pullbackRationalPluriForms sX h τ = pullbackFormsAlong hωg 1 τ from
      pullbackForms_eq hωg 1 τ]
    exact repr_pullbackFormsAlong hωg 1 τ
  have hω₀' : pullbackRationalPluriForms sX h ω₀ ≠ 0 := pullbackForms_ne_zero hωg hω₀
  have hω' : pullbackRationalPluriForms sX h ω ≠ 0 := pullbackForms_ne_zero hωg hω
  -- the canonical divisor of `Y`
  obtain ⟨KY₀, hKY₀⟩ := MMP.Mori.exists_isCanonicalDivisor (h ≫ sX) hY hdimY
  have hKcan : (divisorOfForm (pullbackRationalPluriForms sX h ω₀)).IsCanonicalDivisor (h ≫ sX) n :=
    hKY₀.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hKY₀ hω₀')
  -- the pull-backs of the Cartier divisors `Cᵢ` to `Y` and to `D'.Y`
  have hB₁ : ∀ i, ∀ Z : irreducibleComponents Y, h (componentGenericPoint Y Z) ∉ (C i).supp :=
    fun i => MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp h (C i)
  let C₁ : Fin m → Divisor Y := fun i => (C i).pullback (hCc i) (hB₁ i)
  have hC₁pb : ∀ i, (C i).IsPullback h (hB₁ i) (C₁ i) := fun i =>
    Divisor.isPullback_pullback (hCc i) (hB₁ i)
  have hC₁c : ∀ i, (C₁ i).IsCartier := fun i => (hC₁pb i).isCartier (hCc i)
  have hB₂ : ∀ i, ∀ Z : irreducibleComponents D'.Y,
      D'.f (componentGenericPoint D'.Y Z) ∉ (C₁ i).supp :=
    fun i => MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D'.f (C₁ i)
  let C₂ : Fin m → Divisor D'.Y := fun i => (C₁ i).pullback (hC₁c i) (hB₂ i)
  have hC₂pb : ∀ i, (C₁ i).IsPullback D'.f (hB₂ i) (C₂ i) := fun i =>
    Divisor.isPullback_pullback (hC₁c i) (hB₂ i)
  -- the Cartier multiple of `K_X + B_X` and its pull-back
  obtain ⟨m₀, hm₀, M, hM, hMc⟩ := hq.exists_pos
  obtain ⟨hB, hP⟩ := hpull
  obtain ⟨M', hM', hMpb⟩ := hP m₀ hm₀ M hM hMc
  have hm₀' : (m₀ : ℝ) ≠ 0 := by exact_mod_cast hm₀.ne'
  refine ⟨hY, hD', pullbackRationalPluriForms sX h ω₀, hω₀',
    ⟨_, hKcan, fun Γ => coeff_divisorOfForm _ Γ⟩, m, r, C₁, C₂, hC₁c, fun Γ' => ?_,
    fun i => ⟨_, hC₂pb i⟩, ?_⟩
  · -- `K_Y + B_Y` in terms of the pulled-back Cartier divisors, along `Γ'`
    rw [QDivisor.coeff_toRDivisor]
    choose V hV φ hφ using fun i => hCc i (h Γ'.genericPoint)
    obtain ⟨U₀, hU₀, μ, hμ⟩ := hMc (h Γ'.genericPoint)
    let Z0 := pointComponent (h Γ'.genericPoint)
    let g : Fin m → X.functionField := fun i =>
      MMP.Threefold.Mori.Helpers.evalFF Z0 ((φ i : RationalFunctions X))
    let gμ : X.functionField := MMP.Threefold.Mori.Helpers.evalFF Z0 ((μ : RationalFunctions X))
    set cω₀ := (ZTensorPower.basis b 1).repr ω₀ () with hcω₀
    set cω := (ZTensorPower.basis b 1).repr ω () with hcω
    have hg : ∀ i, g i ≠ 0 := fun i => ((φ i).isUnit.map _).ne_zero
    have hgμ : gμ ≠ 0 := (μ.isUnit.map _).ne_zero
    have hcω₀0 : cω₀ ≠ 0 := repr_ne_zero_of_ne_zero b hω₀
    have hcω0 : cω ≠ 0 := repr_ne_zero_of_ne_zero b hω
    let G : Option (Option (Option (Fin m))) → X.functionField := fun j =>
      Option.elim j gμ fun j => Option.elim j cω₀ fun j => Option.elim j cω g
    let w : Option (Option (Option (Fin m))) → ℝ := fun j =>
      Option.elim j 1 fun j => Option.elim j (m₀ : ℝ) fun j =>
        Option.elim j (-(m₀ : ℝ)) fun i => -(m₀ : ℝ) * r i
    have hG : ∀ j, G j ≠ 0 := by
      rintro (_ | _ | _ | i)
      exacts [hgμ, hcω₀0, hcω0, hg i]
    have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := h) Γ' G hG w
      fun Γ hΓ => by
        obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hdX b
        have hZ : Γ.component = Z0 := Subsingleton.elim
          (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
        have eg : ∀ i, X.ord (g i) Γ.genericPoint = (C i).coeff Γ := fun i => by
          rw [hφ i Γ ⟨_, hΓ, hV i⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
        have eμ : X.ord gμ Γ.genericPoint = M.coeff Γ := by
          rw [hμ Γ ⟨_, hΓ, hU₀⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
        have e1 : (Γ.ordForm ω₀ : ℝ) = X.ord cω₀ Γ.genericPoint + NΓ := by
          exact_mod_cast (by simpa using hNΓ 1 ω₀ hω₀)
        have e2 : (Γ.ordForm ω : ℝ) = X.ord cω Γ.genericPoint + NΓ := by
          exact_mod_cast (by simpa using hNΓ 1 ω hω)
        have e3 := hsum Γ
        rw [QDivisor.coeff_toRDivisor] at e3
        have e4 := coeff_eq_of_toQDivisor_eq_smul hM Γ
        have e5 : (KX.coeff Γ : ℝ) = Γ.ordForm ω := by exact_mod_cast hKX Γ
        simp only [Fintype.sum_option, G, w, Option.elim]
        simp_rw [eg, eμ]
        rw [sum_mul_mul_eq_mul_sum]
        linear_combination e4 - (m₀ : ℝ) * e1 + (m₀ : ℝ) * e2 + (m₀ : ℝ) * e3 + (m₀ : ℝ) * e5
    simp only [Fintype.sum_option, G, w, Option.elim] at key
    obtain ⟨N', hN'⟩ := Γ'.exists_ordForm_eq_ord_add_mul hdY b'
    have f1 : (Γ'.ordForm (pullbackRationalPluriForms sX h ω₀) : ℝ) =
        Y.ord (functionFieldMap h cω₀) Γ'.genericPoint + N' := by
      have := hN' 1 _ hω₀'
      rw [hrepr] at this
      exact_mod_cast (by simpa using this)
    have f2 : (KY.coeff Γ' : ℝ) = Y.ord (functionFieldMap h cω) Γ'.genericPoint + N' := by
      have := hN' 1 _ hω'
      rw [hrepr] at this
      rw [hKY Γ']
      exact_mod_cast (by simpa using this)
    have f3 := coeff_eq_of_toQDivisor_eq_smul hM' Γ'
    have f4 : (M'.coeff Γ' : ℝ) = Y.ord (functionFieldMap h gμ) Γ'.genericPoint := by
      exact_mod_cast MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hMpb hμ Γ' hU₀ Z0
    have f5 : ∀ i, ((C₁ i).coeff Γ' : ℝ) = Y.ord (functionFieldMap h (g i)) Γ'.genericPoint :=
      fun i => by
        exact_mod_cast MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hC₁pb i) (hφ i) Γ'
          (hV i) Z0
    simp_rw [f5]
    rw [sum_mul_mul_eq_mul_sum] at key
    apply mul_left_cancel₀ hm₀'
    linear_combination key + (m₀ : ℝ) * f1 - (m₀ : ℝ) * f2 - f3 + f4
  · -- the value of the log discrepancy
    have he0 : e ≠ 0 := ne_zero_of_valuation_eq_pow he
    have hcen := map_center_eq_of_valuation_eq_pow h hX.1 he0 he
    have hordc : ∀ g : X.functionField, g ≠ 0 →
        D'.Y.ord (functionFieldMap D'.f (functionFieldMap h g)) D'.E.genericPoint =
          e * D.Y.ord (functionFieldMap D.f g) D.E.genericPoint := fun g hg =>
      ord_eq_mul_of_divisorialValuation_eq_pow D.E D'.E (he g) ((map_ne_zero _).mpr hg)
        ((map_ne_zero _).mpr ((map_ne_zero _).mpr hg))
    choose Vx hVx φx hφx using fun i => hCc i (D.f D.E.genericPoint)
    let Zx := pointComponent (D.f D.E.genericPoint)
    have hcoef : ∀ i, ((C₂ i).coeff D'.E : ℝ) = e * ((C' i).coeff D.E : ℝ) := by
      intro i
      obtain ⟨_, hCp⟩ := hpb i
      have hgx : MMP.Threefold.Mori.Helpers.evalFF Zx ((φx i : RationalFunctions X)) ≠ 0 :=
        ((φx i).isUnit.map _).ne_zero
      rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hCp (hφx i) D.E (hVx i) Zx,
        coeff_isPullback_isPullback_eq_ord_evalFF (hCc i) (hC₁pb i) (hC₂pb i) (hφx i) D'.E
          (by rw [hcen]; exact hVx i) Zx, hordc _ hgx]
      push_cast
      ring
    have htame : (D'.ordPullback (pullbackRationalPluriForms sX h ω₀) : ℝ) =
        e * (D.ordPullback ω₀ : ℝ) + (e - 1) := by
      exact_mod_cast ordPullback_pullbackRationalPluriForms_eq hX hY hn he hω₀
    simp_rw [htame, hcoef, mul_left_comm (r _), ← Finset.mul_sum]
    ring

end FiniteLogPullback

end MMP.Intersection
