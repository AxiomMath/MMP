/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
public import MMP.AlgebraicGeometry.Morphisms.Smooth.CoordinateDerivations
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Regular parameters on smooth schemes in characteristic zero

Let `X` be a smooth scheme over a field `k` of characteristic `0`. This file records how a
regular system of parameters of a local ring `𝒪_{X,p}` gives coordinates in the sense of Kollár
Def. 3.73 (`MMP.Resolution.IsLocalCoordinatesOn`) or dual derivations on a neighbourhood of the
point.

* At a closed point `p`, a regular system of parameters `t_1, …, t_n` of `𝒪_{X,p}` is a system of
  local coordinates at `p` on a neighbourhood of `p`: since `κ(p)/k` is finite separable, the
  cotangent space `𝔪_p/𝔪_p²` is the fibre `κ(p) ⊗ Ω_{X/k}` at `p`, so the `dt_i` are a basis of
  `Ω_{X/k}` near `p`.
* At an arbitrary point `x`, a regular system of parameters `t_1, …, t_d` of `𝒪_{X,x}` has dual
  derivations: `δ_1, …, δ_d ∈ Der_X(V)` on a neighbourhood `V` of `x` with `δ_i(t_j) = δ_ij`.
  Here `d = dim 𝒪_{X,x}` may be smaller than the rank of `Ω_{X/k}` at `x`.

That étale morphisms preserve the maximal ideal and the dimension of local rings is the
library's: `AlgebraicGeometry.map_maximalIdeal_stalkMap_of_etale` and
`AlgebraicGeometry.ringKrullDim_stalk_eq_of_etale`.

## Main results

* `MMP.Flips.ResolutionInputs.exists_isLocalCoordinatesAt_of_isRegularSystemOfParameters`:
  regular parameters at a closed point are local coordinates near it.
* `MMP.Flips.ResolutionInputs.exists_sheafDerivationOf_dual_of_isRegularSystemOfParameters`:
  derivations dual to regular parameters at an arbitrary point.

## Implementation notes

The adapted coordinates of a smooth flag are in
`MMP.Foundations.Flips.ResolutionInputs.SmoothFlagParameters`.

* A regular system of parameters of a local ring `A` is `MMP.Mori.IsRegularSystemOfParameters`:
  `dim A` elements generating the maximal ideal. "The `t_i` are regular on `V`" is read as: there
  are sections over `V` whose germs at the point are the `t_i`.
* Closed subschemes are ideal sheaves (`AlgebraicGeometry.Scheme.IdealSheafData`); an equation
  `Z ∩ U = (x_1 = ⋯ = x_r = 0)` of subschemes is read on the affine opens `W ⊆ U`, as
  `I_Z(W) = (x_1|_W, …, x_r|_W)`, and `Z ⊆ S` is the inclusion of ideal sheaves `I_S ⊆ I_Z`.
  The open `Z ∩ U` of `Z` is the preimage of `U` under the closed immersion `Z → X`, and the
  restriction of a section of `𝒪_X(U)` to it is its image under that immersion.
* The local dimension `n = dim_p X` at a closed point `p` of a scheme of finite type over a field
  is the dimension of the local ring `𝒪_{X,p}`, and `codim_p(Z, X) = dim_p X - dim_p Z`; they are
  stated through `ringKrullDim` of the stalks of `X` and of `Z` at `p`, with `n = r + m`.
* "Of finite type over `k`" is weakened to the local finite presentation that smoothness
  carries; quasi-compactness of `X` is not used.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Def. 3.73, 3.75, 3.87]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Flips.ResolutionInputs

open MMP.Resolution

section LocalAlgebra

open KaehlerDifferential TensorProduct

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A regular system of parameters `t` of a Noetherian local ring `R` lies in the maximal ideal
`𝔪`, and its classes in the cotangent space `𝔪/𝔪²` are a basis over the residue field. -/
theorem cotangent_basis_of_regular {n : ℕ} (t : Fin n → R)
    (hspan : Ideal.span (Set.range t) = maximalIdeal R) (hdim : ringKrullDim R = n) :
    ∃ ht : ∀ i, t i ∈ maximalIdeal R,
      LinearIndependent (ResidueField R) (fun i => (maximalIdeal R).toCotangent ⟨t i, ht i⟩) ∧
      ⊤ ≤ Submodule.span (ResidueField R)
        (Set.range fun i => (maximalIdeal R).toCotangent ⟨t i, ht i⟩) := by
  have ht : ∀ i, t i ∈ maximalIdeal R := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hsp : ⊤ ≤ Submodule.span (ResidueField R)
      (Set.range fun i => (maximalIdeal R).toCotangent ⟨t i, ht i⟩) := by
    have : Set.range (fun i => (maximalIdeal R).toCotangent ⟨t i, ht i⟩) =
        (maximalIdeal R).toCotangent '' Set.range (fun i => (⟨t i, ht i⟩ : maximalIdeal R)) := by
      rw [← Set.range_comp]
      rfl
    rw [this, top_le_iff, CotangentSpace.span_image_eq_top_iff]
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hspan
  refine ⟨ht, linearIndependent_of_top_le_span_of_card_eq_finrank hsp ?_, hsp⟩
  rw [Fintype.card_fin, ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  apply le_antisymm
  · exact_mod_cast hdim ▸ ringKrullDim_le_spanFinrank_maximalIdeal R
  · rw [← hspan]
    have h' : (Set.range t).ncard ≤ n := by
      classical
      rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image, Set.ncard_coe_finset]
      exact Finset.card_image_le.trans (by simp)
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_range t)).trans h'

variable (k : Type*) [Field k] [Algebra k R]

omit [IsNoetherianRing R] in
/-- If `R` is formally smooth over `k` and `H¹` of the cotangent complex of `κ(R)/k` vanishes,
then elements of `𝔪` with linearly independent classes in `𝔪/𝔪²` have linearly independent
differentials `1 ⊗ dt_i` in `κ(R) ⊗_R Ω_{R/k}`. -/
theorem linearIndependent_tmul_D [Algebra.FormallySmooth k R]
    [Subsingleton (Algebra.H1Cotangent k (ResidueField R))] {n : ℕ} (t : Fin n → R)
    (ht : ∀ i, t i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i => (maximalIdeal R).toCotangent ⟨t i, ht i⟩)) :
    LinearIndependent (ResidueField R) (fun i => (1 : ResidueField R) ⊗ₜ[R] D k R (t i)) := by
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := k) (P := R)
    (A := ResidueField R) residue_surjective).mpr ‹_›
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  choose r hr using fun i => residue_surjective (c i)
  have hm : ∀ i, t i ∈ RingHom.ker (algebraMap R (ResidueField R)) := fun i => by
    rw [RingHom.mem_ker]
    exact (residue_eq_zero_iff _).mpr (ht i)
  have key : kerCotangentToTensor k R (ResidueField R)
      ((RingHom.ker (algebraMap R (ResidueField R))).toCotangent
        (∑ j, r j • ⟨t j, hm j⟩)) = 0 := by
    rw [map_sum, map_sum, ← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, kerCotangentToTensor_toCotangent, ← hr j]
    exact (algebraMap_smul (ResidueField R) (r j) _).symm
  have h0 := hinj (key.trans (map_zero _).symm)
  rw [Ideal.toCotangent_eq_zero] at h0
  have hmem : (∑ j, r j * t j) ∈ maximalIdeal R ^ 2 := by
    have e : ((∑ j, r j • (⟨t j, hm j⟩ : RingHom.ker (algebraMap R (ResidueField R))) :
        RingHom.ker (algebraMap R (ResidueField R))) : R) = ∑ j, r j * t j := by
      rw [AddSubmonoidClass.coe_finsetSum]
      rfl
    rw [← ker_residue, ← e]
    exact h0
  apply hli
  have hz : (maximalIdeal R).toCotangent (∑ j, r j • (⟨t j, ht j⟩ : maximalIdeal R)) = 0 := by
    rwa [Ideal.toCotangent_eq_zero, AddSubmonoidClass.coe_finsetSum]
  rw [← hz, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ← hr j]
  exact (algebraMap_smul (ResidueField R) (r j) _)

omit [IsNoetherianRing R] in
/-- If `Ω_{κ(R)/k} = 0`, then the differentials `1 ⊗ dt_i` of generators `t_i` of the maximal
ideal span `κ(R) ⊗_R Ω_{R/k}` over the residue field. -/
theorem span_tmul_D [Subsingleton Ω[ResidueField R⁄k]] {n : ℕ} (t : Fin n → R)
    (hspan : Ideal.span (Set.range t) = maximalIdeal R) :
    ⊤ ≤ Submodule.span (ResidueField R)
      (Set.range fun i => (1 : ResidueField R) ⊗ₜ[R] D k R (t i)) := by
  intro v _
  have hex := exact_kerCotangentToTensor_mapBaseChange k R (ResidueField R) residue_surjective
  obtain ⟨y, rfl⟩ := (hex v).mp (Subsingleton.elim _ _)
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
  have hx : (x : R) ∈ Ideal.span (Set.range t) := by
    rw [hspan, ← ker_residue]
    exact x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  rw [kerCotangentToTensor_toCotangent, ← hc, map_sum, tmul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h0 : t j • ((1 : ResidueField R) ⊗ₜ[R] D k R (c j)) = 0 := by
    rw [← algebraMap_smul (ResidueField R) (t j)]
    have : algebraMap R (ResidueField R) (t j) = 0 :=
      (residue_eq_zero_iff _).mpr (hspan ▸ Ideal.subset_span ⟨j, rfl⟩)
    rw [this, zero_smul]
  rw [smul_eq_mul, Derivation.leibniz, tmul_add, tmul_smul, tmul_smul, h0, add_zero,
    ← algebraMap_smul (ResidueField R) (c j)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

omit [IsNoetherianRing R] in
/-- The elements `1 ⊗ dr`, for `r ∈ R`, span `κ(R) ⊗_R Ω_{R/k}` over the residue field. -/
theorem span_tmul_range_D :
    ⊤ ≤ Submodule.span (ResidueField R)
      (Set.range fun r : R => (1 : ResidueField R) ⊗ₜ[R] D k R r) := by
  rintro v -
  induction v using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul c ω =>
    have hω : ω ∈ Submodule.span R (Set.range (D k R)) := by
      rw [span_range_derivation]
      trivial
    have h1 : (1 : ResidueField R) ⊗ₜ[R] ω ∈ Submodule.span (ResidueField R)
        (Set.range fun r : R => (1 : ResidueField R) ⊗ₜ[R] D k R r) := by
      induction hω using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨r, rfl⟩ := hx
        exact Submodule.subset_span ⟨r, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [tmul_add]
        exact add_mem hx hy
      | smul a x _ hx =>
        rw [tmul_smul, ← algebraMap_smul (ResidueField R) a]
        exact Submodule.smul_mem _ _ hx
    rw [show c ⊗ₜ[R] ω = c • ((1 : ResidueField R) ⊗ₜ[R] ω) by
      rw [smul_tmul', smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ h1
  | add x y hx hy => exact add_mem hx hy

end LocalAlgebra

section Spread

open KaehlerDifferential

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- For a localization `B` of `A` at `S`, the map `Ω_{A/k} → Ω_{B/k}` is a localization of
modules at `S`. -/
theorem isLocalizedModule_kaehlerMap (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B]
    [Algebra k B] [IsScalarTower k A B] [IsLocalization S B] :
    IsLocalizedModule S (KaehlerDifferential.map k k A B) := by
  have : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization S
  rw [isLocalizedModule_iff_isBaseChange S B]
  exact isBaseChange_of_formallyEtale k A B

/-- For a localization `B` of `A` at `S`, the coefficientwise map `(ι →₀ A) → (ι →₀ B)` is a
localization of modules at `S`. -/
theorem isLocalizedModule_finsupp (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (ι : Type*) :
    IsLocalizedModule S (Finsupp.mapRange.linearMap (α := ι) (Algebra.linearMap A B)) := by
  rw [isLocalizedModule_iff_isBaseChange S B]
  exact (IsBaseChange.linearMap A B).finsuppPow ι

/-- Localizing the map `(ι →₀ A) → Ω_{A/k}`, `c ↦ ∑ c_i da_i`, at `S` gives the map
`(ι →₀ B) → Ω_{B/k}`, `c ↦ ∑ c_i d(a_i/1)`. -/
theorem map_linearCombination_D (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B]
    [Algebra k B] [IsScalarTower k A B] [IsLocalization S B] {ι : Type*} (a : ι → A) :
    haveI := isLocalizedModule_kaehlerMap (k := k) S B
    haveI := isLocalizedModule_finsupp S B ι
    IsLocalizedModule.map S (Finsupp.mapRange.linearMap (Algebra.linearMap A B))
      (KaehlerDifferential.map k k A B) (Finsupp.linearCombination A (fun i => D k A (a i))) =
      (Finsupp.linearCombination B (fun i => D k B (algebraMap A B (a i)))).restrictScalars A := by
  have := isLocalizedModule_kaehlerMap (k := k) S B
  have := isLocalizedModule_finsupp S B ι
  apply IsLocalizedModule.ext S (Finsupp.mapRange.linearMap (Algebra.linearMap A B))
    (IsLocalizedModule.map_units (KaehlerDifferential.map k k A B))
  rw [IsLocalizedModule.map_comp]
  ext i
  simp

/-- If the differentials `da_i` are a basis of `Ω_{A_P/k}` over the localization `A_P` at a prime
`P`, then there is `g ∉ P` such that the `da_i` are a basis of `Ω_{A_g/k}` over every
localization `A_g` away from `g`. -/
theorem exists_bijective_linearCombination_D_away [Module.FinitePresentation A Ω[A⁄k]]
    (P : Ideal A) [P.IsPrime] (Rp : Type*) [CommRing Rp] [Algebra A Rp]
    [IsLocalization.AtPrime Rp P] [Algebra k Rp] [IsScalarTower k A Rp]
    {ι : Type*} [Finite ι] (a : ι → A)
    (h : Function.Bijective
      (Finsupp.linearCombination Rp (fun i => D k Rp (algebraMap A Rp (a i))))) :
    ∃ g ∉ P, ∀ (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.Away g B] [Algebra k B]
      [IsScalarTower k A B],
      Function.Bijective
        (Finsupp.linearCombination B (fun i => D k B (algebraMap A B (a i)))) := by
  have := isLocalizedModule_kaehlerMap (k := k) P.primeCompl Rp
  have := isLocalizedModule_finsupp P.primeCompl Rp ι
  have h' := map_linearCombination_D (k := k) P.primeCompl Rp a
  obtain ⟨g, hg, hb⟩ := exists_bijective_map_powers P.primeCompl
    (Finsupp.mapRange.linearMap (Algebra.linearMap A Rp)) (KaehlerDifferential.map k k A Rp)
    (Finsupp.linearCombination A (fun i => D k A (a i))) (by rwa [h'])
  refine ⟨g, hg, fun B _ _ _ _ _ => ?_⟩
  have := isLocalizedModule_kaehlerMap (k := k) (Submonoid.powers g) B
  have := isLocalizedModule_finsupp (Submonoid.powers g) B ι
  have := (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Finsupp.mapRange.linearMap (Algebra.linearMap A B)) (KaehlerDifferential.map k k A B)).mpr
    (hb g dvd_rfl)
  rwa [map_linearCombination_D] at this

/-- A family whose linear combination map is bijective gives a basis. -/
def basisOfBijective {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] (v : ι → M)
    (h : Function.Bijective (Finsupp.linearCombination R v)) : Module.Basis ι R M :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective _ h).symm

/-- The basis `basisOfBijective v h` is the family `v`. -/
theorem basisOfBijective_apply {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (v : ι → M) (h : Function.Bijective (Finsupp.linearCombination R v)) (i : ι) :
    basisOfBijective v h i = v i := by
  rw [Module.Basis.apply_eq_iff]
  unfold basisOfBijective
  rw [LinearEquiv.symm_apply_eq]
  simp

/-- A linearly independent family extends to a basis by vectors of a spanning set. -/
theorem exists_sumElim_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {d : ℕ} (w : Fin d → V) (hw : LinearIndependent K w) (S : Set V)
    (hS : ⊤ ≤ Submodule.span K S) :
    ∃ (e : ℕ) (v : Fin e → V), (∀ j, v j ∈ S) ∧ LinearIndependent K (Sum.elim w v) ∧
      ⊤ ≤ Submodule.span K (Set.range (Sum.elim w v)) := by
  classical
  set N := Submodule.span K (Set.range w)
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent K (N.mkQ '' S)
  have hbfin : b.Finite := hbli.setFinite
  have := hbfin.fintype
  let eqv := Fintype.equivFin b
  have hpre : ∀ y : b, ∃ s ∈ S, N.mkQ s = y := fun y => hbS y.2
  choose v0 hv0S hv0 using hpre
  let v : Fin (Fintype.card b) → V := fun j => v0 (eqv.symm j)
  have hqv : N.mkQ ∘ v = ((↑) : b → V ⧸ N) ∘ eqv.symm := funext fun _ => hv0 _
  have hq : LinearIndependent K (N.mkQ ∘ v) := by
    rw [hqv]
    exact hbli.comp _ eqv.symm.injective
  have hqspan : ⊤ ≤ Submodule.span K (Set.range (N.mkQ ∘ v)) := by
    rw [hqv, Set.range_comp, eqv.symm.range_eq_univ, Set.image_univ, Subtype.range_coe, hbspan,
      Submodule.span_image, top_le_iff.mp hS, Submodule.map_top, Submodule.range_mkQ]
  refine ⟨Fintype.card b, v, fun j => hv0S _, ?_, ?_⟩
  · refine linearIndependent_sum.2 ⟨hw, hq.of_comp _, ?_⟩
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx2
    have hx0 : N.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hx1
    rw [← hc, map_sum] at hx0
    simp_rw [map_smul] at hx0
    have := (Fintype.linearIndependent_iff.mp hq) c hx0
    rw [← hc]
    simp [this]
  · intro x _
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
      (hqspan (Submodule.mem_top (x := N.mkQ x)))
    have hdiff : x - ∑ j, c j • v j ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub,
        ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, map_sum, ← hc]
      simp
    have hN : N ≤ Submodule.span K (Set.range (Sum.elim w v)) :=
      Submodule.span_mono fun _ ⟨i, hi⟩ => ⟨Sum.inl i, hi⟩
    have hsum : ∑ j, c j • v j ∈ Submodule.span K (Set.range (Sum.elim w v)) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
    have := Submodule.add_mem _ (hN hdiff) hsum
    rwa [sub_add_cancel] at this

end Spread

section LocalBasis

open KaehlerDifferential TensorProduct

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (k : Type*) [Field k]
  [Algebra k R]

/-- Over a field `k` of characteristic `0`, a regular system of parameters `t` of a formally
smooth, essentially of finite type Noetherian local `k`-algebra `R` extends by elements `r` of `R`
to a family whose differentials are a basis of `Ω_{R/k}`. -/
theorem exists_bijective_linearCombination_D_sumElim [CharZero k] [Algebra.FormallySmooth k R]
    [Algebra.EssFiniteType k R] {d : ℕ} (t : Fin d → R)
    (hspan : Ideal.span (Set.range t) = maximalIdeal R) (hdim : ringKrullDim R = d) :
    ∃ (e : ℕ) (r : Fin e → R),
      Function.Bijective (Finsupp.linearCombination R fun i => D k R (Sum.elim t r i)) := by
  have : Algebra.EssFiniteType k (ResidueField R) :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom k R (ResidueField R))
      residue_surjective
  have : Algebra.FormallySmooth k (ResidueField R) := Algebra.FormallySmooth.of_perfectField
  obtain ⟨ht0, hli, -⟩ := cotangent_basis_of_regular t hspan hdim
  have : Module.Projective R Ω[R⁄k] := ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  obtain ⟨e, v, hvS, hvli, hvsp⟩ :=
    exists_sumElim_basis _ (linearIndependent_tmul_D k t ht0 hli) _ (span_tmul_range_D k)
  choose r hr using hvS
  have hu : (TensorProduct.mk R (ResidueField R) Ω[R⁄k] 1 ∘ fun i => D k R (Sum.elim t r i)) =
      Sum.elim (fun i => (1 : ResidueField R) ⊗ₜ D k R (t i)) v := by
    funext i
    cases i with
    | inl i => rfl
    | inr j => exact hr j
  refine ⟨e, r, ?_⟩
  apply Module.IsLocalRing.linearCombination_bijective_of_flat
  rw [hu]
  refine ⟨hvli, ?_⟩
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  exact top_le_iff.mp hvsp

end LocalBasis

section Geometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- Restriction of sections from `W` to `W' ⊆ W` sends the image of `c ∈ k` in `𝒪_X(W)` to its
image in `𝒪_X(W')`. -/
theorem sectionAlgebra_map_res {W' W : X.Opens} (h : W' ≤ W) (c : k) :
    (X.presheaf.map (homOfLE h).op).hom
      (letI := MMP.Mori.sectionAlgebra sX W; algebraMap k Γ(X, W) c) =
      (letI := MMP.Mori.sectionAlgebra sX W'; algebraMap k Γ(X, W') c) := by
  have := Scheme.Hom.appLE_map sX (U := ⊤) (V := W) (V' := W') (by simp) (homOfLE h).op
  exact congrArg (fun t => (((Scheme.ΓSpecIso (.of k)).inv ≫ t).hom) c) this

/-- For `X` smooth over `k`, the ring of sections `𝒪_X(U)` of an affine open `U` is a smooth
`k`-algebra. -/
theorem smooth_sectionAlgebra [Smooth sX] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := MMP.Mori.sectionAlgebra sX U
    Algebra.Smooth k Γ(X, U) := by
  let := MMP.Mori.sectionAlgebra sX U
  change RingHom.Smooth ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ U (by simp)).hom
  rw [CommRingCat.hom_comp]
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.bijective)
    (HasRingHomProperty.appLE @Smooth sX ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _)

/-- For affine opens `W' ⊆ W`, the restriction map `𝒪_X(W) → 𝒪_X(W')` is étale. -/
theorem etale_res {W' W : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (h : W' ≤ W) :
    RingHom.Etale (X.presheaf.map (homOfLE h).op).hom := by
  have := HasRingHomProperty.appLE @Etale (𝟙 X) inferInstance ⟨W, hW⟩ ⟨W', hW'⟩ h
  convert this using 2
  simp only [Scheme.Hom.appLE]
  exact (Category.id_comp _).symm

/-- Coordinates on an affine open restrict to coordinates on every smaller affine open. -/
theorem exists_basis_res {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    {ι : Type*} (y : ι → Γ(X, V))
    (b : letI := MMP.Mori.sectionAlgebra sX V
      Module.Basis ι Γ(X, V) (KaehlerDifferential k Γ(X, V)))
    (hb : ∀ i, b i =
      (letI := MMP.Mori.sectionAlgebra sX V; KaehlerDifferential.D k Γ(X, V) (y i))) :
    letI := MMP.Mori.sectionAlgebra sX W
    ∃ b' : Module.Basis ι Γ(X, W) (KaehlerDifferential k Γ(X, W)),
      ∀ i, b' i = KaehlerDifferential.D k Γ(X, W) ((X.presheaf.map (homOfLE h).op).hom (y i)) := by
  let := MMP.Mori.sectionAlgebra sX V
  let := MMP.Mori.sectionAlgebra sX W
  let : Algebra Γ(X, V) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  have : IsScalarTower k Γ(X, V) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact (sectionAlgebra_map_res sX h c).symm)
  have : Algebra.Etale Γ(X, V) Γ(X, W) := etale_res hV hW h
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, V) Γ(X, W)
  refine ⟨hbc.basis b, fun i => ?_⟩
  rw [IsBaseChange.basis_apply, hb, KaehlerDifferential.map_D]
  rfl

/-- Finitely many elements of the stalk `𝒪_{X,p}` are the germs at `p` of sections over a
common affine open neighbourhood of `p`. -/
theorem exists_affineOpen_germ_eq {ι : Type*} [Finite ι] (p : X)
    (t : ι → X.presheaf.stalk p) :
    ∃ (W : X.Opens) (_ : IsAffineOpen W) (hpW : p ∈ W) (a : ι → Γ(X, W)),
      ∀ i, (X.presheaf.germ W p hpW).hom (a i) = t i := by
  classical
  have := Fintype.ofFinite ι
  choose U hU s hs using fun i => X.presheaf.exists_germ_eq (t i)
  have hpU' : p ∈ Finset.univ.inf U :=
    Finset.inf_induction (p := fun V : X.Opens => p ∈ V) trivial (fun _ ha _ hb => ⟨ha, hb⟩)
      fun i _ => hU i
  obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset hpU'
  have hle : ∀ i, W ≤ U i := fun i => (show W ≤ Finset.univ.inf U from hWU).trans
    (Finset.inf_le (Finset.mem_univ i))
  refine ⟨W, hW, hpW, fun i => (X.presheaf.map (homOfLE (hle i)).op).hom (s i), fun i => ?_⟩
  rw [← hs i]
  exact X.presheaf.germ_res_apply (homOfLE (hle i)) p hpW (s i)

/-- For `X` locally of finite type over `k`, the residue field at a closed point is a finite
extension of `k`. -/
theorem finite_residueField_of_isClosed [LocallyOfFiniteType sX] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    letI := MMP.Mori.stalkAlgebra sX x
    Module.Finite k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have : LocallyOfFiniteType (X.fromSpecResidueField x) := by
    have hclosedImmersion := isClosed_singleton_iff_isClosedImmersion.mp hx
    infer_instance
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ sX) := inferInstance
  rw [← sX.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp] at hcomp
  simp only [← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  have : Algebra.FiniteType k (X.residueField x) := by
    change RingHom.FiniteType (algebraMap k (X.residueField x))
    convert hcomp using 1
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← Scheme.Γevaluation_naturality]
    simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  have hfin : Module.Finite k (X.residueField x) := finite_of_finite_type_of_isJacobsonRing _ _
  let := MMP.Mori.stalkAlgebra sX x
  exact hfin

/-- For `X` smooth over `k`, each stalk `𝒪_{X,x}` is a formally smooth, Noetherian, essentially
of finite type `k`-algebra. -/
theorem stalk_facts [Smooth sX] (x : X) :
    letI := MMP.Mori.stalkAlgebra sX x
    Algebra.FormallySmooth k (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧
      Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  obtain ⟨W, hW, hpW, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.stalkAlgebra sX x
  let : Algebra Γ(X, W) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hpW⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hpW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hpW⟩
  have : IsScalarTower k Γ(X, W) (X.presheaf.stalk x) :=
    MMP.Mori.isScalarTower_section_stalk sX W ⟨x, hpW⟩
  set P := (hW.primeIdealOf ⟨x, hpW⟩).asIdeal
  have : Algebra.Smooth k Γ(X, W) := smooth_sectionAlgebra sX hW
  have : Algebra.FormallySmooth Γ(X, W) (X.presheaf.stalk x) :=
    Algebra.FormallySmooth.of_isLocalization P.primeCompl
  have : IsNoetherianRing Γ(X, W) := Algebra.FiniteType.isNoetherianRing k _
  have : Algebra.EssFiniteType Γ(X, W) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
  exact ⟨Algebra.FormallySmooth.comp k Γ(X, W) _,
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance,
    Algebra.EssFiniteType.comp k Γ(X, W) _⟩

/-- Germs whose differentials are a basis of `Ω` at a point are sections, over an affine
neighbourhood, whose differentials are a basis on every smaller affine open. -/
theorem exists_affineOpen_basis_of_bijective [Smooth sX] (x : X) {ι : Type*} [Finite ι]
    (u : ι → X.presheaf.stalk x)
    (h : letI := MMP.Mori.stalkAlgebra sX x
      Function.Bijective (Finsupp.linearCombination (X.presheaf.stalk x)
        (fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (u i)))) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (hxV : x ∈ V) (y : ι → Γ(X, V)),
      (∀ i, (X.presheaf.germ V x hxV).hom (y i) = u i) ∧
      ∀ (W : X.Opens) (_ : IsAffineOpen W) (h : W ≤ V),
        letI := MMP.Mori.sectionAlgebra sX W
        ∃ b : Module.Basis ι Γ(X, W) (KaehlerDifferential k Γ(X, W)),
          ∀ i, b i =
            KaehlerDifferential.D k Γ(X, W) ((X.presheaf.map (homOfLE h).op).hom (y i)) := by
  classical
  obtain ⟨W, hW, hpW, a, ha⟩ := exists_affineOpen_germ_eq x u
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.stalkAlgebra sX x
  let : Algebra Γ(X, W) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hpW⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hpW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hpW⟩
  have : IsScalarTower k Γ(X, W) (X.presheaf.stalk x) :=
    MMP.Mori.isScalarTower_section_stalk sX W ⟨x, hpW⟩
  set P := (hW.primeIdealOf ⟨x, hpW⟩).asIdeal
  have : Algebra.Smooth k Γ(X, W) := smooth_sectionAlgebra sX hW
  have hu : ∀ i, u i = algebraMap Γ(X, W) (X.presheaf.stalk x) (a i) := fun i => (ha i).symm
  simp only [hu] at h
  have : Module.FinitePresentation Γ(X, W) Ω[Γ(X, W)⁄k] :=
    Module.finitePresentation_of_projective _ _
  obtain ⟨g, hgP, hg⟩ := exists_bijective_linearCombination_D_away (k := k) P
    (X.presheaf.stalk x) a h
  have hV : IsAffineOpen (X.basicOpen g) := hW.basicOpen g
  let := MMP.Mori.sectionAlgebra sX (X.basicOpen g)
  have : IsLocalization.Away g Γ(X, X.basicOpen g) := hW.isLocalization_basicOpen g
  have : IsScalarTower k Γ(X, W) Γ(X, X.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact (sectionAlgebra_map_res sX (X.basicOpen_le g) c).symm)
  have hbV := hg Γ(X, X.basicOpen g)
  have hpV : x ∈ X.basicOpen g := by
    rw [Scheme.mem_basicOpen X g x hpW]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) P g).mpr hgP
  have hgerm : ∀ i, (X.presheaf.germ (X.basicOpen g) x hpV).hom
      (algebraMap Γ(X, W) Γ(X, X.basicOpen g) (a i)) = u i := fun i => by
    rw [← ha i]
    exact X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le g)) x hpV (a i)
  exact ⟨X.basicOpen g, hV, hpV, fun i => algebraMap Γ(X, W) Γ(X, X.basicOpen g) (a i), hgerm,
    fun W' hW' hle => exists_basis_res sX hV hW' hle _ (basisOfBijective _ hbV)
      (basisOfBijective_apply _ hbV)⟩

/-- Restriction of sections from `U` to itself is the identity. -/
theorem presheaf_map_homOfLE_self (U : X.Opens) (g : Γ(X, U)) :
    (X.presheaf.map (homOfLE (le_refl U)).op).hom g = g := by
  rw [show (homOfLE (le_refl U)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- The pullback of a section `f ∈ 𝒪_X(V)` along the inclusion `V → X` is the restriction to
`ι⁻¹ V` of `f` regarded as a global section of the open subscheme `V`. -/
theorem iota_app_self_eq {V : X.Opens} (f : Γ(X, V)) :
    (V.ι.app V).hom f = (V.toScheme.presheaf.map (homOfLE (le_top : V.ι ⁻¹ᵁ V ≤ ⊤)).op).hom
      (V.topIso.inv.hom f) := by
  change (X.presheaf.map _).hom f = (X.presheaf.map _).hom ((X.presheaf.map _).hom f)
  rw [← CommRingCat.comp_apply]
  erw [← Functor.map_comp]
  rfl

/-- If a derivation `δ` on the open subscheme `V` sends the pullback of `f` to the pullback of
`c`, then `applyDerivation sX δ f = c`. -/
theorem applyDerivation_eq_of_onSections {V : X.Opens}
    (δ : Stacks.Curves.SheafDerivationOf (V.ι ≫ sX)) (f c : Γ(X, V))
    (h : δ.onSections ((V.ι.app V).hom f) = (V.ι.app V).hom c) :
    applyDerivation sX δ f = c := by
  have hge : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun q _ => q.2
  have hinv : ∀ s : Γ(V.toScheme, ⊤), (V.toScheme.presheaf.map (homOfLE hge).op).hom
      ((V.toScheme.presheaf.map (homOfLE (le_top : V.ι ⁻¹ᵁ V ≤ ⊤)).op).hom s) = s := by
    intro s
    rw [← CommRingCat.comp_apply, ← Functor.map_comp,
      show (homOfLE (le_top : V.ι ⁻¹ᵁ V ≤ ⊤)).op ≫ (homOfLE hge).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
    rfl
  rw [iota_app_self_eq, iota_app_self_eq, Stacks.Curves.SheafDerivationOf.onSections_restrict] at h
  have h' := congrArg (V.toScheme.presheaf.map (homOfLE hge).op).hom h
  rw [hinv, hinv] at h'
  unfold applyDerivation
  rw [h', ← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

end Geometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- **At a closed point in characteristic `0`, regular parameters are local coordinates.** Let
`X` be smooth over a field `k` of characteristic `0`, `p ∈ X` a closed point and
`t_1, …, t_n` a regular system of parameters of `𝒪_{X,p}`. There is an open `V ∋ p` on which
the `t_i` are regular (germs of sections `x_i ∈ 𝒪_X(V)`) and are local coordinates at `p`
(Kollár Def. 3.73). -/
@[mmp "lem_mmp_foundation_closed_separable_parameters_differential_coordinates"]
theorem exists_isLocalCoordinatesAt_of_isRegularSystemOfParameters [CharZero k] [Smooth sX]
    (p : X) (hp : IsClosed ({p} : Set X)) {n : ℕ} (t : Fin n → X.presheaf.stalk p)
    (ht : MMP.Mori.IsRegularSystemOfParameters t) :
    ∃ (V : X.Opens) (hpV : p ∈ V) (x : Fin n → Γ(X, V)),
      (∀ i, (X.presheaf.germ V p hpV).hom (x i) = t i) ∧ IsLocalCoordinatesAt sX V x p hpV := by
  classical
  let := MMP.Mori.stalkAlgebra sX p
  obtain ⟨_, _, _⟩ := stalk_facts sX p
  have : Module.Finite k (ResidueField (X.presheaf.stalk p)) :=
    finite_residueField_of_isClosed sX p hp
  have : Algebra.FormallyUnramified k (ResidueField (X.presheaf.stalk p)) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  obtain ⟨ht0, hli, hsp⟩ := cotangent_basis_of_regular t ht.1 ht.2
  have hli' := linearIndependent_tmul_D k t ht0 hli
  have hsp' := span_tmul_D k t ht.1
  have : Module.Projective (X.presheaf.stalk p) Ω[X.presheaf.stalk p⁄k] :=
    ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  have hbij : Function.Bijective (Finsupp.linearCombination (X.presheaf.stalk p)
      (fun i => KaehlerDifferential.D k (X.presheaf.stalk p) (t i))) := by
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    refine ⟨hli', ?_⟩
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact top_le_iff.mp hsp'
  obtain ⟨V, -, hpV, y, hy, hb⟩ := exists_affineOpen_basis_of_bijective sX p t hbij
  exact ⟨V, hpV, y, hy, fun W' hW' => hb W'.1 W'.2 hW', fun i => hy i ▸ ht0 i⟩

/-- **Derivations dual to regular parameters, at any point.** Let `X` be smooth over a field `k`
of characteristic `0`, `x ∈ X` a point (not necessarily closed) and `t_1, …, t_d` a regular system
of parameters of `𝒪_{X,x}`. There are an open neighbourhood `V` of `x` on which the `t_j` are
regular (germs of sections `s_j ∈ 𝒪_X(V)`) and derivations `δ_1, …, δ_d ∈ Der_X(V)` with
`δ_i(s_j) = δ_ij`. -/
@[mmp "lem_mmp_foundation_derivations_dual_nonclosed_parameters"]
theorem exists_sheafDerivationOf_dual_of_isRegularSystemOfParameters [CharZero k] [Smooth sX]
    (x : X) {d : ℕ} (t : Fin d → X.presheaf.stalk x)
    (ht : MMP.Mori.IsRegularSystemOfParameters t) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (s : Fin d → Γ(X, V))
      (δ : Fin d → Stacks.Curves.SheafDerivationOf (V.ι ≫ sX)),
      (∀ j, (X.presheaf.germ V x hxV).hom (s j) = t j) ∧
        ∀ i j, applyDerivation sX (δ i) (s j) = if i = j then 1 else 0 := by
  classical
  let := MMP.Mori.stalkAlgebra sX x
  obtain ⟨_, _, _⟩ := stalk_facts sX x
  obtain ⟨e, r, hbij⟩ := exists_bijective_linearCombination_D_sumElim k t ht.1 ht.2
  obtain ⟨V, hV, hxV, y, hy, hb⟩ := exists_affineOpen_basis_of_bijective sX x _ hbij
  let z : Fin (d + e) → Γ(X, V) := fun i => y (finSumFinEquiv.symm i)
  have hz : IsLocalCoordinatesOn sX V z := fun W' hW' => by
    obtain ⟨b, hb'⟩ := hb W'.1 W'.2 hW'
    exact ⟨b.reindex finSumFinEquiv, fun i => by rw [Module.Basis.reindex_apply, hb']; rfl⟩
  choose δ hδ using fun i : Fin d =>
    MMP.Resolution.Bridges.exists_sheafDerivationOf_onSections_eq_partialDerivative hz
      (Fin.castAdd e i)
  refine ⟨V, hxV, fun j => y (Sum.inl j), δ, fun j => hy _, fun i j => ?_⟩
  apply applyDerivation_eq_of_onSections
  rw [hδ i ⟨V, hV⟩ le_rfl (y (Sum.inl j))]
  congr 1
  have hc := MMP.Resolution.Bridges.partialDerivative_restrictSection_coordinate hz ⟨V, hV⟩
    le_rfl (Fin.castAdd e i) (Fin.castAdd e j)
  have e1 : restrictSection ⟨V, hV⟩ (le_refl V) (z (Fin.castAdd e j)) = y (Sum.inl j) := by
    unfold restrictSection
    rw [presheaf_map_homOfLE_self]
    simp [z]
  rw [e1] at hc
  rw [hc]
  simp [Fin.castAdd_inj]

end MMP.Flips.ResolutionInputs
