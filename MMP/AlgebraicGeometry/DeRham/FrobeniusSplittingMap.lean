module

public import MMP.AlgebraicGeometry.Cohomology.Cech.ComplexMap
public import MMP.AlgebraicGeometry.DeRham.FrobeniusLiftForm
public import MMP.AlgebraicGeometry.DeRham.LogCartierRelation

/-!
# The Frobenius splittings `ψ₀`, `ψ₁` of the logarithmic de Rham complex

Let `k` be a perfect field of characteristic `p`, `V` a smooth `k`-scheme with a simple normal
crossing divisor, `K^•` its sheaves of logarithmic forms and `F_*K^•` the Frobenius direct image
of the logarithmic de Rham complex (`MMP.DeRham.FrobeniusSplittingData`). Deligne and Illusie
construct, from a lifting of `V` and of the divisor over `W₂(k)`, morphisms in the derived
category

`ψ₀ : K⁰ ⟶ F_*K^•`, `ψ₁ : K¹[-1] ⟶ F_*K^•`

inducing the inverse Cartier isomorphism on cohomology sheaves in degrees `0` and `1`. On an
affine chart with a Frobenius lift `F̃` the map `ψ₁` is represented by `φ_{F̃} = F̃^*/p`; two lifts
give maps differing by `d ∘ η` for a homotopy `η` satisfying the cocycle relation, and these local
data glue along a Čech resolution.

This file contains the three layers of that construction.

* **Charts.** For a reduction modulo `p`, `π₀ : A → B` (the functions on an affine open of the
  lifting and of `V`), the induced map `A[1/f] → B[1/π₀ f]` is again a reduction modulo `p`; a
  Frobenius lift extends to `A[1/f]` when `p` is nilpotent; `φ_F` is natural; and on a chart
  whose lift fixes lifts of the equations of the divisor, `φ_F` and the homotopies `η` preserve
  logarithmic forms.
* **Gluing on sections.** Local maps given on the sections over the opens inside the members of
  a cover, with homotopies and the cocycle relation, are Čech gluing data
  (`MMP.DeRham.CechGluingSections`), and the cohomology map they induce is, locally, the class of
  the local map.
* **The Frobenius splittings.** For a cover of `V` with local Frobenius splittings
  (`MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting`), the morphism `ψ₁` in the derived
  category and its local description on `ℋ¹`; and `ψ₀` from a morphism `K⁰ ⟶ F_*K⁰`
  representing the inverse Cartier map in degree `0`.

## Main definitions

* `MMP.DeRham.cechDiagramOpensLift`: a morphism `M ⟶ (j_A)_* (j_A)^* N` from maps on the
  sections over the opens inside `A`.
* `MMP.DeRham.CechGluingSections`, `MMP.DeRham.CechGluingSections.toCechGluingData`: Čech gluing
  data given on sections.
* `MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting`: a cover with local Frobenius
  splittings `φ α` of `K¹` and homotopies `η α β`.
* `MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting.psiOne`: `ψ₁ : K¹[-1] ⟶ F_*K^•`.
* `MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting.homologyMapOne`: its effect
  `K¹ ⟶ ℋ¹(F_*K^•)` on cohomology sheaves.
* `MMP.DeRham.FrobeniusSplittingData.psiZero`: `ψ₀ : K⁰ ⟶ F_*K^•`.

## Main results

* `MMP.DeRham.IsReductionModP.away_map`: reduction modulo `p` localizes.
* `MMP.DeRham.exists_isFrobeniusLift_isLocalization_away_of_isNilpotent`: Frobenius lifts
  extend to localizations.
* `MMP.DeRham.frobeniusLiftForm_mapExteriorPower`: naturality of `φ_F`.
* `MMP.DeRham.frobeniusLiftForm_mem_closedLogForms_of_isLocalization`,
  `MMP.DeRham.frobeniusLiftHomotopy_mem_logForms_of_isLocalization`: on a chart, `φ_F` and the
  homotopies preserve logarithmic forms.
* `MMP.DeRham.CechGluingSections.homologyMap_app_eq`: the local description of the glued
  cohomology map.
* `MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting.homologyFunctor_map_psiOne`: `ℋ¹`
  of `ψ₁` is `homologyMapOne`.
* `LocalFrobeniusSplitting.homologyMapOne_comp_extendHomologyIso_app_eq` (in the namespace
  `MMP.DeRham.FrobeniusSplittingData`): on an open inside a chart, `homologyMapOne` sends `s`
  to the class of `φ α s`, a representative of the inverse Cartier image of `s`.

## Implementation notes

The local splittings are given on the sections over all opens inside a chart, and the Frobenius
semilinearity `φ (r s) = r ^ p φ s` is the linearity of a map `K¹ → F_*K¹`, since `r` acts on the
sections of `F_*K¹` by `r ^ p`. The homotopies take values in `K⁰`, the functions on the chart:
for two lifts each fixing a local equation of the lifted divisor, the equations differ by a unit,
and the difference of the lifts at an equation `t` is divisible by `p t ^ p`, which is the
hypothesis under which the homotopy has no poles
(`MMP.DeRham.frobeniusLiftHomotopy_mem_logForms_of_sub_eq`).

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §2 and §4.2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius
open Stacks.CechSiteChange
open KaehlerDifferential KaehlerDifferential.Cartier exteriorPower

universe u v

namespace MMP.DeRham

/-! ### Frobenius lifts on charts -/

section Localization

variable {p : ℕ} {A B R L : Type*} [CommRing A] [CommRing B] [CommRing R] [CommRing L]
  [Algebra A R] [Algebra B L] {π : A →+* B} (f : A) [IsLocalization.Away f R]
  [IsLocalization.Away (π f) L]

/-- **Reduction modulo `p` localizes**: if `π : A → B` is reduction modulo `p`, so is the induced
map `A[1/f] → B[1/π f]`. -/
theorem IsReductionModP.away_map (hπ : IsReductionModP p π) :
    IsReductionModP p (IsLocalization.Away.map R L π f) := by
  set π' := IsLocalization.Away.map R L π f
  have hπ'a : ∀ a, π' (algebraMap A R a) = algebraMap B L (π a) := fun a =>
    IsLocalization.map_eq _ _
  have hpow : ∀ a : A, algebraMap A R a = 0 → ∃ N : ℕ, f ^ N * a = 0 := by
    intro a ha
    obtain ⟨⟨_, N, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) R a).1 ha
    exact ⟨N, hm⟩
  -- `x = a / f ^ n` lies in `p R` when `f ^ N a ∈ p A`
  have hmem : ∀ (x : R) (a : A) (N n : ℕ), x * algebraMap A R f ^ n = algebraMap A R a →
      f ^ N * a ∈ Ideal.span {(p : A)} → x ∈ Ideal.span {(p : R)} := by
    intro x a N n hx h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
    have hu : IsUnit (algebraMap A R f ^ (N + n)) := (IsLocalization.Away.algebraMap_isUnit f).pow _
    refine Ideal.mem_span_singleton'.2 ⟨algebraMap A R b * hu.unit⁻¹, ?_⟩
    have h2 := congrArg (algebraMap A R) hb
    rw [map_mul, map_mul, map_pow, map_natCast, ← hx] at h2
    calc algebraMap A R b * hu.unit⁻¹ * p = (algebraMap A R b * p) * hu.unit⁻¹ := by ring
      _ = (x * algebraMap A R f ^ (N + n)) * hu.unit⁻¹ := by rw [h2]; ring
      _ = x := by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · refine (IsLocalization.Away.map_surjective_iff (S := R) L π f).2 fun b => ?_
    obtain ⟨a, rfl⟩ := hπ.surjective b
    exact ⟨a, 0, by rw [pow_zero, one_mul]⟩
  · ext x
    rw [RingHom.mem_ker]
    constructor
    · intro hx
      obtain ⟨n, a, h⟩ := IsLocalization.Away.surj f x
      have h1 : algebraMap B L (π a) = 0 := by
        rw [← hπ'a, ← h, map_mul, hx, zero_mul]
      obtain ⟨⟨_, N, rfl⟩, hm⟩ :=
        (IsLocalization.map_eq_zero_iff (Submonoid.powers (π f)) L (π a)).1 h1
      exact hmem x a N n h (hπ.map_eq_zero_iff.1 (by rwa [map_mul, map_pow]))
    · intro hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      rw [map_mul, map_natCast, ← map_natCast π' p, ← map_natCast (algebraMap A R) p, hπ'a,
        hπ.map_natCast_eq_zero, map_zero, mul_zero]
  · intro x hx
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj f x
    have h1 : algebraMap A R (p * a) = 0 := by
      rw [map_mul, ← h, map_natCast, ← mul_assoc, hx, zero_mul]
    obtain ⟨N, hN⟩ := hpow _ h1
    refine hmem x a N n h (hπ.mem_span_of_mul_eq_zero _ ?_)
    rw [← hN]
    ring

end Localization

section LocalizationLift

variable {p : ℕ} {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/-- **A Frobenius lift extends to any localization `A[1/f]` when `p` is nilpotent**: then
`F f = f ^ p + p c` is a unit in `A[1/f]`. -/
theorem exists_isFrobeniusLift_isLocalization_away_of_isNilpotent [Fact p.Prime] (f : A)
    [IsLocalization.Away f R] (hp : IsNilpotent (p : A)) {F : A →+* A} (hF : IsFrobeniusLift p F) :
    ∃ F' : R →+* R, IsFrobeniusLift p F' ∧
      ∀ a : A, F' (algebraMap A R a) = algebraMap A R (F a) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hF f)
  have hu : IsUnit ((algebraMap A R).comp F f) := by
    rw [RingHom.comp_apply, show F f = f ^ p + c * p by rw [hc]; ring, map_add, map_pow]
    refine IsNilpotent.isUnit_add_left_of_commute ?_
      ((IsLocalization.Away.algebraMap_isUnit f).pow p) (Commute.all _ _)
    have h := hp.map (algebraMap A R)
    rw [map_natCast] at h
    rw [map_mul, map_natCast]
    exact Commute.isNilpotent_mul_left (Commute.all _ _) h
  refine ⟨IsLocalization.Away.lift f hu, ?_, fun a => IsLocalization.Away.lift_eq f hu a⟩
  rw [isFrobeniusLift_iff]
  refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, powModP_apply]
  refine Ideal.Quotient.eq.2 ?_
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (hF a)
  refine Ideal.mem_span_singleton'.2 ⟨algebraMap A R d, ?_⟩
  rw [← map_pow, ← map_sub, ← hd, map_mul, map_natCast]

end LocalizationLift

section Naturality

variable {p : ℕ} [hp : Fact p.Prime] {R R' : Type*} [CommRing R] [CommRing R'] (k : Type u)
  {L L' : Type u} [CommRing k] [CommRing L] [CommRing L'] [Algebra k L] [Algebra k L']
  [Algebra L L'] [IsScalarTower k L L'] [CharP L p] [CharP L' p] [ExpChar k p] [PerfectRing k p]
  {π : R →+* L} {π' : R' →+* L'} {F F₁ F₂ : R →+* R} {F' F₁' F₂' : R' →+* R'} (g : R →+* R')

omit hp [CharP L p] [CharP L' p] [ExpChar k p] [PerfectRing k p] in
/-- The defect of Frobenius lifts is natural for compatible maps of lifts. -/
theorem frobeniusDefect_map (hπ' : IsReductionModP p π') (hF : IsFrobeniusLift p F)
    (hF' : IsFrobeniusLift p F') (hg : ∀ a, π' (g a) = algebraMap L L' (π a))
    (hgF : ∀ a, F' (g a) = g (F a)) (a : R) :
    frobeniusDefect π' hF' (g a) = algebraMap L L' (frobeniusDefect π hF a) := by
  obtain ⟨c, hc, hδ⟩ := exists_eq_frobeniusDefect (π := π) hF a
  rw [hδ, ← hg, frobeniusDefect_eq hπ' hF' (c := g c)
    (by rw [hgF, hc, map_add, map_pow, map_mul, map_natCast])]

/-- **`φ_F` is natural**: for maps `g : R → R'` and `L → L'` compatible with the reductions and
the Frobenius lifts, `φ_{F'}` of the image of a one-form is the image of `φ_F` of it. -/
theorem frobeniusLiftForm_mapExteriorPower (hπ : IsReductionModP p π)
    (hπ' : IsReductionModP p π') (hF : IsFrobeniusLift p F) (hF' : IsFrobeniusLift p F')
    (hg : ∀ a, π' (g a) = algebraMap L L' (π a)) (hgF : ∀ a, F' (g a) = g (F a))
    (ω : ⋀[L]^1 (Ω[L⁄k])) :
    frobeniusLiftForm k hπ' hF' (mapExteriorPower k L L' 1 ω) =
      mapExteriorPower k L L' 1 (frobeniusLiftForm k hπ hF ω) := by
  induction ω using oneForms_induction (k := k) with
  | h0 => simp only [map_zero]
  | hadd ω η hω hη => rw [map_add, map_add, map_add, map_add, hω, hη]
  | hsmul c ω hω =>
    rw [mapExteriorPower_smul, frobeniusLiftForm_smul, hω, frobeniusLiftForm_smul,
      mapExteriorPower_smul, map_pow]
  | hD x =>
    obtain ⟨a, rfl⟩ := hπ.surjective x
    rw [mapExteriorPower_ιMulti, frobeniusLiftForm_ιMulti_D, mapExteriorPower_ιMulti]
    simp only [map_D, ← hg]
    rw [frobeniusLiftForm_ιMulti_D]
    congr 1
    funext _
    rw [map_add, map_smul, map_D, map_D, frobeniusDefect_map g hπ' hF hF' hg hgF, hg, ← map_pow,
      algebraMap_smul]

omit [CharP L p] [CharP L' p] [ExpChar k p] [PerfectRing k p] in
/-- The map on `0`-forms induced by `L → L'` is `algebraMap L L'`. -/
theorem mapExteriorPower_zeroEquiv_symm (x : L) :
    mapExteriorPower k L L' 0 ((zeroEquiv L (Ω[L⁄k])).symm x) =
      (zeroEquiv L' (Ω[L'⁄k])).symm (algebraMap L L' x) := by
  refine (zeroEquiv L' (Ω[L'⁄k])).injective ?_
  rw [LinearEquiv.apply_symm_apply, zeroEquiv_symm_apply, mapExteriorPower_smul,
    mapExteriorPower_ιMulti, map_smul, zeroEquiv_ιMulti, smul_eq_mul, mul_one]

/-- **`η₁₂` is natural** for maps compatible with the reductions and with both Frobenius
lifts. -/
theorem frobeniusLiftHomotopy_mapExteriorPower (hπ : IsReductionModP p π)
    (hπ' : IsReductionModP p π') (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂)
    (h₁' : IsFrobeniusLift p F₁') (h₂' : IsFrobeniusLift p F₂')
    (hg : ∀ a, π' (g a) = algebraMap L L' (π a)) (hgF₁ : ∀ a, F₁' (g a) = g (F₁ a))
    (hgF₂ : ∀ a, F₂' (g a) = g (F₂ a)) (ω : ⋀[L]^1 (Ω[L⁄k])) :
    frobeniusLiftHomotopy k hπ' h₁' h₂' (mapExteriorPower k L L' 1 ω) =
      mapExteriorPower k L L' 0 (frobeniusLiftHomotopy k hπ h₁ h₂ ω) := by
  induction ω using oneForms_induction (k := k) with
  | h0 => simp only [map_zero]
  | hadd ω η hω hη => rw [map_add, map_add, map_add, map_add, hω, hη]
  | hsmul c ω hω =>
    rw [mapExteriorPower_smul, frobeniusLiftHomotopy_smul, hω, frobeniusLiftHomotopy_smul,
      mapExteriorPower_smul, map_pow]
  | hD x =>
    obtain ⟨a, rfl⟩ := hπ.surjective x
    rw [mapExteriorPower_ιMulti, frobeniusLiftHomotopy_ιMulti_D, mapExteriorPower_zeroEquiv_symm]
    simp only [map_D, ← hg]
    rw [frobeniusLiftHomotopy_ιMulti_D, frobeniusDefect_map g hπ' h₁ h₁' hg hgF₁,
      frobeniusDefect_map g hπ' h₂ h₂' hg hgF₂, ← map_sub]

end Naturality

section Chart

variable {p : ℕ} [hp : Fact p.Prime] (k : Type u) {A R : Type*} {B L : Type u} [CommRing A]
  [CommRing R] [CommRing B] [CommRing L] [CommRing k] [Algebra k L] [CharP L p] [ExpChar k p]
  [PerfectRing k p] [Algebra A R] [Algebra B L] {π₀ : A →+* B} (f : A) [IsLocalization.Away f R]
  [IsLocalization.Away (π₀ f) L] {ι : Type*} {u : ι → B}

/-- **`φ_F` preserves logarithmic forms on a chart.** Let `π₀ : A → B` be reduction modulo `p`
(the functions on an affine open of a lifting and on the corresponding affine open of `V`), `F`
a Frobenius lift on `A` with `F t̃ⱼ = t̃ⱼ ^ p` for lifts `t̃ⱼ` of the local equations `uⱼ` of the
divisor, and `F'` an extension of `F` to `A[1/f]`. On `L = B[1/π₀ f]`, `φ_{F'}` maps logarithmic
one-forms of `B` with poles along the `uⱼ` to closed logarithmic one-forms. -/
theorem frobeniusLiftForm_mem_closedLogForms_of_isLocalization (hπ₀ : IsReductionModP p π₀)
    {F : A →+* A} (hF : IsFrobeniusLift p F) {F' : R →+* R} (hF' : IsFrobeniusLift p F')
    (hFF' : ∀ a, F' (algebraMap A R a) = algebraMap A R (F a)) (t : ι → A)
    (ht : ∀ j, π₀ (t j) = u j) (hFt : ∀ j, F (t j) = t j ^ p)
    (ω : ⋀[L]^1 (Ω[L⁄k])) (hω : (ω : ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 1) :
    ((frobeniusLiftForm k (hπ₀.away_map (R := R) (L := L) f) hF' ω :
        ⋀[L]^1 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈ closedLogForms k L u 1 := by
  have hmap : ∀ a, IsLocalization.Away.map R L π₀ f (algebraMap A R a) =
      algebraMap B L (π₀ a) := fun a => IsLocalization.map_eq _ _
  refine frobeniusLiftForm_mem_closedLogForms k _ hF' (fun b => ?_) (fun j => ?_) ω hω
  · obtain ⟨a, rfl⟩ := hπ₀.surjective b
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hF a)
    refine ⟨algebraMap A R a, algebraMap A R c, hmap a, ?_, π₀ c, (hmap c).symm⟩
    rw [hFF', show F a = a ^ p + p * c by linear_combination -hc, map_add, map_pow, map_mul,
      map_natCast]
  · refine ⟨algebraMap A R (t j), by rw [hmap, ht], ?_⟩
    rw [hFF', hFt, map_pow]

omit [CharP L p] [ExpChar k p] [PerfectRing k p] in
/-- Multiplication by `Ring.inverse x ^ p * x ^ p` preserves every `B`-submodule. -/
theorem ringInverse_pow_mul_pow_smul_mem {M : Type*} [AddCommMonoid M] [Module L M] [Module B M]
    (N : Submodule B M) (x : L) (y : M) (hy : y ∈ N) :
    (Ring.inverse x ^ p * x ^ p) • y ∈ N := by
  by_cases hx : IsUnit x
  · rw [← mul_pow, Ring.inverse_mul_cancel x hx, one_pow, one_smul]
    exact hy
  · rw [Ring.inverse_non_unit x hx, zero_pow hp.out.ne_zero, zero_mul, zero_smul]
    exact zero_mem N

/-- `η₁₂ (dlog π(t)) = π(c)` when `F₂ t - F₁ t = p t ^ p c` and `π t` is a unit; it vanishes
when `π t` is not a unit. -/
theorem frobeniusLiftHomotopy_dlog_of_sub_eq {R : Type*} [CommRing R] {π : R →+* L}
    {F₁ F₂ : R →+* R} (hπ : IsReductionModP p π) (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂) {t c : R} (ht : F₂ t - F₁ t = p * (t ^ p * c)) :
    frobeniusLiftHomotopy k hπ h₁ h₂ (ιMulti L 1 fun _ => Ring.inverse (π t) • D k L (π t)) =
      (Ring.inverse (π t) ^ p * π t ^ p) • (zeroEquiv L (Ω[L⁄k])).symm (π c) := by
  rw [ιMulti_one_smul, frobeniusLiftHomotopy_smul, frobeniusLiftHomotopy_ιMulti_D,
    frobeniusDefect_sub_frobeniusDefect_eq hπ h₁ h₂ ht, map_mul, map_pow, mul_smul,
    ← smul_eq_mul (π t ^ p), map_smul]

/-- **`η₁₂` maps logarithmic one-forms to functions on `B`**, for lifts whose difference at the
lifts `t` of the equations `uⱼ` of the divisor is divisible by `p t ^ p`: the case of two
Frobenius lifts each fixing a local equation of the lifted divisor, the two equations differing by
a unit. -/
theorem frobeniusLiftHomotopy_mem_logForms_of_sub_eq {R : Type*} [CommRing R] {π : R →+* L}
    {F₁ F₂ : R →+* R} (hπ : IsReductionModP p π) (h₁ : IsFrobeniusLift p F₁)
    (h₂ : IsFrobeniusLift p F₂)
    (hB : ∀ b : B, ∃ b' c : R, π b' = algebraMap B L b ∧ F₂ b' - F₁ b' = p * c ∧
      π c ∈ Set.range (algebraMap B L))
    (hu : ∀ j, ∃ t c : R, π t = algebraMap B L (u j) ∧ F₂ t - F₁ t = p * (t ^ p * c) ∧
      π c ∈ Set.range (algebraMap B L))
    (ω : ⋀[L]^1 (Ω[L⁄k])) (hω : (ω : ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 1) :
    ((frobeniusLiftHomotopy k hπ h₁ h₂ ω : ⋀[L]^0 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
      logForms k L u 0 := by
  let S : Submodule B (⋀[L]^1 (Ω[L⁄k])) :=
    { carrier := {ω | ((frobeniusLiftHomotopy k hπ h₁ h₂ ω : ⋀[L]^0 (Ω[L⁄k])) :
        ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 0}
      zero_mem' := by simp
      add_mem' := by
        intro ω η hω hη
        simpa only [Set.mem_ofPred_eq, map_add, Submodule.coe_add] using add_mem hω hη
      smul_mem' := by
        intro b ω hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [← algebraMap_smul L b ω, frobeniusLiftHomotopy_smul, ← map_pow, algebraMap_smul,
          Submodule.coe_smul_of_tower]
        exact Submodule.smul_mem _ _ hω }
  have hrange : ∀ b : B, (((zeroEquiv L (Ω[L⁄k])).symm (algebraMap B L b) :
      ⋀[L]^0 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 0 := by
    intro b
    rw [zeroEquiv_symm_apply, algebraMap_smul, Submodule.coe_smul_of_tower]
    refine Submodule.smul_mem (logForms k L u 0) _ ?_
    rw [ιMulti_apply_coe]
    exact ιMulti_mem_logForms _ fun m => m.elim0
  refine mem_of_mem_logForms S (fun v hv => ?_) ω hω
  have hv' : v = fun _ => v 0 := funext fun i => congrArg v (Subsingleton.elim i 0)
  change ((frobeniusLiftHomotopy k hπ h₁ h₂ _ : ⋀[L]^0 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
    logForms k L u 0
  rw [hv']
  rcases hv 0 with ⟨b, hb⟩ | ⟨j, hj⟩
  · obtain ⟨b', c, hb', hc, b'', hb''⟩ := hB b
    rw [← hb]
    dsimp only
    rw [← hb', frobeniusLiftHomotopy_ιMulti_D, frobeniusDefect_sub_frobeniusDefect_eq hπ h₁ h₂ hc,
      ← hb'']
    exact hrange b''
  · obtain ⟨t, c, ht, hFt, b'', hb''⟩ := hu j
    rw [← hj]
    dsimp only
    rw [← ht, frobeniusLiftHomotopy_dlog_of_sub_eq k hπ h₁ h₂ hFt, ← hb'', Submodule.coe_smul]
    exact ringInverse_pow_mul_pow_smul_mem (logForms k L u 0) (π t) _ (hrange b'')

/-- **`η₁₂` maps logarithmic one-forms to functions on a chart.** For two Frobenius lifts
`F₁, F₂` on `A` and extensions `F₁', F₂'` to `A[1/f]`, with `F₂ t̃ⱼ - F₁ t̃ⱼ` divisible by
`p t̃ⱼ ^ p` at lifts `t̃ⱼ` of the equations `uⱼ` of the divisor, the homotopy `η₁₂` on
`L = B[1/π₀ f]` maps logarithmic one-forms of `B` to the image of `B`. -/
theorem frobeniusLiftHomotopy_mem_logForms_of_isLocalization (hπ₀ : IsReductionModP p π₀)
    {F₁ F₂ : A →+* A} (h₁ : IsFrobeniusLift p F₁) (h₂ : IsFrobeniusLift p F₂)
    {F₁' F₂' : R →+* R} (h₁' : IsFrobeniusLift p F₁') (h₂' : IsFrobeniusLift p F₂')
    (hF₁ : ∀ a, F₁' (algebraMap A R a) = algebraMap A R (F₁ a))
    (hF₂ : ∀ a, F₂' (algebraMap A R a) = algebraMap A R (F₂ a)) (t : ι → A)
    (ht : ∀ j, π₀ (t j) = u j) (hFt : ∀ j, ∃ c : A, F₂ (t j) - F₁ (t j) = p * (t j ^ p * c))
    (ω : ⋀[L]^1 (Ω[L⁄k])) (hω : (ω : ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 1) :
    ((frobeniusLiftHomotopy k (hπ₀.away_map (R := R) (L := L) f) h₁' h₂' ω :
        ⋀[L]^0 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 0 := by
  have hmap : ∀ a, IsLocalization.Away.map R L π₀ f (algebraMap A R a) =
      algebraMap B L (π₀ a) := fun a => IsLocalization.map_eq _ _
  refine frobeniusLiftHomotopy_mem_logForms_of_sub_eq k _ h₁' h₂' (fun b => ?_) (fun j => ?_) ω hω
  · obtain ⟨a, rfl⟩ := hπ₀.surjective b
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h₁.sub_mem h₂ a)
    refine ⟨algebraMap A R a, algebraMap A R c, hmap a, ?_, π₀ c, (hmap c).symm⟩
    rw [hF₁, hF₂, ← map_sub, ← hc, map_mul, map_natCast, mul_comm]
  · obtain ⟨c, hc⟩ := hFt j
    refine ⟨algebraMap A R (t j), algebraMap A R c, by rw [hmap, ht], ?_, π₀ c, (hmap c).symm⟩
    rw [hF₁, hF₂, ← map_sub, hc, map_mul, map_mul, map_pow, map_natCast]

end Chart

/-! ### Čech gluing data from sections -/

section Cech

variable {V : Scheme.{u}}

/-- **A morphism into the direct image of a restriction, from sections.** Additive maps
`φ W : Γ(M, W) → Γ(N, W)` on the opens `W ⊆ A`, linear and compatible with restriction, give the
morphism `M ⟶ (j_A)_* (j_A)^* N` sending a section `s` over `W` to `φ (W ⊓ A) (s|_{W ⊓ A})`. -/
def cechDiagramOpensLift {M N : V.Modules} (A : V.Opens)
    (φ : ∀ W : V.Opens, W ≤ A → Γ(M, W) →+ Γ(N, W))
    (hsmul : ∀ (W : V.Opens) (hW : W ≤ A) (r : Γ(V, W)) (s : Γ(M, W)),
      φ W hW (r • s) = r • φ W hW s)
    (hnat : ∀ (W₁ W₂ : V.Opens) (h₁ : W₁ ≤ A) (h₂ : W₂ ≤ A) (h : W₁ ≤ W₂) (s : Γ(M, W₂)),
      φ W₁ h₁ (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ W₂ h₂ s)) :
    M ⟶ ((cechDiagramOpens V).obj N).obj (op A) :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((φ (W.unop ⊓ A) inf_le_right).comp
          (M.presheaf.map (homOfLE (inf_le_left : W.unop ⊓ A ≤ W.unop)).op).hom))
      naturality := fun W₁ W₂ g => by
        ext s
        apply ULift.ext
        change φ (W₂.unop ⊓ A) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op
            (M.presheaf.map g s)) =
          N.presheaf.map (homOfLE (inf_le_inf_right A (leOfHom g.unop))).op
            (φ (W₁.unop ⊓ A) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op s))
        refine Eq.trans ?_
          (hnat _ _ inf_le_right inf_le_right (inf_le_inf_right A (leOfHom g.unop)) _)
        exact congrArg _
          ((presheaf_map_map _ _ (homOfLE (inf_le_left.trans (leOfHom g.unop))) _).trans
            (presheaf_map_map _ _ _ _).symm) }
    fun (W : (V.Opens)ᵒᵖ) (r : Γ(V, W.unop)) (s : Γ(M, W.unop)) => by
      apply ULift.ext
      change φ (W.unop ⊓ A) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op (r • s)) =
        V.presheaf.map (homOfLE (inf_le_left : W.unop ⊓ A ≤ W.unop)).op r •
          φ (W.unop ⊓ A) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op s)
      refine Eq.trans ?_ (hsmul _ _ _ _)
      exact congrArg _ (M.val.map_smul _ r s)⟩

/-- On a section `s` over `W`, the lift `cechDiagramOpensLift A φ` is `φ` applied to the
restriction of `s` to `W ⊓ A`. -/
theorem cechDiagramOpensLift_app_down {M N : V.Modules} (A : V.Opens)
    (φ : ∀ W : V.Opens, W ≤ A → Γ(M, W) →+ Γ(N, W))
    (hsmul : ∀ (W : V.Opens) (hW : W ≤ A) (r : Γ(V, W)) (s : Γ(M, W)),
      φ W hW (r • s) = r • φ W hW s)
    (hnat : ∀ (W₁ W₂ : V.Opens) (h₁ : W₁ ≤ A) (h₂ : W₂ ≤ A) (h : W₁ ≤ W₂) (s : Γ(M, W₂)),
      φ W₁ h₁ (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ W₂ h₂ s))
    (W : V.Opens) (s : Γ(M, W)) :
    ((cechDiagramOpensLift A φ hsmul hnat).app W s).down =
      φ (W ⊓ A) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op s) := rfl

/-- Morphisms into `(j_A)_* (j_A)^* N` agree when they agree on all sections. -/
theorem cechDiagramOpens_hom_ext {M N : V.Modules} {A : V.Opens}
    {f g : M ⟶ ((cechDiagramOpens V).obj N).obj (op A)}
    (H : ∀ (W : V.Opens) (s : Γ(M, W)), (f.app W s).down = (g.app W s).down) : f = g :=
  Scheme.Modules.hom_ext _ _ fun W => by
    ext s
    exact ULift.ext (H W s)

variable {ι : Type u} {U : ι → V.Opens}

variable (U) in
/-- **Čech gluing data on sections.** Local maps `φ α` on the sections over the opens inside
`U α` and homotopies `η α β` on the sections over the opens inside `U α ⊓ U β`, linear and
compatible with restriction, with `d ∘ φ α = 0`, `φ β - φ α = d ∘ η α β` on `U α ⊓ U β` and
`η α β + η β γ = η α γ` on `U α ⊓ U β ⊓ U γ`. -/
structure CechGluingSections (K : CochainComplex V.Modules ℤ) (M : V.Modules) (n : ℤ) where
  /-- The local maps. -/
  φ (α : ι) (W : V.Opens) : W ≤ U α → Γ(M, W) →+ Γ(K.X (n + 1), W)
  φ_smul (α : ι) (W : V.Opens) (hW : W ≤ U α) (r : Γ(V, W)) (s : Γ(M, W)) :
    φ α W hW (r • s) = r • φ α W hW s
  φ_res (α : ι) (W₁ W₂ : V.Opens) (h₁ : W₁ ≤ U α) (h₂ : W₂ ≤ U α) (h : W₁ ≤ W₂)
    (s : Γ(M, W₂)) : φ α W₁ h₁ (M.presheaf.map (homOfLE h).op s) =
      (K.X (n + 1)).presheaf.map (homOfLE h).op (φ α W₂ h₂ s)
  /-- The homotopies. -/
  η (α β : ι) (W : V.Opens) : W ≤ U α ⊓ U β → Γ(M, W) →+ Γ(K.X n, W)
  η_smul (α β : ι) (W : V.Opens) (hW : W ≤ U α ⊓ U β) (r : Γ(V, W)) (s : Γ(M, W)) :
    η α β W hW (r • s) = r • η α β W hW s
  η_res (α β : ι) (W₁ W₂ : V.Opens) (h₁ : W₁ ≤ U α ⊓ U β) (h₂ : W₂ ≤ U α ⊓ U β)
    (h : W₁ ≤ W₂) (s : Γ(M, W₂)) : η α β W₁ h₁ (M.presheaf.map (homOfLE h).op s) =
      (K.X n).presheaf.map (homOfLE h).op (η α β W₂ h₂ s)
  φ_d (α : ι) (W : V.Opens) (hW : W ≤ U α) (s : Γ(M, W)) :
    (K.d (n + 1) (n + 2)).app W (φ α W hW s) = 0
  φ_sub (α β : ι) (W : V.Opens) (hW : W ≤ U α ⊓ U β) (s : Γ(M, W)) :
    φ β W (hW.trans inf_le_right) s - φ α W (hW.trans inf_le_left) s =
      (K.d n (n + 1)).app W (η α β W hW s)
  η_add (α β γ : ι) (W : V.Opens) (hW : W ≤ U α ⊓ U β ⊓ U γ) (s : Γ(M, W)) :
    η α β W (hW.trans inf_le_left) s +
        η β γ W (hW.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) s =
      η α γ W (hW.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) s

namespace CechGluingSections

variable {K : CochainComplex V.Modules ℤ} {M : V.Modules} {n : ℤ}
  (S : CechGluingSections U K M n)

/-- The Čech gluing data of local maps given on sections. -/
def toCechGluingData : CechGluingData U K M n where
  f α := cechDiagramOpensLift (U α) (S.φ α) (S.φ_smul α) (S.φ_res α)
  h α β := cechDiagramOpensLift (U α ⊓ U β) (S.η α β) (S.η_smul α β) (S.η_res α β)
  f_d α := cechDiagramOpens_hom_ext fun W s => by
    change (K.d (n + 1) (n + 2)).app (W ⊓ U α) (S.φ α (W ⊓ U α) inf_le_right _) = 0
    exact S.φ_d α _ _ _
  f_sub_f α β := cechDiagramOpens_hom_ext fun W s => by
    change (K.X (n + 1)).presheaf.map (homOfLE (inf_le_inf_left W inf_le_right)).op
        (S.φ β (W ⊓ U β) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op s)) -
      (K.X (n + 1)).presheaf.map (homOfLE (inf_le_inf_left W inf_le_left)).op
        (S.φ α (W ⊓ U α) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op s)) =
      (K.d n (n + 1)).app (W ⊓ (U α ⊓ U β)) (S.η α β (W ⊓ (U α ⊓ U β)) inf_le_right
        (M.presheaf.map (homOfLE inf_le_left).op s))
    rw [← S.φ_res, ← S.φ_res, presheaf_map_map, presheaf_map_map]
    exact S.φ_sub α β _ inf_le_right _
  h_add α β γ := cechDiagramOpens_hom_ext fun W s => by
    change (K.X n).presheaf.map (homOfLE (inf_le_inf_left W inf_le_left)).op
        (S.η α β (W ⊓ (U α ⊓ U β)) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op s)) +
      (K.X n).presheaf.map (homOfLE (inf_le_inf_left W
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right))).op
        (S.η β γ (W ⊓ (U β ⊓ U γ)) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op s)) =
      (K.X n).presheaf.map (homOfLE (inf_le_inf_left W
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right))).op
        (S.η α γ (W ⊓ (U α ⊓ U γ)) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op s))
    rw [← S.η_res, ← S.η_res, ← S.η_res, presheaf_map_map, presheaf_map_map, presheaf_map_map]
    exacts [S.η_add α β γ _ inf_le_right _, homOfLE inf_le_left]

/-- On a section `s` over `W`, the local map `f α` of the Čech gluing data is `φ α` applied to the
restriction of `s` to `W ⊓ U α`. -/
theorem toCechGluingData_f_app_down (α : ι) (W : V.Opens) (s : Γ(M, W)) :
    ((S.toCechGluingData.f α).app W s).down =
      S.φ α (W ⊓ U α) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op s) := rfl

/-- **The cohomology map of gluing data on sections is induced by the local maps**: on an open
`W ⊆ U α`, a section `s` is sent to the class of the cycle `φ α s`. -/
theorem homologyMap_app_eq (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] (α : ι)
    {W : V.Opens} (hW : W ≤ U α) (s : Γ(M, W)) (z : Γ(K.cycles (n + 1), W))
    (hz : (K.iCycles (n + 1)).app W z = S.φ α W hW s) :
    (S.toCechGluingData.homologyMap hU a).app W s = (K.homologyπ (n + 1)).app W z := by
  refine S.toCechGluingData.homologyMap_app_eq hU a α hW s z ?_
  rw [toCechGluingData_f_app_down, hz, S.φ_res α _ _ inf_le_right hW inf_le_left]

end CechGluingSections

end Cech

/-! ### The Frobenius splitting maps of the Deligne–Illusie data -/

namespace FrobeniusSplittingData

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectField k] {n : ℕ}
  {V : Scheme.{u}} {f : V ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f]
  {ι : Type v} [Fintype ι] [HasDerivedCategory.{u} V.Modules]
  (D : FrobeniusSplittingData p k n f ι)

/-- **Local Frobenius splittings of the logarithmic de Rham complex.** An open cover `U α` of `V`
with, on the opens inside each `U α`, Frobenius-semilinear maps `φ α : K¹ → K¹` whose values are
closed forms representing the inverse Cartier image (`φ α = F̃_α^*/p` for a Frobenius lift
`F̃_α` on a lifting of `U α`), and on the opens inside `U α ⊓ U β` Frobenius-semilinear
homotopies `η α β : K¹ → K⁰` with `φ β - φ α = d ∘ η α β` and the cocycle relation
`η α β + η β γ = η α γ` (Deligne–Illusie, §2). -/
structure LocalFrobeniusSplitting where
  /-- The index type of the cover. -/
  Chart : Type u
  /-- The cover. -/
  U : Chart → V.Opens
  iSup_U : ⨆ α, U α = ⊤
  /-- The local splittings `φ α = F̃_α^*/p`. -/
  φ (α : Chart) (W : V.Opens) : W ≤ U α → Γ(D.K 1, W) →+ Γ(D.K 1, W)
  φ_smul (α : Chart) (W : V.Opens) (hW : W ≤ U α) (r : Γ(V, W)) (s : Γ(D.K 1, W)) :
    φ α W hW (r • s) = r ^ p • φ α W hW s
  φ_res (α : Chart) (W₁ W₂ : V.Opens) (h₁ : W₁ ≤ U α) (h₂ : W₂ ≤ U α) (h : W₁ ≤ W₂)
    (s : Γ(D.K 1, W₂)) : φ α W₁ h₁ ((D.K 1).presheaf.map (homOfLE h).op s) =
      (D.K 1).presheaf.map (homOfLE h).op (φ α W₂ h₂ s)
  /-- The local splittings represent the inverse Cartier map. -/
  cartierRep_φ (α : Chart) (W : V.Opens) (hW : W ≤ U α) (s : Γ(D.K 1, W)) :
    D.cartierRep 1 W s (φ α W hW s)
  /-- The homotopies `η α β`. -/
  η (α β : Chart) (W : V.Opens) : W ≤ U α ⊓ U β → Γ(D.K 1, W) →+ Γ(D.K 0, W)
  η_smul (α β : Chart) (W : V.Opens) (hW : W ≤ U α ⊓ U β) (r : Γ(V, W)) (s : Γ(D.K 1, W)) :
    η α β W hW (r • s) = r ^ p • η α β W hW s
  η_res (α β : Chart) (W₁ W₂ : V.Opens) (h₁ : W₁ ≤ U α ⊓ U β) (h₂ : W₂ ≤ U α ⊓ U β)
    (h : W₁ ≤ W₂) (s : Γ(D.K 1, W₂)) :
    η α β W₁ h₁ ((D.K 1).presheaf.map (homOfLE h).op s) =
      (D.K 0).presheaf.map (homOfLE h).op (η α β W₂ h₂ s)
  φ_sub (α β : Chart) (W : V.Opens) (hW : W ≤ U α ⊓ U β) (s : Γ(D.K 1, W)) :
    φ β W (hW.trans inf_le_right) s - φ α W (hW.trans inf_le_left) s =
      (D.d 0).app W (η α β W hW s)
  η_add (α β γ : Chart) (W : V.Opens) (hW : W ≤ U α ⊓ U β ⊓ U γ) (s : Γ(D.K 1, W)) :
    η α β W (hW.trans inf_le_left) s +
        η β γ W (hW.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) s =
      η α γ W (hW.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) s

/-- The sections of `F_*M` over `W` are those of `M`, with `r` acting by `r ^ p`. -/
theorem pushforward_smul (M : V.Modules) (W : V.Opens) (r : Γ(V, W))
    (s : Γ((Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj M, W)) :
    (r • s : Γ((Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj M, W)) =
      (r ^ p • (show Γ(M, W) from s) : Γ(M, W)) := by
  change (show Γ(V, W) from (absoluteFrobenius V p D.hV).app W r) • (show Γ(M, W) from s) = _
  rw [absoluteFrobenius_app_apply]

/-- The `ℤ`-indexed complex `F_*K^•` of the decomposition. -/
abbrev complexZ : CochainComplex V.Modules ℤ := D.complex.extend ComplexShape.embeddingUpNat

/-- The term of degree `q` of the `ℤ`-indexed complex. -/
def complexZXIso (q : ℕ) : D.complexZ.X (q : ℤ) ≅ D.complex.X q :=
  D.complex.extendXIso ComplexShape.embeddingUpNat rfl

/-- The differential of the `ℤ`-indexed complex from degree `q` to `q + 1` corresponds to the
differential `d q` of `K^•`. -/
theorem complexZXIso_inv_d (q : ℕ) :
    (D.complexZXIso q).inv ≫ D.complexZ.d (q : ℤ) ((q + 1 : ℕ) : ℤ) =
      D.d q ≫ (D.complexZXIso (q + 1)).inv := by
  rw [HomologicalComplex.extend_d_eq _ _ (i' := (q : ℤ)) (j' := ((q + 1 : ℕ) : ℤ)) (i := q)
    (j := q + 1) rfl rfl, complexZXIso, Iso.inv_hom_id_assoc]
  exact congrArg (· ≫ _) (CochainComplex.of_d
    (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K q)) D.d q)

/-- The identification of the sections of `K^q` with those of the `ℤ`-indexed complex in
degree `q`. -/
def toComplexZ (q : ℕ) (W : V.Opens) : Γ(D.K q, W) →+ Γ(D.complexZ.X (q : ℤ), W) :=
  ((D.complexZXIso q).inv.app W).hom

/-- The identification `toComplexZ q W` is bijective. -/
theorem toComplexZ_bijective (q : ℕ) (W : V.Opens) : Function.Bijective (D.toComplexZ q W) := by
  refine Function.bijective_iff_has_inverse.2 ⟨((D.complexZXIso q).hom.app W).hom, fun x => ?_,
    fun x => ?_⟩
  · change ((D.complexZXIso q).inv ≫ (D.complexZXIso q).hom).app W x = x
    rw [Iso.inv_hom_id]
    rfl
  · change ((D.complexZXIso q).hom ≫ (D.complexZXIso q).inv).app W x = x
    rw [Iso.hom_inv_id]
    rfl

/-- The identification `toComplexZ q W` sends `r ^ p • s` to `r • toComplexZ q W s`. -/
theorem toComplexZ_pow_smul (q : ℕ) (W : V.Opens) (r : Γ(V, W)) (s : Γ(D.K q, W)) :
    D.toComplexZ q W (r ^ p • s) = r • D.toComplexZ q W s := by
  refine Eq.trans ?_ (Scheme.Modules.Hom.app_smul (D.complexZXIso q).inv r _)
  exact congrArg ((D.complexZXIso q).inv.app W) (D.pushforward_smul (D.K q) W r s).symm

/-- The identification `toComplexZ` commutes with restriction of sections. -/
theorem toComplexZ_res (q : ℕ) {W₁ W₂ : V.Opens} (h : W₁ ≤ W₂) (s : Γ(D.K q, W₂)) :
    D.toComplexZ q W₁ ((D.K q).presheaf.map (homOfLE h).op s) =
      (D.complexZ.X (q : ℤ)).presheaf.map (homOfLE h).op (D.toComplexZ q W₂ s) :=
  app_presheaf_map (D.complexZXIso q).inv (homOfLE h) s

/-- On sections, the differential of the `ℤ`-indexed complex corresponds under `toComplexZ` to
the differential `d q` of `K^•`. -/
theorem complexZ_d_toComplexZ (q : ℕ) (W : V.Opens) (s : Γ(D.K q, W)) :
    (D.complexZ.d (q : ℤ) ((q + 1 : ℕ) : ℤ)).app W (D.toComplexZ q W s) =
      D.toComplexZ (q + 1) W ((D.d q).app W s) :=
  congrArg (fun φ => φ.app W s) (D.complexZXIso_inv_d q)

namespace LocalFrobeniusSplitting

variable {D} (L : D.LocalFrobeniusSplitting)

/-- **The Čech gluing data of the local Frobenius splittings**, for `M = K¹` and the complex
`F_*K^•` in degree `0 + 1`. -/
def toCechGluingSections : CechGluingSections L.U D.complexZ (D.K 1) 0 where
  φ α W hW := (D.toComplexZ 1 W).comp (L.φ α W hW)
  φ_smul α W hW r s := (congrArg (D.toComplexZ 1 W) (L.φ_smul α W hW r s)).trans
    (D.toComplexZ_pow_smul 1 W r _)
  φ_res α W₁ W₂ h₁ h₂ h s := (congrArg (D.toComplexZ 1 W₁) (L.φ_res α W₁ W₂ h₁ h₂ h s)).trans
    (D.toComplexZ_res 1 h _)
  η α β W hW := (D.toComplexZ 0 W).comp (L.η α β W hW)
  η_smul α β W hW r s := (congrArg (D.toComplexZ 0 W) (L.η_smul α β W hW r s)).trans
    (D.toComplexZ_pow_smul 0 W r _)
  η_res α β W₁ W₂ h₁ h₂ h s :=
    (congrArg (D.toComplexZ 0 W₁) (L.η_res α β W₁ W₂ h₁ h₂ h s)).trans (D.toComplexZ_res 0 h _)
  φ_d α W hW s := by
    refine (D.complexZ_d_toComplexZ 1 W _).trans ?_
    exact (congrArg (D.toComplexZ (1 + 1) W)
      (D.cartierRep_d_eq_zero 1 (L.cartierRep_φ α W hW s))).trans
      (map_zero _)
  φ_sub α β W hW s := by
    refine Eq.trans ?_ (D.complexZ_d_toComplexZ 0 W _).symm
    change D.toComplexZ 1 W _ - D.toComplexZ 1 W _ = _
    rw [← map_sub, L.φ_sub α β W hW s]
  η_add α β γ W hW s := by
    change D.toComplexZ 0 W _ + D.toComplexZ 0 W _ = D.toComplexZ 0 W _
    rw [← map_add, L.η_add α β γ W hW s]

/-- **The Frobenius splitting `ψ₁ : K¹[-1] ⟶ F_*K^•` in the derived category**, glued from the
local splittings `φ α = F̃_α^*/p` along the homotopies `η α β`. -/
def psiOne : (DerivedCategory.singleFunctor V.Modules ((1 : ℕ) : ℤ)).obj (D.K 1) ⟶
    DerivedCategory.Q.obj D.complexZ :=
  L.toCechGluingSections.toCechGluingData.derivedMap L.iSup_U 0

/-- The map `K¹ ⟶ ℋ¹(F_*K^•)` induced by `ψ₁`. -/
def homologyMapOne : D.K 1 ⟶ D.complexZ.homology ((1 : ℕ) : ℤ) :=
  L.toCechGluingSections.toCechGluingData.homologyMap L.iSup_U 0

/-- The cohomology in degree `1` of `ψ₁` is `homologyMapOne`, up to the canonical
identifications. -/
theorem homologyFunctor_map_psiOne :
    (DerivedCategory.homologyFunctor V.Modules ((1 : ℕ) : ℤ)).map L.psiOne =
      (homologySingleIso ((1 : ℕ) : ℤ) (D.K 1)).hom ≫ L.homologyMapOne ≫
        ((DerivedCategory.homologyFunctorFactors V.Modules ((1 : ℕ) : ℤ)).app D.complexZ).inv :=
  L.toCechGluingSections.toCechGluingData.homologyFunctor_map_derivedMap L.iSup_U 0

/-- On an open `W ⊆ U α`, `homologyMapOne` sends `s` to the class of the cycle `φ α s` of the
`ℤ`-indexed complex. -/
theorem homologyMapOne_app_eq (α : L.Chart) {W : V.Opens} (hW : W ≤ L.U α)
    (s : Γ(D.K 1, W)) (z : Γ(D.complexZ.cycles ((1 : ℕ) : ℤ), W))
    (hz : (D.complexZ.iCycles ((1 : ℕ) : ℤ)).app W z = D.toComplexZ 1 W (L.φ α W hW s)) :
    L.homologyMapOne.app W s = (D.complexZ.homologyπ ((1 : ℕ) : ℤ)).app W z :=
  L.toCechGluingSections.homologyMap_app_eq L.iSup_U 0 α hW s z hz

/-- **The local description of `ψ₁` on `ℋ¹`.** On an open `W ⊆ U α`, the composite of
`homologyMapOne` with the identification `ℋ¹` of the `ℤ`-indexed complex with `ℋ¹(F_*K^•)` sends
a section `s` of `K¹` to the class of any cycle `z` with `z = φ α s`; and `φ α s` represents the
inverse Cartier image of `s` (the field `cartierRep_φ`). -/
theorem homologyMapOne_comp_extendHomologyIso_app_eq (α : L.Chart) {W : V.Opens}
    (hW : W ≤ L.U α) (s : Γ(D.K 1, W)) (z : ToType ((D.complex.cycles 1).val.obj (op W)))
    (hz : (D.complex.iCycles 1).val.app (op W) z = L.φ α W hW s) :
    (L.homologyMapOne ≫ (D.complex.extendHomologyIso ComplexShape.embeddingUpNat
        (j := 1) (j' := ((1 : ℕ) : ℤ)) rfl).hom).val.app (op W) s =
      (D.complex.homologyπ 1).val.app (op W) z := by
  set e := ComplexShape.embeddingUpNat
  let z' := (D.complex.extendCyclesIso e (j := 1) (j' := ((1 : ℕ) : ℤ)) rfl).inv.app W z
  have hz' : (D.complexZ.iCycles ((1 : ℕ) : ℤ)).app W z' = D.toComplexZ 1 W (L.φ α W hW s) := by
    have h := congrArg (fun φ => φ.app W z)
      (D.complex.extendCyclesIso_inv_iCycles e (j := 1) (j' := ((1 : ℕ) : ℤ)) rfl)
    exact h.trans (congrArg ((D.complexZXIso 1).inv.app W) hz)
  have h1 := L.homologyMapOne_app_eq α hW s z' hz'
  have h2 := congrArg (fun φ => φ.app W z')
    (D.complex.homologyπ_extendHomologyIso_hom e (j := 1) (j' := ((1 : ℕ) : ℤ)) rfl)
  have h3 := congrArg (fun φ => φ.app W z)
    (D.complex.extendCyclesIso e (j := 1) (j' := ((1 : ℕ) : ℤ)) rfl).inv_hom_id
  change (D.complex.extendHomologyIso e rfl).hom.app W (L.homologyMapOne.app W s) = _
  rw [h1]
  exact h2.trans (congrArg ((D.complex.homologyπ 1).app W) h3)

end LocalFrobeniusSplitting

/-- A morphism `K⁰ ⟶ F_*K⁰` representing the inverse Cartier map in degree `0` lands in the
cycles. -/
theorem comp_d_eq_zero_of_cartierRep
    (c₀ : D.K 0 ⟶ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K 0))
    (hc₀ : ∀ (W : V.Opens) (s : Γ(D.K 0, W)), D.cartierRep 0 W s (c₀.app W s)) :
    c₀ ≫ D.d 0 = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext s
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app, AddCommGrpCat.hom_comp,
    AddCommGrpCat.hom_zero, AddMonoidHom.comp_apply, AddMonoidHom.zero_apply]
  exact D.cartierRep_d_eq_zero 0 (hc₀ W s)

/-- A morphism `c₀ : K⁰ ⟶ F_*K⁰` representing the inverse Cartier map in degree `0`, viewed in
degree `0` of the `ℤ`-indexed complex, composes to zero with its differential. -/
theorem comp_complexZXIso_inv_d
    (c₀ : D.K 0 ⟶ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K 0))
    (hc₀ : ∀ (W : V.Opens) (s : Γ(D.K 0, W)), D.cartierRep 0 W s (c₀.app W s)) (j : ℤ)
    (hj : (ComplexShape.up ℤ).Rel ((0 : ℕ) : ℤ) j) :
    (c₀ ≫ (D.complexZXIso 0).inv) ≫ D.complexZ.d ((0 : ℕ) : ℤ) j = 0 := by
  obtain rfl : ((0 + 1 : ℕ) : ℤ) = j := hj
  rw [Category.assoc, D.complexZXIso_inv_d 0, ← Category.assoc,
    D.comp_d_eq_zero_of_cartierRep c₀ hc₀, zero_comp]

/-- **The Frobenius splitting `ψ₀ : K⁰ ⟶ F_*K^•` in the derived category**, induced by a
morphism `c₀ : K⁰ ⟶ F_*K⁰` representing the inverse Cartier map in degree `0`, that is the
`p`-th power map `a ↦ a ^ p`. -/
def psiZero (c₀ : D.K 0 ⟶ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K 0))
    (hc₀ : ∀ (W : V.Opens) (s : Γ(D.K 0, W)), D.cartierRep 0 W s (c₀.app W s)) :
    (DerivedCategory.singleFunctor V.Modules ((0 : ℕ) : ℤ)).obj (D.K 0) ⟶
      DerivedCategory.Q.obj D.complexZ :=
  (DerivedCategory.singleFunctorIsoCompQ V.Modules ((0 : ℕ) : ℤ)).hom.app (D.K 0) ≫
    DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle (c₀ ≫ (D.complexZXIso 0).inv)
      (D.comp_complexZXIso_inv_d c₀ hc₀))

end FrobeniusSplittingData

end MMP.DeRham
