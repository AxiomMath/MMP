module
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous

/-!
# Depth over a finite extension of a local ring

Let `(A, 𝔪_A)` be a Noetherian local ring, `A → B` a finite ring homomorphism and `M ≠ 0` a
finite `B`-module, hence a finite `A`-module. Then the depth of `M` over `A` is the minimum of
the depths of the localizations `M_𝔓` over the local rings `B_𝔓`, where `𝔓` runs over the
maximal ideals of `B` with `M_𝔓 ≠ 0`.

## Main results

* `MMP.Mori.localDepth_eq_iInf_localDepth_localization`: the depth formula above.

## Implementation notes

The localizations are not fixed constructions: for each maximal ideal `𝔓` of `B` the statement
takes any localization `B_𝔓` of `B` at `𝔓` (`IsLocalization.AtPrime`) and any localization
`f_𝔓 : M → M_𝔓` of `M` at `𝔓` (`IsLocalizedModule`) carrying a compatible `B_𝔓`-module
structure. The minimum over the maximal ideals with `M_𝔓 ≠ 0` is an infimum in `ℕ∞` over the
maximal ideals `𝔓` of `B` such that `M_𝔓` is nontrivial.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 5.4
-/

namespace MMP.Mori

open IsLocalRing RingTheory.Sequence Pointwise

/-- If a prime `p` of a Noetherian ring `B` is an associated prime of `M`, then the localization
`M_p` is nonzero and has depth zero over `B_p`. -/
private theorem nontrivial_and_localDepth_eq_zero_of_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsNoetherianRing B] (p : Ideal B) [p.IsPrime]
    (Bₚ : Type*) [CommRing Bₚ] [Algebra B Bₚ] [IsLocalization.AtPrime Bₚ p] [IsLocalRing Bₚ]
    {M : Type*} [AddCommGroup M] [Module B M]
    {Mₚ : Type*} [AddCommGroup Mₚ] [Module B Mₚ] [Module Bₚ Mₚ] [IsScalarTower B Bₚ Mₚ]
    (f : M →ₗ[B] Mₚ) [IsLocalizedModule p.primeCompl f] (hp : p ∈ associatedPrimes B M) :
    Nontrivial Mₚ ∧ localDepth Bₚ Mₚ = 0 := by
  have : IsNoetherianRing Bₚ := IsLocalization.isNoetherianRing p.primeCompl Bₚ ‹_›
  have hass : maximalIdeal Bₚ ∈ associatedPrimes Bₚ Mₚ :=
    Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      p.primeCompl f _ (by rwa [← Ideal.under_def, IsLocalization.AtPrime.under_maximalIdeal Bₚ p])
  refine ⟨?_, ?_⟩
  · by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    simp [associatedPrimes.eq_empty_of_subsingleton] at hass
  · refine nonpos_iff_eq_zero.mp (iSup₂_le fun xs hxs => ?_)
    rcases xs with _ | ⟨x, xs⟩
    · simp
    · exfalso
      have hreg := ((isWeaklyRegular_cons_iff Mₚ x xs).mp hxs.2).1
      have hx : x ∈ ⋃ q ∈ associatedPrimes Bₚ Mₚ, (q : Set Bₚ) :=
        Set.mem_biUnion hass (hxs.1 x List.mem_cons_self)
      rw [biUnion_associatedPrimes_eq_compl_regular] at hx
      exact hx hreg

/-- The localization of `b • ⊤` is `b • ⊤`. -/
private theorem localized'_smul_top {B : Type*} [CommRing B] (S : Submonoid B)
    (Bₚ : Type*) [CommRing Bₚ] [Algebra B Bₚ] [IsLocalization S Bₚ]
    {M : Type*} [AddCommGroup M] [Module B M]
    {Mₚ : Type*} [AddCommGroup Mₚ] [Module B Mₚ] [Module Bₚ Mₚ] [IsScalarTower B Bₚ Mₚ]
    (f : M →ₗ[B] Mₚ) [IsLocalizedModule S f] (b : B) :
    (b • (⊤ : Submodule B M)).localized' Bₚ S f = algebraMap B Bₚ b • (⊤ : Submodule Bₚ Mₚ) := by
  rw [← Submodule.ideal_span_singleton_smul, Submodule.localized'_smul, Submodule.localized'_top,
    Ideal.span, Submodule.localized'_span, Set.image_singleton,
    ← Submodule.ideal_span_singleton_smul]
  rfl

section Induction

universe u w

variable {A : Type*} [CommRing A] [IsLocalRing A] {B : Type*} [CommRing B] [Algebra A B]
  [Algebra.IsIntegral A B] [IsNoetherianRing B]
  (Bₚ : MaximalSpectrum B → Type*) [∀ P, CommRing (Bₚ P)] [∀ P, Algebra B (Bₚ P)]
  [∀ P, IsLocalization.AtPrime (Bₚ P) P.asIdeal] [∀ P, IsLocalRing (Bₚ P)]

omit [IsNoetherianRing B] in
/-- Over an integral extension of a local ring, every maximal ideal lies over the maximal
ideal. -/
private theorem algebraMap_mem_of_mem_maximalIdeal (P : MaximalSpectrum B) {a : A}
    (ha : a ∈ maximalIdeal A) : algebraMap A B a ∈ P.asIdeal := by
  have := P.isMaximal
  have := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) P.asIdeal
  rw [← Ideal.mem_comap, ← Ideal.under_def, IsLocalRing.eq_maximalIdeal this]
  exact ha

/-- If every nonzero localization `M_𝔓` at a maximal ideal has depth at least `k`, then `M` has
a weakly regular sequence of length `k` in the maximal ideal of `A`. -/
private theorem exists_isWeaklyRegular_of_le_localDepth (k : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M]
      (Mₚ : MaximalSpectrum B → Type w) [∀ P, AddCommGroup (Mₚ P)] [∀ P, Module B (Mₚ P)]
      [∀ P, Module (Bₚ P) (Mₚ P)] [∀ P, IsScalarTower B (Bₚ P) (Mₚ P)]
      (f : ∀ P, M →ₗ[B] Mₚ P) [∀ P, IsLocalizedModule P.asIdeal.primeCompl (f P)],
      (∀ P, Nontrivial (Mₚ P) → (k : ℕ∞) ≤ localDepth (Bₚ P) (Mₚ P)) →
      ∃ xs : List A, (∀ x ∈ xs, x ∈ maximalIdeal A) ∧ xs.length = k ∧
        IsWeaklyRegular M (xs.map (algebraMap A B)) := by
  induction k with
  | zero => intro M _ _ _ Mₚ _ _ _ _ f _ _; exact ⟨[], by simp, rfl, by simp⟩
  | succ k ih =>
    intro M _ _ _ Mₚ _ _ _ _ f _ h
    obtain ⟨y, hy, hreg⟩ : ∃ y ∈ maximalIdeal A, IsSMulRegular M (algebraMap A B y) := by
      by_contra! H
      have hsub : ((maximalIdeal A : Ideal A) : Set A) ⊆
          ⋃ Q ∈ associatedPrimes B M, (Q.comap (algebraMap A B) : Set A) := by
        intro a ha
        have : algebraMap A B a ∈ ⋃ Q ∈ associatedPrimes B M, (Q : Set B) := by
          rw [biUnion_associatedPrimes_eq_compl_regular]
          exact H a ha
        simpa using this
      obtain ⟨Q, hQ, hle⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite B M) ⊥ ⊥
        (fun Q hQ _ _ => (hQ : IsAssociatedPrime Q M).isPrime.comap _)).mp hsub
      have hQp := (hQ : IsAssociatedPrime Q M).isPrime
      have hcomap : Q.comap (algebraMap A B) = maximalIdeal A :=
        ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.comap _).ne_top hle).symm
      have hQmax : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) Q
        (by rw [Ideal.under_def, hcomap]; exact maximalIdeal.isMaximal A)
      obtain ⟨hnt, h0⟩ := nontrivial_and_localDepth_eq_zero_of_mem_associatedPrimes
        (p := (⟨Q, hQmax⟩ : MaximalSpectrum B).asIdeal) (Bₚ ⟨Q, hQmax⟩) (f ⟨Q, hQmax⟩) hQ
      have := h ⟨Q, hQmax⟩ hnt
      rw [h0] at this
      simp at this
    set b := algebraMap A B y
    obtain ⟨ys, hys, hlen, hreg'⟩ := ih (QuotSMulTop b M)
      (fun P => Mₚ P ⧸ (b • (⊤ : Submodule B M)).localized' (Bₚ P) P.asIdeal.primeCompl (f P))
      (fun P => (b • (⊤ : Submodule B M)).toLocalizedQuotient' (Bₚ P) P.asIdeal.primeCompl (f P))
      (fun P hP => by
        have hnt : Nontrivial (Mₚ P) := by
          by_contra hc
          rw [not_nontrivial_iff_subsingleton] at hc
          exact not_subsingleton _ (Submodule.Quotient.mk_surjective
            ((b • (⊤ : Submodule B M)).localized' (Bₚ P) P.asIdeal.primeCompl (f P))).subsingleton
        have hbP : algebraMap B (Bₚ P) b ∈ maximalIdeal (Bₚ P) :=
          (IsLocalization.AtPrime.to_map_mem_maximal_iff (Bₚ P) P.asIdeal b).mpr
            (algebraMap_mem_of_mem_maximalIdeal P hy)
        have hregP : IsSMulRegular (Mₚ P) (algebraMap B (Bₚ P) b) := by
          have := IsWeaklyRegular.of_isLocalizedModule (Bₚ P) P.asIdeal.primeCompl (f P)
            (rs := [b]) ((isWeaklyRegular_cons_iff M b []).mpr ⟨hreg, by simp⟩)
          simpa using this
        have : IsNoetherianRing (Bₚ P) :=
          IsLocalization.isNoetherianRing P.asIdeal.primeCompl (Bₚ P) ‹_›
        have : Module.Finite (Bₚ P) (Mₚ P) :=
          Module.Finite.of_isLocalizedModule P.asIdeal.primeCompl (f P)
        have hk := h P hnt
        rw [← localDepth_quotSMulTop_add_one hbP hregP] at hk
        show (k : ℕ∞) ≤ localDepth (Bₚ P)
          (Mₚ P ⧸ (b • (⊤ : Submodule B M)).localized' (Bₚ P) P.asIdeal.primeCompl (f P))
        rw [localized'_smul_top]
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp (by simpa using hk))
    refine ⟨y :: ys, ?_, by simp [hlen], ?_⟩
    · exact List.forall_mem_cons.mpr ⟨hy, hys⟩
    · simpa [isWeaklyRegular_cons_iff] using ⟨hreg, hreg'⟩

end Induction

/-- Let `A` be a Noetherian local ring, `B` a finite `A`-algebra and `M ≠ 0` a finite
`B`-module. Then the depth of `M` as an `A`-module is the infimum, over the maximal ideals `𝔓`
of `B` with `M_𝔓 ≠ 0`, of the depth of `M_𝔓` over the local ring `B_𝔓`. -/
@[mmp "lem_km5a_depth_finite_semilocal"]
public theorem localDepth_eq_iInf_localDepth_localization
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (B : Type*) [CommRing B] [Algebra A B] [Module.Finite A B]
    (M : Type*) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] [Nontrivial M]
    (Bₚ : MaximalSpectrum B → Type*) [∀ P, CommRing (Bₚ P)] [∀ P, Algebra B (Bₚ P)]
    [∀ P, IsLocalization.AtPrime (Bₚ P) P.asIdeal]
    (Mₚ : MaximalSpectrum B → Type*) [∀ P, AddCommGroup (Mₚ P)] [∀ P, Module B (Mₚ P)]
    [∀ P, Module (Bₚ P) (Mₚ P)] [∀ P, IsScalarTower B (Bₚ P) (Mₚ P)]
    (f : ∀ P, M →ₗ[B] Mₚ P) [∀ P, IsLocalizedModule P.asIdeal.primeCompl (f P)] :
    haveI (P : MaximalSpectrum B) : IsLocalRing (Bₚ P) :=
      IsLocalization.AtPrime.isLocalRing (Bₚ P) P.asIdeal
    localDepth A M = ⨅ (P : MaximalSpectrum B) (_ : Nontrivial (Mₚ P)),
      localDepth (Bₚ P) (Mₚ P) := by
  haveI : ∀ P, IsLocalRing (Bₚ P) := fun P => IsLocalization.AtPrime.isLocalRing (Bₚ P) P.asIdeal
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  refine le_antisymm (le_iInf₂ fun P _ => iSup₂_le fun xs hxs => ?_) ?_
  · have hreg : IsRegularSequence (Bₚ P) (Mₚ P)
        ((xs.map (algebraMap A B)).map (algebraMap B (Bₚ P))) := by
      refine ⟨fun x hx => ?_, IsWeaklyRegular.of_isLocalizedModule (Bₚ P) P.asIdeal.primeCompl
        (f P) ((isWeaklyRegular_map_algebraMap_iff B M xs).mpr hxs.2)⟩
      simp only [List.map_map, List.mem_map, Function.comp_apply] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Bₚ P) P.asIdeal _).mpr
        (algebraMap_mem_of_mem_maximalIdeal (A := A) P (hxs.1 a ha))
    simpa using hreg.length_le_localDepth
  · refine ENat.forall_natCast_le_iff_le.mp fun k hk => ?_
    obtain ⟨xs, hmem, hlen, hreg⟩ := exists_isWeaklyRegular_of_le_localDepth (A := A) Bₚ k M Mₚ f
      fun P hP => (le_iInf₂_iff.mp hk) P hP
    rw [← hlen]
    exact IsRegularSequence.length_le_localDepth
      ⟨hmem, (isWeaklyRegular_map_algebraMap_iff B M xs).mp hreg⟩

end MMP.Mori
