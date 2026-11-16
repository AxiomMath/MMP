module

public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
public import MMP.Algebra.Homology.ComplexDeterminant

/-!
# Poincaré residues of sections of `ω_X(S)` are regular

Let `X` be a normal variety of dimension `n + 1` over a field of characteristic zero, `S ⊂ X` a
normal prime divisor and `Q` a codimension-one point of `S`, with image `x ∈ X`. A rational top
form `α` on `X` with at most a simple pole along `S` and no pole along any other prime divisor
through `x` is a section of `ω_X(S)` near `x`; its Poincaré residue along `S` has no pole at `Q`.
Together with `MMP.Fourfold.exists_isPoincareResidue_of_le_ordForm` this says that the residue maps
the stalk `ω_X(S)_x` onto `ω_{S,Q}`.

## Main results

* `MMP.Fourfold.zero_le_ordForm_of_isPoincareResidue`: the Poincaré residue of a section of
  `ω_X(S)` near `x` is regular at `Q`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.4–16.5
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP MMP.Mori

/-! ### Traces in finite free algebras over a local ring -/

/-- In a finite algebra `S` over a local ring `O`, some element lies outside a given maximal
ideal `E` and in every other maximal ideal. -/
private theorem exists_notMem_and_forall_mem {O S : Type*} [CommRing O] [IsLocalRing O]
    [CommRing S] [Algebra O S] [Module.Finite O S] (E : Ideal S) [E.IsMaximal] :
    ∃ a : S, a ∉ E ∧ ∀ M : Ideal S, M.IsMaximal → M ≠ E → a ∈ M := by
  classical
  set I := (IsLocalRing.maximalIdeal O).map (algebraMap O S) with hIdef
  haveI : Algebra.IsIntegral O S := Algebra.IsIntegral.of_finite O S
  have hIM : ∀ M : Ideal S, M.IsMaximal → I ≤ M := fun M _ => map_maximalIdeal_le M
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal O)
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : IsArtinianRing (S ⧸ I) := IsArtinianRing.of_finite (O ⧸ IsLocalRing.maximalIdeal O) _
  have hfin : {M : Ideal S | M.IsMaximal ∧ M ≠ E}.Finite := by
    refine Set.Finite.of_finite_image (f := Ideal.map (Ideal.Quotient.mk I)) ?_ ?_
    · refine (IsArtinianRing.setOfPred_isMaximal_finite (S ⧸ I)).subset ?_
      rintro _ ⟨M, ⟨hM, -⟩, rfl⟩
      haveI := hM
      exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hIM M hM)
    · intro M hM M' hM' h
      have h1 := congrArg (Ideal.comap (Ideal.Quotient.mk I)) h
      rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
        Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        sup_eq_left.mpr (hIM M hM.1), sup_eq_left.mpr (hIM M' hM'.1)] at h1
  set s := hfin.toFinset
  have hnle : ¬ s.inf id ≤ E := by
    intro h
    obtain ⟨M, hMs, hME⟩ := (Ideal.IsPrime.inf_le' (Ideal.IsMaximal.isPrime inferInstance)).mp h
    rw [Set.Finite.mem_toFinset] at hMs
    exact hMs.2 (hMs.1.eq_of_le (Ideal.IsMaximal.ne_top inferInstance) hME)
  obtain ⟨a, ha, haE⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨a, haE, fun M hM hME => ?_⟩
  have hMs : M ∈ s := by rw [Set.Finite.mem_toFinset]; exact ⟨hM, hME⟩
  exact Finset.inf_le (f := id) hMs ha

/-- **Elements of the Jacobson radical have trace in `𝔪`.** In a finite free algebra `S` over a
local ring `O`, an element lying in every maximal ideal of `S` has trace in `𝔪_O`. -/
private theorem trace_mem_maximalIdeal_of_forall_mem {O S : Type*} [CommRing O] [IsLocalRing O]
    [CommRing S] [Algebra O S] [Module.Free O S] [Module.Finite O S] {z : S}
    (hz : ∀ M : Ideal S, M.IsMaximal → z ∈ M) :
    Algebra.trace O S z ∈ IsLocalRing.maximalIdeal O := by
  classical
  set I := (IsLocalRing.maximalIdeal O).map (algebraMap O S) with hIdef
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal O)
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) :=
    Module.Finite.of_restrictScalars_finite O _ _
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_mk]
  apply trace_eq_zero_of_mem_jacobson
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro M ⟨-, hM⟩
  have hE : (M.comap (Ideal.Quotient.mk I)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  exact hz _ hE

/-- **The trace form detects maximal ideals.** Let `S` be a finite free algebra over a local ring
`O` whose residue field has characteristic zero, and `E` a maximal ideal of `S`. If
`Tr_{S/O}(y s) ∈ 𝔪_O` for every `s ∈ S`, then `y ∈ E`: otherwise `z = y s ≡ 1` modulo `E` and
`z ∈ M` for the other maximal ideals `M` is an idempotent modulo the nilpotent radical of
`S / 𝔪_O S`, and its trace is the (nonzero) rank of the corresponding factor. -/
private theorem mem_of_forall_trace_mul_mem {O S : Type*} [CommRing O] [IsLocalRing O]
    [CommRing S] [Algebra O S] [Module.Free O S] [Module.Finite O S]
    [CharZero (O ⧸ IsLocalRing.maximalIdeal O)] (E : Ideal S) [E.IsMaximal] {y : S}
    (hy : ∀ s : S, Algebra.trace O S (y * s) ∈ IsLocalRing.maximalIdeal O) : y ∈ E := by
  classical
  by_contra hyE
  obtain ⟨a, haE, ha⟩ := exists_notMem_and_forall_mem (O := O) E
  obtain ⟨r, i, hi, hri⟩ := Ideal.IsMaximal.exists_inv ‹E.IsMaximal›
    (fun h => (Ideal.IsPrime.mem_or_mem (Ideal.IsMaximal.isPrime inferInstance) h).elim hyE haE :
      y * a ∉ E)
  set z := y * (a * r) with hzdef
  have hzE : z - 1 ∈ E := by
    rw [show z - 1 = -i by rw [hzdef]; linear_combination hri]
    exact E.neg_mem hi
  have hzM : ∀ M : Ideal S, M.IsMaximal → M ≠ E → z ∈ M := fun M hM hME =>
    M.mul_mem_left _ (M.mul_mem_right _ (ha M hM hME))
  set I := (IsLocalRing.maximalIdeal O).map (algebraMap O S) with hIdef
  haveI : Algebra.IsIntegral O S := Algebra.IsIntegral.of_finite O S
  have hIM : ∀ M : Ideal S, M.IsMaximal → I ≤ M := fun M _ => map_maximalIdeal_le M
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal O)
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : IsArtinianRing (S ⧸ I) := IsArtinianRing.of_finite (O ⧸ IsLocalRing.maximalIdeal O) _
  set z' : (S ⧸ I) := Ideal.Quotient.mk I z with hz'def
  -- `z'` is idempotent modulo the Jacobson radical
  let f := Ideal.Quotient.mk (Ideal.jacobson (⊥ : Ideal (S ⧸ I)))
  have hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x := by
    intro x hx
    rw [Ideal.mk_ker, IsArtinianRing.jacobson_eq_radical, Ideal.mem_radical_iff] at hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, by simpa using hn⟩
  have hidem : IsIdempotentElem (f z') := by
    rw [IsIdempotentElem, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    have hE : (M.comap (Ideal.Quotient.mk I)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    change z * z - z ∈ M.comap (Ideal.Quotient.mk I)
    rw [show z * z - z = z * (z - 1) by ring]
    by_cases hME : M.comap (Ideal.Quotient.mk I) = E
    · rw [hME]
      exact E.mul_mem_left _ hzE
    · exact Ideal.mul_mem_right _ _ (hzM _ hE hME)
  obtain ⟨e, he, hfe⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f hnil (f z')
    ⟨z', rfl⟩ hidem
  have hez : IsNilpotent (z' - e) := hnil _ (by rw [RingHom.mem_ker, map_sub, hfe, sub_self])
  -- the trace of `z'` is that of `e`
  have htr : Algebra.trace (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) z' =
      Algebra.trace (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) e := by
    have h0 : Algebra.trace (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) (z' - e) = 0 := by
      rw [Algebra.trace_apply]
      exact (LinearMap.isNilpotent_trace_of_isNilpotent
        (hez.map (Algebra.lmul (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I)))).eq_zero
    rwa [map_sub, sub_eq_zero] at h0
  have hz0 : Algebra.trace (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) z' = 0 := by
    rw [hz'def, Algebra.trace_quotient_mk, Ideal.Quotient.eq_zero_iff_mem, hzdef]
    exact hy _
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [sub_zero] at hez
    obtain ⟨k, hk⟩ := hez
    have : z ^ k ∈ E :=
      hIM E inferInstance (by rwa [← Ideal.Quotient.eq_zero_iff_mem, map_pow])
    have hzE' : z ∈ E := (Ideal.IsMaximal.isPrime inferInstance).mem_of_pow_mem k this
    exact (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr
      (by simpa using E.sub_mem hzE' hzE))
  have hlmul : IsIdempotentElem (Algebra.lmul (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) e) := by
    rw [IsIdempotentElem, ← map_mul, he.eq]
  have hne : Algebra.lmul (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) e ≠ 0 := fun h =>
    he0 (by simpa using LinearMap.congr_fun h 1)
  haveI := Module.Free.of_divisionRing (O ⧸ IsLocalRing.maximalIdeal O)
    (LinearMap.range (Algebra.lmul (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) e))
  haveI := Module.Free.of_divisionRing (O ⧸ IsLocalRing.maximalIdeal O)
    (LinearMap.ker (Algebra.lmul (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) e))
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O)
      (LinearMap.range (Algebra.lmul (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) e)) :=
    Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O)
      (LinearMap.ker (Algebra.lmul (O ⧸ IsLocalRing.maximalIdeal O) (S ⧸ I) e)) :=
    Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  apply hne
  apply LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hlmul
  rw [← Algebra.trace_apply, ← htr, hz0]

/-- **Algebraic Hartogs over a factorial domain.** An element of the fraction field of a
factorial domain `C` which is regular at every prime element (a fraction with denominator prime to
it) lies in `C`. -/
private theorem exists_eq_algebraMap_of_forall_prime {C F : Type*} [CommRing C] [IsDomain C]
    [UniqueFactorizationMonoid C] [Field F] [Algebra C F] [IsFractionRing C F] (x : F)
    (hx : ∀ π : C, Prime π → ∃ c d : C, ¬ π ∣ d ∧ x * algebraMap C F d = algebraMap C F c) :
    ∃ c : C, x = algebraMap C F c := by
  obtain ⟨a, b, hab, rfl⟩ := IsFractionRing.exists_reduced_fraction C x
  have hb0 : (b : C) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  by_cases hbu : IsUnit (b : C)
  · refine ⟨a * ↑hbu.unit⁻¹, ?_⟩
    rw [IsLocalization.mk'_eq_iff_eq_mul, map_mul, mul_assoc, ← map_mul]
    simp
  exfalso
  obtain ⟨π, hπirr, hπb⟩ := WfDvdMonoid.exists_irreducible_factor hbu hb0
  have hπ : Prime π := UniqueFactorizationMonoid.irreducible_iff_prime.mp hπirr
  obtain ⟨c, d, hπd, hcd⟩ := hx π hπ
  have hrel : a * d = c * b := by
    apply IsFractionRing.injective C F
    rw [map_mul, map_mul, ← hcd, mul_comm (IsLocalization.mk' F a b), mul_assoc,
      IsLocalization.mk'_spec_mk, mul_comm]
  have hπa : π ∣ a := by
    have : π ∣ a * d := hrel ▸ dvd_mul_of_dvd_right hπb c
    exact (hπ.dvd_or_dvd this).resolve_right hπd
  exact hπirr.not_isUnit (hab hπa hπb)

/-- **The trace of an element of every prime over `q`.** Let `B` be finite free over a ring
`C` and `q` a prime of `C`. An element of `B` lying in every prime of `B` over `q` has trace in
`q`: over the localization `C_q` it lies in every maximal ideal of `B_q`. -/
private theorem trace_mem_of_forall_liesOver {C B : Type*} [CommRing C] [CommRing B]
    [Algebra C B] [Module.Free C B] [Module.Finite C B] (q : Ideal C) [q.IsPrime] {z : B}
    (hz : ∀ E : Ideal B, E.IsPrime → E.comap (algebraMap C B) = q → z ∈ E) :
    Algebra.trace C B z ∈ q := by
  classical
  let O := Localization.AtPrime q
  let S := Localization (Algebra.algebraMapSubmonoid B q.primeCompl)
  letI : Algebra O S := localizationAlgebra q.primeCompl B
  haveI : IsScalarTower C O S := IsScalarTower.of_algebraMap_eq fun c => by
    simp only [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply C B S]
    exact (IsLocalization.map_eq _ _).symm
  let b := Module.Free.chooseBasis C B
  let bS := b.localizationLocalization O q.primeCompl S
  haveI : Module.Free O S := Module.Free.of_basis bS
  haveI : Module.Finite O S := Module.Finite.of_basis bS
  haveI : Algebra.IsIntegral C B := Algebra.IsIntegral.of_finite C B
  haveI : Algebra.IsIntegral O S := Algebra.IsIntegral.of_finite O S
  have key : Algebra.trace O S (algebraMap B S z) ∈ IsLocalRing.maximalIdeal O := by
    apply trace_mem_maximalIdeal_of_forall_mem
    intro M hM
    set P := M.comap (algebraMap B S) with hPdef
    haveI : P.IsPrime := Ideal.comap_isPrime _ _
    have hMO : M.comap (algebraMap O S) = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) M)
    have hPq : P.comap (algebraMap C B) = q := by
      rw [hPdef, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq C O S, ← Ideal.comap_comap, hMO]
      exact Localization.AtPrime.under_maximalIdeal
    exact hz P inferInstance hPq
  rw [Algebra.trace_localization C q.primeCompl] at key
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff O q _).mp key

open nonZeroDivisors in
/-- **Codifferent bounds make the trace integral.** Let `B` be a domain finite free over a
factorial domain `C`, with fraction fields `K / F`. If `x ∈ K` has `x π ∈ E B_E` at every prime `E`
of `B` over a prime element `π` of `C`, then `Tr_{K/F}(x) ∈ C`: at each `(π)`, clearing a
denominator prime to `π` gives `z = x π d ∈ B` in every prime over `(π)`, whose trace lies in `(π)`
(`trace_mem_of_forall_liesOver`); then `C` is the intersection of the `C_(π)`. -/
private theorem exists_trace_eq_of_forall_mul_mem {C B F K : Type*} [CommRing C] [IsDomain C]
    [UniqueFactorizationMonoid C] [CommRing B] [IsDomain B] [Algebra C B] [Module.Free C B]
    [Module.Finite C B] [FaithfulSMul C B] [Field F] [Algebra C F] [IsFractionRing C F] [Field K]
    [Algebra B K] [Algebra F K] [Algebra C K] [IsScalarTower C F K] [IsScalarTower C B K]
    [IsLocalization (Algebra.algebraMapSubmonoid B C⁰) K] (x : K)
    (hx : ∀ (E : Ideal B) [E.IsPrime] (π : C), Prime π →
      E.comap (algebraMap C B) = Ideal.span {π} →
        ∃ s ∉ E, ∃ a ∈ E, x * algebraMap C K π * algebraMap B K s = algebraMap B K a) :
    ∃ c : C, Algebra.trace F K x = algebraMap C F c := by
  classical
  haveI : Algebra.IsIntegral C B := Algebra.IsIntegral.of_finite C B
  have hCB : Function.Injective (algebraMap C B) := FaithfulSMul.algebraMap_injective C B
  have hBK : Function.Injective (algebraMap B K) :=
    IsLocalization.injective K
      (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul (A := C) B le_rfl)
  apply exists_eq_algebraMap_of_forall_prime
  intro π hπ
  set q := Ideal.span {π} with hqdef
  haveI : q.IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  obtain ⟨d, hdq, z, hz⟩ := exists_mul_mem_of_forall_liesOver (K := K) q
    (x * algebraMap C K π) fun E hE hEq => by
      obtain ⟨s, hs, a, -, h⟩ := hx E π hπ hEq
      exact ⟨s, hs, a, h⟩
  have hzE : ∀ E : Ideal B, E.IsPrime → E.comap (algebraMap C B) = q → z ∈ E := by
    intro E hE hEq
    obtain ⟨s, hs, a, ha, h⟩ := hx E π hπ hEq
    have hzs : z * s = algebraMap C B d * a := by
      apply hBK
      rw [map_mul, map_mul, ← hz, ← h]
      ring
    have : z * s ∈ E := hzs ▸ E.mul_mem_left _ ha
    exact (hE.mem_or_mem this).resolve_right hs
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (trace_mem_of_forall_liesOver q hzE)
  refine ⟨c, d, fun h => hdq (Ideal.mem_span_singleton.mpr h), ?_⟩
  have htr := Algebra.trace_localization (Rₘ := F) (Sₘ := K) C C⁰ z
  have hzK : algebraMap B K z = (algebraMap C F (π * d)) • x := by
    rw [← hz, ← IsScalarTower.algebraMap_apply C B K, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply C F K, map_mul]
    ring
  rw [hzK, LinearMap.map_smul, smul_eq_mul, ← hc, map_mul, map_mul] at htr
  have hπ0 : algebraMap C F π ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)
  apply mul_left_cancel₀ hπ0
  linear_combination htr

/-- **A trace bound on a fraction at one maximal ideal.** Let `S` be finite free over a local
domain `O` of residue characteristic zero, `Q` a maximal ideal of `S` and `f : S → T` an injective
map to a discrete valuation ring through which `T` is the localization of `S` at `Q`. Let `y ∈ S`,
`d ≠ 0` in `O` and `N > 0` with `N Tr(y r) ∈ d O` for every `r ∈ S`, and `a, s ∈ T`, `s ≠ 0`, with
`y s = d a`. Then `w a ∈ s 𝔪_T` for every `w ∈ 𝔪_O`: otherwise `s = w a r` for some `r = r₁ / u`
with `u ∉ Q`, so `d u = w y r₁` and `Tr(u t) ∈ 𝔪_O` for every `t`, which forces `u ∈ Q`
(`mem_of_forall_trace_mul_mem`). -/
private theorem exists_mem_maximalIdeal_of_forall_trace_mul_mem {O S T : Type*} [CommRing O]
    [IsDomain O] [IsLocalRing O] [CommRing S] [Algebra O S] [Module.Free O S] [Module.Finite O S]
    [CharZero (O ⧸ IsLocalRing.maximalIdeal O)] (Q : Ideal S) [Q.IsMaximal] [CommRing T]
    [IsDomain T] [IsDiscreteValuationRing T] (f : S →+* T) (hf : Function.Injective f)
    (hsurj : ∀ t : T, ∃ r : S, ∃ u ∉ Q, f r = t * f u) {y : S} {d w : O} (hd : d ≠ 0)
    (hw : w ∈ IsLocalRing.maximalIdeal O) {N : ℕ} (hN : 0 < N)
    (htr : ∀ r : S, ∃ γ : O, (N : O) * Algebra.trace O S (y * r) = d * γ) {a s : T}
    (hrel : f y * s = f (algebraMap O S d) * a) :
    ∃ m ∈ IsLocalRing.maximalIdeal T, f (algebraMap O S w) * a = s * m := by
  classical
  by_contra H
  have hNO : (N : O) ∉ IsLocalRing.maximalIdeal O := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨r, hr⟩ : ∃ r : T, s = f (algebraMap O S w) * a * r := by
    rcases ValuationRing.dvd_total s (f (algebraMap O S w) * a) with ⟨m, hm⟩ | h
    · by_cases hm' : m ∈ IsLocalRing.maximalIdeal T
      · exact absurd ⟨m, hm', hm⟩ H
      · obtain ⟨v, hv⟩ := IsLocalRing.notMem_maximalIdeal.mp hm'
        refine ⟨↑v⁻¹, ?_⟩
        rw [hm, ← hv, mul_assoc, Units.mul_inv, mul_one]
    · exact h
  have ha : a ≠ 0 := by
    rintro rfl
    exact H ⟨0, zero_mem _, by simp⟩
  obtain ⟨r₁, u₁, hu₁, hr₁⟩ := hsurj r
  have h2 : f (algebraMap O S d) = f y * f (algebraMap O S w) * r :=
    mul_right_cancel₀ ha (by rw [← hrel, hr]; ring)
  have h3 : algebraMap O S d * u₁ = y * algebraMap O S w * r₁ := by
    apply hf
    rw [map_mul, map_mul, map_mul, h2, hr₁]
    ring
  apply hu₁
  apply mem_of_forall_trace_mul_mem (O := O) Q
  intro t
  obtain ⟨γ, hγ⟩ := htr (r₁ * t)
  have htd : ∀ (c : O) (z : S), Algebra.trace O S (algebraMap O S c * z) =
      c * Algebra.trace O S z := fun c z => by
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have h4 : d * ((N : O) * Algebra.trace O S (u₁ * t)) = d * (w * γ) := by
    have h5 : algebraMap O S d * (u₁ * t) = algebraMap O S w * (y * (r₁ * t)) := by
      rw [← mul_assoc, h3]
      ring
    calc d * ((N : O) * Algebra.trace O S (u₁ * t))
        = (N : O) * Algebra.trace O S (algebraMap O S d * (u₁ * t)) := by rw [htd]; ring
      _ = w * ((N : O) * Algebra.trace O S (y * (r₁ * t))) := by rw [h5, htd]; ring
      _ = d * (w * γ) := by rw [hγ]; ring
  have h7 : (N : O) * Algebra.trace O S (u₁ * t) ∈ IsLocalRing.maximalIdeal O :=
    mul_left_cancel₀ hd h4 ▸ Ideal.mul_mem_right _ _ hw
  exact (Ideal.IsPrime.mem_or_mem inferInstance h7).resolve_left hNO

/-- **The trace bound on a residue, through quotients.** Let `B → A` and `C → B` be ring maps, `p`
a prime of `A` with `A / p` a discrete valuation ring, lying over `q ⊆ C` with `C / q` local of
residue characteristic zero and `B / (p ∩ B)` finite free over it, and `Q` a maximal ideal of
`B / (p ∩ B)` at which `A / p` is the localization. If `y ∈ B` has `Tr_{B/C}(y c) ∈ d C` and
`Tr_{B/C}(y c) ≡ N Tr(ȳ c̄)` modulo `q` for every `c`, with `d ∉ q` and `N > 0`, and `y s = d a` in
`A`, then `w̄ ā ∈ s̄ 𝔪_{A/p}` for every `w` with `w̄ ∈ 𝔪_{C/q}`
(`exists_mem_maximalIdeal_of_forall_trace_mul_mem`). -/
private theorem exists_mem_maximalIdeal_of_trace_mem_quotient {C B A : Type*} [CommRing C]
    [CommRing B] [CommRing A] [Algebra C B] [Algebra B A] [Algebra C A] [IsScalarTower C B A]
    (q : Ideal C) [q.IsPrime] [IsLocalRing (C ⧸ q)]
    [CharZero ((C ⧸ q) ⧸ IsLocalRing.maximalIdeal (C ⧸ q))]
    (p : Ideal A) [p.IsPrime] [IsDiscreteValuationRing (A ⧸ p)]
    (hpq : (p.comap (algebraMap B A)).comap (algebraMap C B) = q)
    [letI := Ideal.Quotient.algebraQuotientOfLEComap hpq.ge;
      Module.Free (C ⧸ q) (B ⧸ p.comap (algebraMap B A))]
    [letI := Ideal.Quotient.algebraQuotientOfLEComap hpq.ge;
      Module.Finite (C ⧸ q) (B ⧸ p.comap (algebraMap B A))]
    (𝔐 : Ideal B) [𝔐.IsMaximal] (hp𝔐 : p.comap (algebraMap B A) ≤ 𝔐)
    (hsurj : ∀ α : A, ∃ β m : B, m ∉ 𝔐 ∧ α * algebraMap B A m = algebraMap B A β)
    {y : B} {d : C} (hd : d ∉ q) {w : C}
    (hw : Ideal.Quotient.mk q w ∈ IsLocalRing.maximalIdeal (C ⧸ q))
    {N : ℕ} (hN : 0 < N)
    (key : letI := Ideal.Quotient.algebraQuotientOfLEComap hpq.ge;
      ∀ c : B, Ideal.Quotient.mk q (Algebra.trace C B (y * c)) =
        N • Algebra.trace (C ⧸ q) (B ⧸ p.comap (algebraMap B A))
          (Ideal.Quotient.mk (p.comap (algebraMap B A)) (y * c)))
    (htrC : ∀ c : B, ∃ γ : C, Algebra.trace C B (y * c) = d * γ) {s a : A}
    (hrel : algebraMap B A y * s = algebraMap C A d * a) :
    ∃ m ∈ IsLocalRing.maximalIdeal (A ⧸ p),
      Ideal.Quotient.mk p (algebraMap C A w) * Ideal.Quotient.mk p a =
        Ideal.Quotient.mk p s * m := by
  classical
  set pB := p.comap (algebraMap B A) with hpBdef
  set Q := 𝔐.map (Ideal.Quotient.mk pB) with hQdef
  haveI : Q.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])
  letI : Algebra (C ⧸ q) (B ⧸ pB) := Ideal.Quotient.algebraQuotientOfLEComap hpq.ge
  let φ : B ⧸ pB →+* A ⧸ p := Ideal.quotientMap p (algebraMap B A) le_rfl
  have hφ : ∀ z : B, φ (Ideal.Quotient.mk pB z) = Ideal.Quotient.mk p (algebraMap B A z) :=
    fun _ => Ideal.quotientMap_mk
  have hmk : ∀ c : C, algebraMap (C ⧸ q) (B ⧸ pB) (Ideal.Quotient.mk q c) =
      Ideal.Quotient.mk pB (algebraMap C B c) := fun c =>
    (Ideal.Quotient.mk_algebraMap _ _ c).symm
  have hCBA : ∀ c : C, algebraMap B A (algebraMap C B c) = algebraMap C A c :=
    fun c => (IsScalarTower.algebraMap_apply C B A c).symm
  have hdq : Ideal.Quotient.mk q d ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hsurj' : ∀ t : A ⧸ p, ∃ r : B ⧸ pB, ∃ u ∉ Q, φ r = t * φ u := by
    intro t
    obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨β, m, hm, hαm⟩ := hsurj α
    refine ⟨Ideal.Quotient.mk pB β, Ideal.Quotient.mk pB m, fun h => hm ?_,
      by rw [hφ, hφ, ← map_mul, hαm]⟩
    have h1 : m ∈ Q.comap (Ideal.Quotient.mk pB) := h
    rwa [hQdef, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hp𝔐] at h1
  have htr : ∀ r : B ⧸ pB, ∃ γ : C ⧸ q,
      (N : C ⧸ q) * Algebra.trace (C ⧸ q) (B ⧸ pB) (Ideal.Quotient.mk pB y * r) =
        Ideal.Quotient.mk q d * γ := by
    intro r
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨γ, hγ⟩ := htrC c
    refine ⟨Ideal.Quotient.mk q γ, ?_⟩
    have hk := key c
    rw [hγ, map_mul (Ideal.Quotient.mk q), map_mul (Ideal.Quotient.mk pB), nsmul_eq_mul] at hk
    exact hk.symm
  have hrel' : φ (Ideal.Quotient.mk pB y) * Ideal.Quotient.mk p s =
      φ (algebraMap (C ⧸ q) (B ⧸ pB) (Ideal.Quotient.mk q d)) * Ideal.Quotient.mk p a := by
    rw [hmk, hφ, hφ, hCBA, ← map_mul, ← map_mul, hrel]
  obtain ⟨m, hm, hmeq⟩ := exists_mem_maximalIdeal_of_forall_trace_mul_mem (O := C ⧸ q) Q φ
    Ideal.quotientMap_injective hsurj' hdq hw hN htr hrel'
  refine ⟨m, hm, ?_⟩
  rwa [hmk, hφ, hCBA] at hmeq

/-- **A prime over a principal prime is minimal over each of its nonzero elements of the base.**
Let `B` be integral over a factorial domain `C` and `E` a prime of `B` with `E ∩ C = (π)`, `π`
prime. Then `E` is a minimal prime of `δ B` for every nonzero `δ ∈ C` with `δ ∈ E`: a prime
`P ⊆ E` containing `δ` has `P ∩ C` a nonzero prime inside `(π)`, hence `P ∩ C = (π)`, and
incomparability gives `P = E`. -/
private theorem mem_minimalPrimes_of_comap_eq_span {C B : Type*} [CommRing C] [IsDomain C]
    [UniqueFactorizationMonoid C] [CommRing B] [Algebra C B] [Algebra.IsIntegral C B]
    (E : Ideal B) [E.IsPrime] {π δ : C} (hπ : Prime π)
    (hE : E.comap (algebraMap C B) = Ideal.span {π}) (hδ : δ ≠ 0) (hδE : algebraMap C B δ ∈ E) :
    E ∈ (Ideal.span {algebraMap C B δ}).minimalPrimes := by
  refine ⟨⟨inferInstance, by rwa [Ideal.span_le, Set.singleton_subset_iff]⟩,
    fun P ⟨hP, hδP⟩ hPE => ?_⟩
  haveI := hP
  have hPC : P.comap (algebraMap C B) = Ideal.span {π} := by
    refine le_antisymm (hE ▸ Ideal.comap_mono hPE) ?_
    have hne : P.comap (algebraMap C B) ≠ ⊥ := fun h => hδ (by
      have : δ ∈ P.comap (algebraMap C B) := hδP (Ideal.mem_span_singleton_self _)
      rwa [h, Ideal.mem_bot] at this)
    obtain ⟨π', hπ'P, hπ'⟩ :=
      Ideal.IsPrime.exists_mem_prime_of_ne_bot (Ideal.comap_isPrime _ _) hne
    have hπ'E : π' ∈ Ideal.span {π} := hE ▸ Ideal.comap_mono hPE hπ'P
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hπ'E
    have hcu : IsUnit c :=
      (hπ'.irreducible.isUnit_or_isUnit hc.symm).resolve_right hπ.not_isUnit
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      show π = ↑hcu.unit⁻¹ * π' by rw [← hc, ← mul_assoc, IsUnit.val_inv_mul, one_mul]]
    exact Ideal.mul_mem_left _ _ hπ'P
  by_contra hne
  have hlt : P < E := lt_of_le_of_ne hPE fun h => hne (h ▸ le_rfl)
  have := Ideal.IsIntegral.comap_lt_comap (R := C) hlt
  rw [Ideal.under_def, Ideal.under_def, hPC, hE] at this
  exact lt_irrefl _ this

open nonZeroDivisors in
/-- **Clearing the poles away from one prime.** Let `B` be a Noetherian ring integral over a
factorial domain `C`, `K` its localization at `C ∖ 0`, `𝔐` a prime of `B` and `x ∈ K`. Some
`b ∉ 𝔐` makes `b x` regular at every prime `E ⊄ 𝔐` of `B` lying over a principal prime of `C`:
write `x = y / δ`; such an `E` containing `δ` is a minimal prime of `δ B`
(`mem_minimalPrimes_of_comap_eq_span`), and a power of `b c` lies in `δ B` for `b` in the minimal
primes not inside `𝔐` and `c` in the others but in none of the former. -/
private theorem exists_notMem_forall_not_le {C B K : Type*} [CommRing C] [IsDomain C]
    [UniqueFactorizationMonoid C] [CommRing B] [IsNoetherianRing B] [Algebra C B]
    [Algebra.IsIntegral C B] [CommRing K] [Algebra B K]
    [IsLocalization (Algebra.algebraMapSubmonoid B C⁰) K] (𝔐 : Ideal B) [𝔐.IsPrime] (x : K) :
    ∃ b ∉ 𝔐, ∀ (E : Ideal B) [E.IsPrime], ¬ E ≤ 𝔐 → ∀ π : C, Prime π →
      E.comap (algebraMap C B) = Ideal.span {π} →
        ∃ s ∉ E, ∃ a : B, x * algebraMap B K b * algebraMap B K s = algebraMap B K a := by
  classical
  obtain ⟨⟨y, ⟨_, δ, hδ, rfl⟩⟩, hxy⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B C⁰) x
  simp only at hxy
  have hδ0 : δ ≠ 0 := nonZeroDivisors.ne_zero hδ
  set I := Ideal.span {algebraMap C B δ} with hIdef
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
  have h₁ : {P | P ∈ I.minimalPrimes ∧ ¬ P ≤ 𝔐}.Finite := hfin.subset fun P hP => hP.1
  have h₂ : {P | P ∈ I.minimalPrimes ∧ P ≤ 𝔐}.Finite := hfin.subset fun P hP => hP.1
  set t₁ := h₁.toFinset
  set t₂ := h₂.toFinset
  have hprime : ∀ P ∈ I.minimalPrimes, P.IsPrime := fun P hP => hP.1.1
  -- `b₀` in every minimal prime not inside `𝔐`, but not in `𝔐`
  have hnle : ¬ t₁.inf id ≤ 𝔐 := by
    intro h
    obtain ⟨P, hP, hPle⟩ := (Ideal.IsPrime.inf_le' inferInstance).mp h
    rw [Set.Finite.mem_toFinset] at hP
    exact hP.2 hPle
  obtain ⟨b₀, hb₀, hb₀𝔐⟩ := SetLike.not_le_iff_exists.mp hnle
  -- `c` in every minimal prime inside `𝔐`, and in none of the others
  have hc : ¬ ((t₂.inf id : Ideal B) : Set B) ⊆
      ⋃ P ∈ (t₁ : Set (Ideal B)), ((id P : Ideal B) : Set B) := by
    rw [Ideal.subset_union_prime (f := id) ⊥ ⊥ fun P (hP : P ∈ t₁) _ _ => by
      rw [Set.Finite.mem_toFinset] at hP; exact hprime P hP.1]
    rintro ⟨P, hP, hle⟩
    rw [Set.Finite.mem_toFinset] at hP
    haveI : (id P).IsPrime := hprime P hP.1
    obtain ⟨P', hP', hP'le⟩ := (Ideal.IsPrime.inf_le' inferInstance).mp hle
    rw [Set.Finite.mem_toFinset] at hP'
    exact hP.2 ((hP.1.2 hP'.1.1 hP'le).trans hP'.2)
  obtain ⟨c, hc₂, hc₁⟩ := Set.not_subset.mp hc
  simp only [Set.mem_iUnion, not_exists] at hc₁
  have hcE : ∀ P ∈ t₁, c ∉ P := fun P hP h => hc₁ P hP h
  -- `b₀ c` lies in the radical of `δ B`
  have hrad : b₀ * c ∈ I.radical := by
    rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro P hP
    by_cases hP𝔐 : P ≤ 𝔐
    · have : P ∈ t₂ := by rw [Set.Finite.mem_toFinset]; exact ⟨hP, hP𝔐⟩
      exact Ideal.mul_mem_left _ _ (Finset.inf_le (f := id) this hc₂)
    · have : P ∈ t₁ := by rw [Set.Finite.mem_toFinset]; exact ⟨hP, hP𝔐⟩
      exact Ideal.mul_mem_right _ _ (Finset.inf_le (f := id) this hb₀)
  obtain ⟨n, hn⟩ := hrad
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hn
  refine ⟨b₀ ^ n, fun h => hb₀𝔐 (Ideal.IsPrime.mem_of_pow_mem inferInstance n h), ?_⟩
  intro E _ hE𝔐 π hπ hEπ
  by_cases hδE : algebraMap C B δ ∈ E
  · have hEmin := mem_minimalPrimes_of_comap_eq_span E hπ hEπ hδ0 hδE
    have hEt : E ∈ t₁ := by rw [Set.Finite.mem_toFinset]; exact ⟨hEmin, hE𝔐⟩
    refine ⟨c ^ n, fun h => hcE E hEt (Ideal.IsPrime.mem_of_pow_mem inferInstance n h), r * y, ?_⟩
    rw [mul_assoc, ← map_mul, ← mul_pow, ← hr, map_mul, map_mul, ← hxy]
    ring
  · exact ⟨algebraMap C B δ, hδE, b₀ ^ n * y, by rw [map_mul, ← hxy]; ring⟩

/-- **A prime of a normal local ring over a principal prime of the base is of height one.** Let
`A` be a Noetherian normal domain, the localization of a ring `B` integral over `C` at a prime,
and `E` a prime of `A` with `E ∩ C = (π)`, `π ≠ 0` in `A`. Then `A_E` is a discrete valuation ring:
`E` is minimal over `π A` (incomparability), so it has height one by Krull's principal ideal
theorem. -/
private theorem isDiscreteValuationRing_localization_of_comap_eq {C B A : Type*} [CommRing C]
    [CommRing B] [Algebra C B] [Algebra.IsIntegral C B] [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra B A] (𝔐 : Ideal B) [𝔐.IsPrime]
    [IsLocalization.AtPrime A 𝔐] (E : Ideal A) [E.IsPrime] {π : C}
    (hπ : algebraMap B A (algebraMap C B π) ≠ 0)
    (hE : (E.comap (algebraMap B A)).comap (algebraMap C B) = Ideal.span {π}) :
    IsDiscreteValuationRing (Localization.AtPrime E) := by
  apply MMP.Chow.isDiscreteValuationRing_localization_atPrime_of_height_eq_one
  set z := algebraMap B A (algebraMap C B π) with hz
  have hzE : z ∈ E :=
    (hE ▸ Ideal.mem_span_singleton_self π : π ∈ (E.comap (algebraMap B A)).comap (algebraMap C B))
  have hmin : E ∈ (Ideal.span {z}).minimalPrimes := by
    refine ⟨⟨inferInstance, by rwa [Ideal.span_le, Set.singleton_subset_iff]⟩,
      fun P ⟨hP, hzP⟩ hPE => ?_⟩
    haveI := hP
    have hPB : (P.comap (algebraMap B A)).comap (algebraMap C B) = Ideal.span {π} := by
      refine le_antisymm (hE ▸ Ideal.comap_mono (Ideal.comap_mono hPE)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hzP (Ideal.mem_span_singleton_self _)
    have hcomap : P.comap (algebraMap B A) = E.comap (algebraMap B A) := by
      by_contra hne
      have hlt : P.comap (algebraMap B A) < E.comap (algebraMap B A) :=
        lt_of_le_of_ne (Ideal.comap_mono hPE) hne
      have := Ideal.IsIntegral.comap_lt_comap (R := C) hlt
      rw [Ideal.under_def, Ideal.under_def, hPB, hE] at this
      exact lt_irrefl _ this
    rw [← IsLocalization.map_under 𝔐.primeCompl A P, ← IsLocalization.map_under 𝔐.primeCompl A E,
      Ideal.under, Ideal.under, hcomap]
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ E hmin) ?_
  rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  rintro rfl
  exact hπ hzE

/-- **Clearing the denominators of a local relation.** Let `A` be the localization of `B` at a
prime and `P` a prime of `A`. A relation `x s = a` with `s, a ∈ A` becomes `x s' = a'` with
`s', a' ∈ B`, where `s' ∉ P ∩ B` when `s ∉ P` and `a' ∈ P ∩ B` when `a ∈ P`. -/
private theorem exists_mul_eq_of_isLocalization {B A K : Type*} [CommRing B] [CommRing A]
    [Algebra B A] (𝔐 : Ideal B) [𝔐.IsPrime] [IsLocalization.AtPrime A 𝔐] [CommRing K]
    [Algebra A K] [Algebra B K] [IsScalarTower B A K] (P : Ideal A) [P.IsPrime] {x : K} {s a : A}
    (h : x * algebraMap A K s = algebraMap A K a) :
    ∃ s' a' : B, (s ∉ P → s' ∉ P.comap (algebraMap B A)) ∧
      (a ∈ P → a' ∈ P.comap (algebraMap B A)) ∧ x * algebraMap B K s' = algebraMap B K a' := by
  obtain ⟨⟨s₁, m⟩, hs⟩ := IsLocalization.surj 𝔐.primeCompl s
  obtain ⟨⟨a₁, m'⟩, ha⟩ := IsLocalization.surj 𝔐.primeCompl a
  simp only at hs ha
  have hm : ∀ m : 𝔐.primeCompl, algebraMap B A m ∉ P := fun m h =>
    (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem P h
      (IsLocalization.map_units A m))
  refine ⟨s₁ * m', a₁ * m, fun hsP h => ?_, fun haP => ?_, ?_⟩
  · rw [Ideal.mem_comap, map_mul, ← hs] at h
    rcases (Ideal.IsPrime.mem_or_mem inferInstance h) with h | h
    · rcases (Ideal.IsPrime.mem_or_mem inferInstance h) with h | h
      · exact hsP h
      · exact hm m h
    · exact hm m' h
  · rw [Ideal.mem_comap, map_mul, ← ha]
    exact P.mul_mem_right _ (P.mul_mem_right _ haP)
  · rw [IsScalarTower.algebraMap_apply B A K (s₁ * m'),
      IsScalarTower.algebraMap_apply B A K (a₁ * m)]
    simp only [map_mul]
    rw [← hs, ← ha]
    simp only [map_mul]
    linear_combination
      (algebraMap A K (algebraMap B A m) * algebraMap A K (algebraMap B A m')) * h

/-- **The codifferent bound at a prime of `B` inside `𝔐`.** Let `A` be the localization at `𝔐`
of a ring `B` integral over a localization `C` of `D`, and `E ≤ 𝔐` a prime of `B` over a principal
prime `(π)` of `C`, other than `p ∩ B`. A codifferent bound `F π' ∈ E' A_{E'}` at every height-one
prime `E' ≠ p` of `A` gives `F π ∈ E B_E`. -/
private theorem exists_mul_eq_mem_of_le_of_isLocalization {D R C B A K : Type*}
    [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] [CommRing R] [IsDomain R]
    [Algebra D R] [Algebra.IsIntegral D R] [FaithfulSMul D R] [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra D A] [Algebra R A]
    [IsScalarTower D R A] (𝔮 : Ideal R) [𝔮.IsPrime] [IsLocalization.AtPrime A 𝔮]
    [CommRing C] [IsDomain C] [Algebra D C] (M : Submonoid D) [IsLocalization M C] [CommRing B]
    [Algebra C B] [Algebra.IsIntegral C B] [Algebra B A] [Algebra C A] [IsScalarTower C B A]
    (𝔐 : Ideal B) [𝔐.IsPrime] [IsLocalization.AtPrime A 𝔐] [CommRing K] [Algebra A K]
    [Algebra B K] [Algebra C K] [Algebra D K] [IsScalarTower B A K] [IsScalarTower C A K]
    [IsScalarTower D C K] (hCA : Function.Injective (algebraMap C A))
    (hcomap : ∀ E : Ideal A, ((E.comap (algebraMap B A)).comap (algebraMap C B)).comap
      (algebraMap D C) = E.comap (algebraMap D A))
    (p : Ideal A) {F : K}
    (hFE : ∀ (E : Ideal A) [E.IsPrime], IsDiscreteValuationRing (Localization.AtPrime E) → E ≠ p →
      ∀ π : D, π ≠ 0 → E.comap (algebraMap D A) = Ideal.span {π} →
        ∃ s ∉ E, ∃ a ∈ E, F * algebraMap D K π * algebraMap A K s = algebraMap A K a)
    (E : Ideal B) [E.IsPrime] (hE𝔐 : E ≤ 𝔐) {π : C} (hπ : Prime π)
    (hEπ : E.comap (algebraMap C B) = Ideal.span {π}) (hEp : E ≠ p.comap (algebraMap B A)) :
    ∃ s ∉ E, ∃ a ∈ E, F * algebraMap C K π * algebraMap B K s = algebraMap B K a := by
  have hdisj : Disjoint (𝔐.primeCompl : Set B) (E : Set B) := by
    rw [Set.disjoint_left]; exact fun x hx h => hx (hE𝔐 h)
  haveI hEA : (E.map (algebraMap B A)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔐.primeCompl A E inferInstance hdisj
  have hEAc : (E.map (algebraMap B A)).comap (algebraMap B A) = E :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔐.primeCompl A inferInstance hdisj
  have hπA : algebraMap B A (algebraMap C B π) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply]; exact (map_ne_zero_iff _ hCA).mpr hπ.ne_zero
  have hdvr := isDiscreteValuationRing_localization_of_comap_eq (C := C) 𝔐
    (E.map (algebraMap B A)) hπA (by rw [hEAc, hEπ])
  have hne : E.map (algebraMap B A) ≠ p := fun h => hEp (by rw [← hEAc, h])
  obtain ⟨πD, hπD0, hπD, -⟩ := exists_comap_eq_span_singleton (D := D) 𝔮 _ hdvr
  obtain ⟨sA, hsA, aA, haA, hFA⟩ := hFE _ hdvr hne πD hπD0 hπD
  have hcD : (E.comap (algebraMap C B)).comap (algebraMap D C) = Ideal.span {πD} := by
    rw [← hπD, ← hcomap, hEAc]
  have hspan : Ideal.span {π} = Ideal.span {algebraMap D C πD} := by
    rw [← hEπ, ← IsLocalization.map_under M C (E.comap (algebraMap C B)), Ideal.under, hcD,
      Ideal.map_span, Set.image_singleton]
  obtain ⟨v, hv'⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hrel : F * algebraMap C K π * algebraMap A K (algebraMap C A ↑v * sA) =
      algebraMap A K aA := by
    rw [← hFA, map_mul, ← IsScalarTower.algebraMap_apply C A K,
      IsScalarTower.algebraMap_apply D C K πD, ← hv', map_mul]
    ring
  have hsA' : algebraMap C A ↑v * sA ∉ E.map (algebraMap B A) := fun h =>
    hsA ((Ideal.IsPrime.mem_or_mem inferInstance h).resolve_left fun h' =>
      (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.eq_top_of_isUnit_mem _ h' (v.isUnit.map _)))
  obtain ⟨s', a', hs', ha', h'⟩ :=
    exists_mul_eq_of_isLocalization 𝔐 (E.map (algebraMap B A)) hrel
  rw [hEAc] at hs' ha'
  exact ⟨s', hs' hsA', a', ha' haA, h'⟩

open nonZeroDivisors in
/-- **The ring-level residue regularity.** In the situation of `exists_residue_lift_ring`, let
`F ∈ K` satisfy the codifferent bounds of a section of `ω(P)`: `F π ∈ E A_E` at every prime
`E ≠ p` of `A` with `A_E` a discrete valuation ring and `E ∩ D = (π)`, and `F x₀ = a / s` with
`s ∉ p`. Then `w̄ ā ∈ s̄ 𝔪_{A/p}`: the residue `ā / s̄` has order at least `1 - e_Q` at the closed
point of `A / p`, where `w̄` has order `e_Q`. -/
private theorem exists_mem_maximalIdeal_of_residue_ring (k : Type u) [Field k] [CharZero k]
    {D R A K : Type u} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]
    [IsNoetherianRing D] [Algebra k D] [CommRing R] [IsDomain R] [Algebra D R]
    [Module.Finite D R] [FaithfulSMul D R] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Algebra D A] [Algebra R A] [IsScalarTower D R A]
    (𝔮 : Ideal R) [𝔮.IsPrime] [IsLocalization.AtPrime A 𝔮] [Field K] [Algebra A K]
    [IsFractionRing A K] [Algebra D K] [IsScalarTower D A K] [Algebra R K] [IsScalarTower R A K]
    [IsFractionRing R K]
    (p : Ideal A) [p.IsPrime]
    [IsDiscreteValuationRing (A ⧸ p)] {x₀ w : D} (hx₀ : x₀ ≠ 0)
    (hx₀p : (Ideal.span {x₀}).IsPrime) (hpX : p.comap (algebraMap D A) = Ideal.span {x₀})
    (hw : w ∉ Ideal.span {x₀})
    (hv : (IsLocalRing.maximalIdeal A).comap (algebraMap D A) = Ideal.span {x₀, w})
    {F : K}
    (hFE : ∀ (E : Ideal A) [E.IsPrime], IsDiscreteValuationRing (Localization.AtPrime E) → E ≠ p →
      ∀ π : D, π ≠ 0 → E.comap (algebraMap D A) = Ideal.span {π} →
        ∃ s ∉ E, ∃ a ∈ E, F * algebraMap D K π * algebraMap A K s = algebraMap A K a)
    {s a : A} (hs : s ∉ p) (hFP : F * algebraMap D K x₀ * algebraMap A K s = algebraMap A K a) :
    ∃ m ∈ IsLocalRing.maximalIdeal (A ⧸ p),
      Ideal.Quotient.mk p (algebraMap D A w) * Ideal.Quotient.mk p a =
        Ideal.Quotient.mk p s * m := by
  classical
  -- injectivity
  have hRA : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A 𝔮.primeCompl_le_nonZeroDivisors
  have hDR : Function.Injective (algebraMap D R) := FaithfulSMul.algebraMap_injective D R
  have hDA : Function.Injective (algebraMap D A) := by
    rw [IsScalarTower.algebraMap_eq D R A]; exact hRA.comp hDR
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  -- the regular base `C = D_v`
  haveI : (Ideal.span {x₀, w} : Ideal D).IsPrime := hv ▸ Ideal.comap_isPrime _ _
  let C := Localization.AtPrime (Ideal.span {x₀, w} : Ideal D)
  have hunits : ∀ s : (Ideal.span {x₀, w} : Ideal D).primeCompl, IsUnit (algebraMap D A s) :=
    fun s => by
      by_contra h
      have h1 : (s : D) ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap D A) :=
        (IsLocalRing.mem_maximalIdeal _).mpr h
      rw [hv] at h1
      exact s.2 h1
  letI : Algebra C A := (IsLocalization.lift hunits).toAlgebra
  haveI : IsScalarTower D C A :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunits x).symm
  letI : Algebra C K := ((algebraMap A K).comp (algebraMap C A)).toAlgebra
  haveI : IsScalarTower C A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower D C K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply D A K, IsScalarTower.algebraMap_apply D C A]; rfl
  haveI : IsNoetherianRing C :=
    IsLocalization.isNoetherianRing (Ideal.span {x₀, w} : Ideal D).primeCompl C inferInstance
  haveI : IsIntegrallyClosed C := isIntegrallyClosed_of_isLocalization C
    (Ideal.span {x₀, w} : Ideal D).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)
  have hCA : Function.Injective (algebraMap C A) :=
    (IsLocalization.lift_injective_iff hunits).mpr fun x y =>
      (IsLocalization.injective C
        (Ideal.span {x₀, w} : Ideal D).primeCompl_le_nonZeroDivisors).eq_iff.trans
        hDA.eq_iff.symm
  obtain ⟨hg0, hgm, hgprime, hwg, hmaxC⟩ := localization_span_pair_facts hx₀ hx₀p hw C
  haveI := hgprime
  obtain ⟨_, hmax, hdvr, hwirr⟩ := isDiscreteValuationRing_quotient_span hmaxC hwg
  haveI := hdvr
  -- the fraction field `Fr` of `D` and of `C`
  let Fr := FractionRing D
  have hDK : Function.Injective (algebraMap D K) := by
    rw [IsScalarTower.algebraMap_eq D A K]; exact hAK.comp hDA
  haveI : FaithfulSMul D K := (faithfulSMul_iff_algebraMap_injective D K).mpr hDK
  letI : Algebra Fr K := FractionRing.liftAlgebra D K
  haveI : IsScalarTower D Fr K := FractionRing.isScalarTower_liftAlgebra D K
  have hunitsF : ∀ s : (Ideal.span {x₀, w} : Ideal D).primeCompl, IsUnit (algebraMap D Fr s) :=
    fun s => IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective D Fr)).mpr
      (nonZeroDivisors.ne_zero ((Ideal.primeCompl_le_nonZeroDivisors _) s.2)))
  letI : Algebra C Fr := (IsLocalization.lift hunitsF).toAlgebra
  haveI : IsScalarTower D C Fr :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunitsF x).symm
  haveI : IsFractionRing C Fr := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Ideal.span {x₀, w} : Ideal D).primeCompl C Fr
  have hCFK : (algebraMap Fr K).comp (algebraMap C Fr) = algebraMap C K :=
    IsLocalization.ringHom_ext (Ideal.span {x₀, w} : Ideal D).primeCompl (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply])
  haveI : IsScalarTower C Fr K :=
    IsScalarTower.of_algebraMap_eq fun c => (RingHom.congr_fun hCFK c).symm
  haveI : IsScalarTower D R K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply R A K, ← IsScalarTower.algebraMap_apply D R A,
      ← IsScalarTower.algebraMap_apply D A K]
  haveI : Algebra.IsAlgebraic D R := Algebra.IsAlgebraic.of_finite D R
  haveI : Module.Finite Fr K := Module.Finite.of_isLocalization D R (Rₚ := Fr) (Sₚ := K) D⁰
  haveI : CharZero Fr :=
    charZero_of_injective_ringHom ((algebraMap D Fr).comp (algebraMap k D)).injective
  haveI : Algebra.IsAlgebraic Fr K := Algebra.IsAlgebraic.of_finite Fr K
  haveI : Algebra.IsSeparable Fr K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- the integral closure `B` of `C` in `A`
  let B := integralClosure C A
  have hBA : Function.Injective (algebraMap B A) := Subtype.val_injective
  have hBK : Function.Injective (algebraMap B K) := hAK.comp hBA
  haveI : IsIntegralClosure B C K := by
    refine ⟨hBK, fun {x} => ⟨fun hx => ?_, ?_⟩⟩
    · obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := A))
      exact ⟨⟨a, (isIntegral_algHom_iff (IsScalarTower.toAlgHom C A K) hAK).mp hx⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact b.2.map (IsScalarTower.toAlgHom C A K)
  haveI : Module.Finite C B := IsIntegralClosure.finite C Fr K B
  haveI : IsFractionRing B K := IsIntegralClosure.isFractionRing_of_finite_extension C Fr K B
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B C⁰) K :=
    IsIntegralClosure.isLocalization C Fr K B
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing C B
  haveI : Algebra.IsIntegral C B := Algebra.IsIntegral.of_finite C B
  haveI : IsIntegrallyClosed B := (isIntegrallyClosed_iff K).mpr fun {x} hx =>
    IsIntegralClosure.isIntegral_iff.mp (isIntegral_trans (R := C) x hx)
  haveI : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective C B).mpr fun x y h => hCA (by
    rw [IsScalarTower.algebraMap_apply C B A, h, ← IsScalarTower.algebraMap_apply])
  -- `A` is the localization of `B` at `𝔐 = 𝔪_A ∩ B`
  set 𝔐 := (IsLocalRing.maximalIdeal A).comap (algebraMap B A) with h𝔐def
  have hRB : ∀ r : R, ∃ b : B, algebraMap B A b = algebraMap R A r := fun r =>
    ⟨⟨algebraMap R A r, ((Algebra.IsIntegral.isIntegral (R := D) r).map
      (IsScalarTower.toAlgHom D R A)).tower_top⟩, rfl⟩
  haveI : IsLocalization.AtPrime A 𝔐 := isLocalization_atPrime_comap_maximalIdeal 𝔮 hBA hRB
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing 𝔐.primeCompl A inferInstance
  -- the prime `p_B` of `B` below `p`, over `(g)`
  set pB := p.comap (algebraMap B A) with hpBdef
  have hpCA : p.comap (algebraMap C A) = Ideal.span {algebraMap D C x₀} := by
    rw [← IsLocalization.map_under (Ideal.span {x₀, w} : Ideal D).primeCompl C
      (p.comap (algebraMap C A)), Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      hpX, Ideal.map_span, Set.image_singleton]
  have hpB : pB.comap (algebraMap C B) = Ideal.span {algebraMap D C x₀} := by
    rw [hpBdef, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hpCA]
  -- `𝔐` is maximal
  have hmCA : (IsLocalRing.maximalIdeal A).comap (algebraMap C A) = IsLocalRing.maximalIdeal C := by
    rw [← IsLocalization.map_under (Ideal.span {x₀, w} : Ideal D).primeCompl C
      ((IsLocalRing.maximalIdeal A).comap (algebraMap C A)), Ideal.under, Ideal.comap_comap,
      ← IsScalarTower.algebraMap_eq, hv, Localization.AtPrime.map_eq_maximalIdeal]
  haveI h𝔐max : 𝔐.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := C)
    rw [Ideal.under_def, h𝔐def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hmCA]
    exact IsLocalRing.maximalIdeal.isMaximal C
  have hpB𝔐 : pB ≤ 𝔐 :=
    Ideal.comap_mono (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  have hCBK : ∀ c : C, algebraMap B K (algebraMap C B c) = algebraMap C K c :=
    fun c => (IsScalarTower.algebraMap_apply C B K c).symm
  have hDCK : ∀ x : D, algebraMap C K (algebraMap D C x) = algebraMap D K x :=
    fun x => (IsScalarTower.algebraMap_apply D C K x).symm
  have hBAK : ∀ x : B, algebraMap A K (algebraMap B A x) = algebraMap B K x := fun _ => rfl
  have hcomapEB : ∀ E : Ideal A, ((E.comap (algebraMap B A)).comap (algebraMap C B)).comap
      (algebraMap D C) = E.comap (algebraMap D A) := fun E => by
    ext x
    simp only [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
  -- the residue algebra `B / p_B` over the discrete valuation ring `C / (g)`
  have hcz : ∀ (R' : Type u) [CommRing R'] [Nontrivial R'] [Algebra C R'], CharZero R' :=
    fun R' _ _ _ =>
      charZero_of_injective_ringHom ((algebraMap C R').comp (algebraMap k C)).injective
  haveI : Module.Free C B := free_of_isDiscreteValuationRing_quotient hg0 hgm hgprime hwg hwirr
  set g := algebraMap D C x₀ with hgdef
  set q := Ideal.span {g} with hqdef
  letI : Algebra (C ⧸ q) (B ⧸ pB) := Ideal.Quotient.algebraQuotientOfLEComap hpB.ge
  haveI : IsScalarTower C (C ⧸ q) (B ⧸ pB) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (C ⧸ q) (B ⧸ pB) := Module.Finite.of_restrictScalars_finite C _ _
  haveI : FaithfulSMul (C ⧸ q) (B ⧸ pB) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (Ideal.quotientMap_injective' hpB.le)
  haveI : Module.Free (C ⧸ q) (B ⧸ pB) := free_of_isDiscreteValuationRing
  haveI : CharZero (Localization.AtPrime q ⧸ q.map (algebraMap C (Localization.AtPrime q))) := by
    haveI : Nontrivial (Localization.AtPrime q ⧸ q.map (algebraMap C (Localization.AtPrime q))) :=
      Ideal.Quotient.nontrivial_iff.mpr (by
        rw [Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.IsMaximal.ne_top inferInstance)
    exact hcz _
  haveI : CharZero ((C ⧸ q) ⧸ IsLocalRing.maximalIdeal (C ⧸ q)) := by
    haveI : Nontrivial ((C ⧸ q) ⧸ IsLocalRing.maximalIdeal (C ⧸ q)) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top inferInstance)
    exact hcz _
  have hgP : Prime g := (Ideal.span_singleton_prime hg0).mp hgprime
  -- clearing the poles of `F` at the primes of `B` away from `𝔐`
  obtain ⟨b, hb𝔐, hbE⟩ := exists_notMem_forall_not_le (C := C) (K := K) 𝔐 F
  -- the codifferent bounds at every prime of `B` over a principal prime, except `p_B`
  have hU : ∀ (E : Ideal B) [E.IsPrime] (π : C), Prime π →
      E.comap (algebraMap C B) = Ideal.span {π} → E ≠ pB →
        ∃ s ∉ E, ∃ a ∈ E, F * algebraMap B K b * algebraMap C K π * algebraMap B K s =
          algebraMap B K a := by
    intro E _ π hπ hEπ hEp
    have hπE : algebraMap C B π ∈ E :=
      (hEπ ▸ Ideal.mem_span_singleton_self π : π ∈ E.comap (algebraMap C B))
    by_cases hE𝔐 : E ≤ 𝔐
    · obtain ⟨s', hs', a', ha', h'⟩ := exists_mul_eq_mem_of_le_of_isLocalization 𝔮
        (Ideal.span {x₀, w} : Ideal D).primeCompl 𝔐 hCA hcomapEB p hFE E hE𝔐 hπ hEπ hEp
      refine ⟨s', hs', b * a', E.mul_mem_left _ ha', ?_⟩
      rw [map_mul, ← h']
      ring
    · obtain ⟨s', hs', a', h'⟩ := hbE E hE𝔐 π hπ hEπ
      refine ⟨s', hs', algebraMap C B π * a', E.mul_mem_right _ hπE, ?_⟩
      rw [map_mul, hCBK, ← h']
      ring
  -- the bound at `p_B`
  have hPB : ∃ s' ∉ pB, ∃ a' : B,
      F * algebraMap B K b * algebraMap C K g * algebraMap B K s' = algebraMap B K a' := by
    obtain ⟨s', a', hs', -, h'⟩ := exists_mul_eq_of_isLocalization 𝔐 p hFP
    refine ⟨s', hs' hs, b * a', ?_⟩
    rw [map_mul, ← h', hgdef, hDCK]
    ring
  -- the element `X = b F x₀` and a multiple `y₁ = d X ∈ B`, `d ∉ (g)`
  have hXq : ∀ E : Ideal B, E.IsPrime → E.comap (algebraMap C B) = q →
      ∃ s' ∉ E, ∃ a' : B, (E ≠ pB → a' ∈ E) ∧
        F * algebraMap B K b * algebraMap C K g * algebraMap B K s' = algebraMap B K a' := by
    intro E hE hEq
    by_cases hEp : E = pB
    · obtain ⟨s', hs', a', h'⟩ := hPB
      exact ⟨s', hEp ▸ hs', a', fun h => absurd hEp h, h'⟩
    · obtain ⟨s', hs', a', ha', h'⟩ := hU E g hgP hEq hEp
      exact ⟨s', hs', a', fun _ => ha', h'⟩
  obtain ⟨d, hdq, y₁, hy₁⟩ := exists_mul_mem_of_forall_liesOver q
    (F * algebraMap B K b * algebraMap C K g) fun E hE hEq => by
      obtain ⟨s', hs', a', -, h'⟩ := hXq E hE hEq
      exact ⟨s', hs', a', h'⟩
  have hy₁E : ∀ E : Ideal B, E.IsPrime → E.comap (algebraMap C B) = q → E ≠ pB → y₁ ∈ E := by
    intro E hE hEq hne
    obtain ⟨s', hs', a', ha', h'⟩ := hXq E hE hEq
    have h2 : y₁ * s' = algebraMap C B d * a' := by
      apply hBK
      rw [map_mul, map_mul, ← hy₁, ← h', hCBK]
      ring
    exact (hE.mem_or_mem (h2 ▸ E.mul_mem_left _ (ha' hne))).resolve_right hs'
  -- `Tr(y₁ c) ∈ d C` for every `c ∈ B`
  have htrC : ∀ c : B, ∃ γ : C, Algebra.trace C B (y₁ * c) = d * γ := by
    intro c
    obtain ⟨γ, hγ⟩ := exists_trace_eq_of_forall_mul_mem (C := C) (B := B) (F := Fr) (K := K)
      (F * algebraMap B K b * algebraMap C K g * algebraMap B K c) fun E _ π hπ hEπ => by
        have hπE : algebraMap C B π ∈ E :=
          (hEπ ▸ Ideal.mem_span_singleton_self π : π ∈ E.comap (algebraMap C B))
        by_cases hEp : E = pB
        · obtain ⟨s', hs', a', h'⟩ := hPB
          refine ⟨s', hEp ▸ hs', c * algebraMap C B π * a',
            E.mul_mem_right _ (E.mul_mem_left _ hπE), ?_⟩
          rw [map_mul, map_mul, ← h', hCBK]
          ring
        · obtain ⟨s', hs', a', ha', h'⟩ := hU E π hπ hEπ hEp
          refine ⟨s', hs', a' * algebraMap C B g * c,
            E.mul_mem_right _ (E.mul_mem_right _ ha'), ?_⟩
          rw [map_mul, map_mul, ← h', hCBK]
          ring
    refine ⟨γ, ?_⟩
    have htr := Algebra.trace_localization (Rₘ := Fr) (Sₘ := K) C C⁰ (y₁ * c)
    have hK : algebraMap B K (y₁ * c) =
        algebraMap C Fr d • (F * algebraMap B K b * algebraMap C K g * algebraMap B K c) := by
      rw [map_mul, ← hy₁, hCBK, Algebra.smul_def, ← IsScalarTower.algebraMap_apply C Fr K]
      ring
    rw [hK, LinearMap.map_smul, smul_eq_mul, hγ, ← map_mul] at htr
    exact (IsFractionRing.injective C Fr htr).symm
  -- the relation `y₁ s = d b a` in `A`
  have hy₁A : algebraMap B A y₁ * s = algebraMap C A d * (algebraMap B A b * a) := by
    apply hAK
    have e1 : algebraMap A K (algebraMap B A y₁) =
        F * algebraMap B K b * algebraMap D K x₀ * algebraMap C K d := by
      rw [hBAK, ← hy₁, hCBK, hgdef, hDCK]
    rw [map_mul, map_mul, map_mul, e1, ← IsScalarTower.algebraMap_apply C A K d, hBAK, ← hFP]
    ring
  -- the trace modulo `g`
  obtain ⟨N, hN, key⟩ := exists_mk_trace_eq_nsmul_of_comap_eq q rfl hg0 pB hpB
  have hsurjA : ∀ α : A, ∃ β m : B, m ∉ 𝔐 ∧ α * algebraMap B A m = algebraMap B A β := by
    intro α
    obtain ⟨⟨β, m⟩, hβ⟩ := IsLocalization.surj 𝔐.primeCompl α
    exact ⟨β, m, m.2, hβ⟩
  have hwq : Ideal.Quotient.mk q (algebraMap D C w) ∈ IsLocalRing.maximalIdeal (C ⧸ q) :=
    hmax ▸ Ideal.mem_span_singleton_self _
  obtain ⟨m, hm, hmeq⟩ := exists_mem_maximalIdeal_of_trace_mem_quotient q p hpB 𝔐 hpB𝔐 hsurjA hdq
    hwq hN
    (fun c => key (y₁ * c) fun E hE hEq hne => Ideal.mul_mem_right _ _ (hy₁E E hE hEq hne))
    htrC hy₁A
  rw [← IsScalarTower.algebraMap_apply D C A, map_mul] at hmeq
  have hbu : IsUnit (Ideal.Quotient.mk p (algebraMap B A b)) :=
    (IsLocalization.map_units A (⟨b, hb𝔐⟩ : 𝔐.primeCompl)).map _
  refine ⟨m * ↑hbu.unit⁻¹, Ideal.mul_mem_right _ _ hm, ?_⟩
  linear_combination (↑hbu.unit⁻¹ : A ⧸ p) * hmeq -
    (Ideal.Quotient.mk p (algebraMap D A w) * Ideal.Quotient.mk p a) * hbu.mul_val_inv

/-! ### Points, stalks and orders -/

/-- The prime `𝔪_z ∩ 𝒪_{X,x}` of a generization `z` of `x` depends only on the point `z`. -/
private theorem comap_maximalIdeal_stalkSpecializes_eq_of_eq {X : Scheme.{u}} {x z z' : X}
    (e : z = z') (hz : z ⤳ x) (hz' : z' ⤳ x) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk z)).comap (X.presheaf.stalkSpecializes hz).hom =
      (IsLocalRing.maximalIdeal (X.presheaf.stalk z')).comap
        (X.presheaf.stalkSpecializes hz').hom := by
  subst e
  rfl

/-- An element of the stalk at `y' = y` is an element of the stalk at `y`, in the function
field. -/
private theorem exists_algebraMap_eq_of_eq {X : Scheme.{u}} [IsIntegral X] {y y' : X}
    (e : y = y') (a : X.presheaf.stalk y') :
    ∃ b : X.presheaf.stalk y,
      algebraMap _ X.functionField b = algebraMap _ X.functionField a := by
  subst e
  exact ⟨a, rfl⟩

/-- A nonzero element of the maximal ideal of the local ring along a prime divisor has
positive order. -/
private theorem one_le_ord_of_mem_maximalIdeal {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (Γ : Mori.PrimeDivisor X)
    {a : X.presheaf.stalk Γ.genericPoint} (ha0 : a ≠ 0)
    (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk Γ.genericPoint)) :
    1 ≤ X.ord (algebraMap _ X.functionField a) Γ.genericPoint := by
  haveI := Γ.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk Γ.genericPoint)
  obtain ⟨k, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  have hϖ0 : algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact absurd (by simpa using v.isUnit) ((IsLocalRing.mem_maximalIdeal _).mp ha)
  rw [map_mul, map_pow, Scheme.ord_mul ((v.isUnit.map _).ne_zero) (pow_ne_zero _ hϖ0),
    Γ.ord_algebraMap_of_isUnit v.isUnit, ord_pow' hϖ0,
    ord_algebraMap_eq_one_of_irreducible Γ.coheight_genericPoint hϖ]
  push_cast
  omega

/-- **Prime divisors through `x` from primes of `𝒪_{X,x}`.** A prime `E` of `𝒪_{X,x}` at which
`𝒪_{X,x}` localizes to a discrete valuation ring is `𝔪_Γ ∩ 𝒪_{X,x}` for a prime divisor `Γ`
whose generic point specializes to `x`: the point of `Spec 𝒪_{X,x} → X` at `E` has local ring
`(𝒪_{X,x})_E`, of dimension one. -/
private theorem exists_primeDivisor_comap_eq {X : Scheme.{u}} [IsIntegral X] {x : X}
    (E : Ideal (X.presheaf.stalk x)) [E.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime E)] :
    ∃ (Γ : Mori.PrimeDivisor X) (hΓ : Γ.genericPoint ⤳ x),
      (IsLocalRing.maximalIdeal (X.presheaf.stalk Γ.genericPoint)).comap
        (X.presheaf.stalkSpecializes hΓ).hom = E := by
  set q : PrimeSpectrum (X.presheaf.stalk x) := ⟨E, inferInstance⟩ with hqdef
  have hz := MMP.Intersection.fromSpecStalk_specializes x q
  have hcomap := MMP.Intersection.comap_maximalIdeal_stalkSpecializes_fromSpecStalk x q
  letI := (X.presheaf.stalkSpecializes hz).hom.toAlgebra
  haveI := MMP.Intersection.isLocalization_stalkSpecializes hz
  have hco : Order.coheight (X.fromSpecStalk x q) = 1 := by
    have h2 := IsLocalization.AtPrime.ringKrullDim_eq_height
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk (X.fromSpecStalk x q))).comap
        (X.presheaf.stalkSpecializes hz).hom) (X.presheaf.stalk (X.fromSpecStalk x q))
    rw [hcomap] at h2
    have h3 := IsLocalization.AtPrime.ringKrullDim_eq_height E (Localization.AtPrime E)
    have h5 : ((Order.coheight (X.fromSpecStalk x q) : ℕ∞) : WithBot ℕ∞) = 1 := by
      rw [← ringKrullDim_stalk_eq_coheight, h2, ← h3,
        IsDiscreteValuationRing.ringKrullDim_eq_one]
    exact_mod_cast h5
  have hgen := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have hΓ : (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco).genericPoint ⤳ x := by
    rwa [hgen]
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco, hΓ, ?_⟩
  rw [comap_maximalIdeal_stalkSpecializes_eq_of_eq hgen hΓ hz, hcomap]

open exteriorPower in
/-- **Local equations from orders of forms.** Let `E` be a prime divisor of a normal variety of
dimension `N + 1` over a field `k` of characteristic zero, and `ν : k[X₀, …, X_N] → 𝒪_{X,E}`
injective, with `𝔪_E ∩ k[X] = (π)` and `𝒪_{X,E}` a ring of fractions of elements integral over
`k[X]`. If `F dX₀ ∧ ⋯ ∧ dX_N` has at most a simple pole along `E`, then `F π ∈ 𝒪_{X,E}`, and
`F π ∈ 𝔪_E` when the form has no pole: `ord_E(F dX) = ord_E F + e - 1` with `e = ord_E π`
(`exists_ordForm_smul_tprod_ιMulti_eq`). -/
private theorem exists_mul_eq_of_neg_one_le_ordForm {k : Type} [Field k] [CharZero k]
    {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X]
    [LocallyOfFiniteType sX] {N : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = N + 1)
    (E : Mori.PrimeDivisor X) :
    letI := stalkAlgebra sX E.genericPoint
    letI := functionFieldAlgebra sX
    ∀ (ν : MvPolynomial (Fin (N + 1)) k →ₐ[k] X.presheaf.stalk E.genericPoint),
      Function.Injective ν → ∀ {π : MvPolynomial (Fin (N + 1)) k}, π ≠ 0 →
      (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)).comap ν = Ideal.span {π} →
      (∀ y : X.presheaf.stalk E.genericPoint, ∃ a b : X.presheaf.stalk E.genericPoint,
        (ν : MvPolynomial (Fin (N + 1)) k →+* _).IsIntegralElem a ∧
        (ν : MvPolynomial (Fin (N + 1)) k →+* _).IsIntegralElem b ∧ IsUnit b ∧ y * b = a) →
      ∀ F : X.functionField,
        -1 ≤ E.ordForm (m := 1) ((F • PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
          ιMulti X.functionField (N + 1) (fun i => KaehlerDifferential.D k X.functionField
            (algebraMap _ X.functionField (ν (MvPolynomial.X i))))) :
          TensorPower X.functionField 1 (⋀[X.functionField]^(N + 1) Ω[X.functionField⁄k])) :
            RationalPluriForms sX (N + 1) 1) →
        ∃ a : X.presheaf.stalk E.genericPoint,
          F * algebraMap _ X.functionField (ν π) = algebraMap _ X.functionField a ∧
          (0 ≤ E.ordForm (m := 1) ((F • PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
            ιMulti X.functionField (N + 1) (fun i => KaehlerDifferential.D k X.functionField
              (algebraMap _ X.functionField (ν (MvPolynomial.X i))))) :
            TensorPower X.functionField 1 (⋀[X.functionField]^(N + 1) Ω[X.functionField⁄k])) :
              RationalPluriForms sX (N + 1) 1) →
            a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)) := by
  letI := stalkAlgebra sX E.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX E.genericPoint
  intro ν hν π hπ0 hf halg F hF1
  obtain ⟨t, u, e, ht, hu, he, hπ, -, hord⟩ :=
    exists_ordForm_smul_tprod_ιMulti_eq sX hd E ν hν hπ0 hf halg
  by_cases hF0 : F = 0
  · exact ⟨0, by rw [hF0, zero_mul, map_zero], fun _ => zero_mem _⟩
  rw [hord F hF0] at hF1 ⊢
  haveI := E.isDiscreteValuationRing_localRing
  have ht1 := ord_algebraMap_eq_one_of_irreducible E.coheight_genericPoint ht
  have ht0 : algebraMap (X.presheaf.stalk E.genericPoint) X.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht.ne_zero
  have hπ0' : algebraMap (X.presheaf.stalk E.genericPoint) X.functionField (ν π) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ((map_ne_zero_iff _ hν).mpr hπ0)
  have hπord : X.ord (algebraMap _ X.functionField (ν π)) E.genericPoint = e := by
    rw [hπ, map_mul, map_pow, Scheme.ord_mul (hu.map _).ne_zero (pow_ne_zero _ ht0),
      E.ord_algebraMap_of_isUnit hu, ord_pow' ht0, ht1]
    simp
  have hford : X.ord (F * algebraMap _ X.functionField (ν π)) E.genericPoint =
      X.ord F E.genericPoint + e := by
    rw [Scheme.ord_mul hF0 hπ0', hπord]
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_ord_nonneg E (mul_ne_zero hF0 hπ0') (by omega)
  refine ⟨a, ha.symm, fun h0 => ?_⟩
  by_contra hna
  have h2 := E.ord_algebraMap_of_isUnit (IsLocalRing.notMem_maximalIdeal.mp hna)
  rw [ha, hford] at h2
  omega

open exteriorPower in
/-- **Codifferent bounds from the orders of a form.** Let `φ : k[X₀, …, X_N] → 𝒪_{X,x}` be a chart
inducing charts at every generization of `x`, with the local rings there rings of fractions of
integral elements. Let `E` be a prime of `𝒪_{X,x}` with `(𝒪_{X,x})_E` a discrete valuation ring
and `E ∩ k[X] = (π)`. If `F dX₀ ∧ ⋯ ∧ dX_N` has no pole along the prime divisor of `E`
(`exists_primeDivisor_comap_eq`), then `F π s = a` with `s ∉ E` and `a ∈ E`. -/
private theorem exists_mul_mem_of_ordForm_nonneg {k : Type} [Field k] [CharZero k]
    {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X]
    [LocallyOfFiniteType sX] {N : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = N + 1)
    {x : X} (φ : MvPolynomial (Fin (N + 1)) k →+* X.presheaf.stalk x)
    (hφ : ∀ (z : X) (hz : z ⤳ x), ∃ νz : (letI := stalkAlgebra sX z;
      MvPolynomial (Fin (N + 1)) k →ₐ[k] X.presheaf.stalk z),
        ∀ d, νz d = (X.presheaf.stalkSpecializes hz).hom (φ d))
    (hinj : Function.Injective
      ((algebraMap (X.presheaf.stalk x) X.functionField).comp φ))
    (halg : ∀ (z : X) (hz : z ⤳ x) (y : X.presheaf.stalk z), ∃ a b : X.presheaf.stalk z,
      ((X.presheaf.stalkSpecializes hz).hom.comp φ).IsIntegralElem a ∧
      ((X.presheaf.stalkSpecializes hz).hom.comp φ).IsIntegralElem b ∧ IsUnit b ∧ y * b = a)
    (F : X.functionField) (E : Ideal (X.presheaf.stalk x)) [E.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime E)] {π : MvPolynomial (Fin (N + 1)) k}
    (hπ0 : π ≠ 0) (hEπ : E.comap φ = Ideal.span {π})
    (hord : letI := functionFieldAlgebra sX; ∀ (Γ : Mori.PrimeDivisor X)
      (hΓ : Γ.genericPoint ⤳ x),
      (IsLocalRing.maximalIdeal (X.presheaf.stalk Γ.genericPoint)).comap
        (X.presheaf.stalkSpecializes hΓ).hom = E →
      0 ≤ Γ.ordForm (m := 1) ((F • PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
          ιMulti X.functionField (N + 1) (fun i => KaehlerDifferential.D k X.functionField
            (algebraMap (X.presheaf.stalk x) X.functionField (φ (MvPolynomial.X i))))) :
          TensorPower X.functionField 1 (⋀[X.functionField]^(N + 1) Ω[X.functionField⁄k])) :
            RationalPluriForms sX (N + 1) 1)) :
    ∃ s ∉ E, ∃ a ∈ E, F * algebraMap _ X.functionField (φ π) *
      algebraMap _ X.functionField s = algebraMap _ X.functionField a := by
  letI := functionFieldAlgebra sX
  obtain ⟨Γ, hΓ, hΓE⟩ := exists_primeDivisor_comap_eq E
  obtain ⟨νΓ, hνΓ⟩ := hφ _ hΓ
  letI := stalkAlgebra sX Γ.genericPoint
  have hK : ∀ d, algebraMap _ X.functionField (νΓ d) =
      algebraMap (X.presheaf.stalk x) X.functionField (φ d) := fun d => by
    rw [hνΓ, algebraMap_stalkSpecializes']
  have hνinj : Function.Injective νΓ := fun a b h => hinj (by
    simp only [RingHom.comp_apply]
    rw [← hK, ← hK, h])
  have hf : (IsLocalRing.maximalIdeal (X.presheaf.stalk Γ.genericPoint)).comap νΓ =
      Ideal.span {π} := by
    rw [← hEπ, ← hΓE]
    ext d
    simp only [Ideal.mem_comap, hνΓ]
  have hνeq : (νΓ : MvPolynomial (Fin (N + 1)) k →+* _) =
      (X.presheaf.stalkSpecializes hΓ).hom.comp φ := RingHom.ext hνΓ
  have halgΓ : ∀ y : X.presheaf.stalk Γ.genericPoint, ∃ a b : X.presheaf.stalk Γ.genericPoint,
      (νΓ : MvPolynomial (Fin (N + 1)) k →+* _).IsIntegralElem a ∧
      (νΓ : MvPolynomial (Fin (N + 1)) k →+* _).IsIntegralElem b ∧ IsUnit b ∧ y * b = a := by
    rw [hνeq]
    exact halg _ hΓ
  have hfam : (fun i => KaehlerDifferential.D k X.functionField
      (algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField (νΓ (MvPolynomial.X i)))) =
      fun i => KaehlerDifferential.D k X.functionField
        (algebraMap (X.presheaf.stalk x) X.functionField (φ (MvPolynomial.X i))) := by
    funext i
    rw [hK]
  have h0 := hord Γ hΓ hΓE
  rw [← hfam] at h0
  obtain ⟨a, ha, haE⟩ := exists_mul_eq_of_neg_one_le_ordForm sX hd Γ νΓ hνinj hπ0 hf halgΓ F
    (le_trans (by norm_num) h0)
  letI := (X.presheaf.stalkSpecializes hΓ).hom.toAlgebra
  haveI := MMP.Intersection.isLocalization_stalkSpecializes hΓ
  obtain ⟨⟨a', s⟩, has⟩ := IsLocalization.surj ((IsLocalRing.maximalIdeal
    (X.presheaf.stalk Γ.genericPoint)).comap (X.presheaf.stalkSpecializes hΓ).hom).primeCompl a
  have has' : a * (X.presheaf.stalkSpecializes hΓ).hom s =
      (X.presheaf.stalkSpecializes hΓ).hom a' := has
  refine ⟨s, fun h => s.2 (hΓE ▸ h), a', ?_, ?_⟩
  · rw [← hΓE, Ideal.mem_comap, ← has']
    exact Ideal.mul_mem_right _ _ (haE h0)
  · have h1 := congrArg (algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField) has'
    rwa [map_mul, algebraMap_stalkSpecializes', algebraMap_stalkSpecializes', ← ha, hK] at h1

/-- **The order bound at `Q`.** On the local ring of a prime divisor `Q`, if `g s = a` and
`u t^e a = s m` in the function field, with `u` a unit, `t` a uniformizer and `m` in the maximal
ideal, then `g` has order at least `1 - e` along `Q`. -/
private theorem one_sub_le_ord_of_mul_eq {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] (Q : Mori.PrimeDivisor T) {g : T.functionField}
    {s a m t v : T.presheaf.stalk Q.genericPoint} {e : ℕ} (hg : g ≠ 0) (hs : s ≠ 0)
    (ht : Irreducible t) (hv : IsUnit v)
    (hm : m ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk Q.genericPoint))
    (hga : g * algebraMap _ T.functionField s = algebraMap _ T.functionField a)
    (hrel : algebraMap _ T.functionField v * algebraMap _ T.functionField t ^ e *
      algebraMap _ T.functionField a = algebraMap _ T.functionField s * algebraMap _ _ m) :
    1 - (e : ℤ) ≤ T.ord g Q.genericPoint := by
  haveI := Q.isDiscreteValuationRing_localRing
  have hinj : Function.Injective
      (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField) :=
    IsFractionRing.injective _ _
  have hs0 := (map_ne_zero_iff _ hinj).mpr hs
  have ha0 : algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField a ≠ 0 := by
    intro h0
    rw [h0] at hga
    exact mul_ne_zero hg hs0 hga
  have ht0 := (map_ne_zero_iff _ hinj).mpr ht.ne_zero
  have hv0 : algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField v ≠ 0 :=
    (hv.map _).ne_zero
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at hrel
    exact mul_ne_zero (mul_ne_zero hv0 (pow_ne_zero _ ht0)) ha0 hrel
  have hordm := one_le_ord_of_mem_maximalIdeal Q hm0 hm
  have hordrel := congrArg (fun f => T.ord f Q.genericPoint) hrel
  rw [Scheme.ord_mul (mul_ne_zero hv0 (pow_ne_zero _ ht0)) ha0,
    Scheme.ord_mul hv0 (pow_ne_zero _ ht0),
    Scheme.ord_mul hs0 ((map_ne_zero_iff _ hinj).mpr hm0),
    Q.ord_algebraMap_of_isUnit hv, ord_pow' ht0,
    ord_algebraMap_eq_one_of_irreducible Q.coheight_genericPoint ht] at hordrel
  have hordg := congrArg (fun f => T.ord f Q.genericPoint) hga
  rw [Scheme.ord_mul hg hs0] at hordg
  omega

/-- **The Poincaré residue of a section of `ω_X(S)` is regular.** Let `X` be a normal variety of
dimension `n + 1` over a field `k` of characteristic zero, `j : T ⟶ X` the inclusion of a normal
prime divisor `P` and `Q` a prime divisor of `T`. If a rational top form `α` on `X` has at most a
simple pole along `P` and no pole along any other prime divisor through `j(η_Q)`, then its Poincaré
residue `ρ` (`MMP.Fourfold.IsPoincareResidue`) has no pole at `Q`. -/
theorem zero_le_ordForm_of_isPoincareResidue
    {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (Q : Mori.PrimeDivisor T) {α : RationalPluriForms sX (n + 1) 1}
    {ρ : RationalPluriForms (j ≫ sX) n 1} (hαP : -1 ≤ P.ordForm α)
    (hαE : ∀ E : Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support → E ≠ P → 0 ≤ E.ordForm α)
    (hres : IsPoincareResidue sX j n 1 α ρ) : 0 ≤ Q.ordForm ρ := by
  classical
  have hlft : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra sX
  have hjT := MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hP
  -- the point `y = η_P` specializing to `x = j(η_Q)`
  have hyx : j (genericPoint T) ⤳ j Q.genericPoint :=
    j.base.hom.map_specializes (genericPoint_specializes _)
  -- the prime `p` of `P` in `𝒪_{X,x}`
  set p := (IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T)))).comap
    (X.presheaf.stalkSpecializes hyx).hom with hpdef
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  -- the Noether-normalization chart
  obtain ⟨n', rfl, U, hU', hxU, ν, hν, hνint, hpA, hdvrQ, hkerT, hpX, w', hw'0, hw'X, hv, -,
    mkν₀, hνK₀, νT, hνT₀, -, -, -, ⟨tQ, uQ, eQ, htQ, huQ, heQ, hwQ, hιT, hordT⟩, hνyfacts⟩ :=
    exists_noetherNormalization_chart_of_primeDivisor sX hX hdim j hT P hP Q
  have hd : (Algebra.trdeg k X.functionField).toNat = n' + 1 + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  letI := sectionAlgebra sX U
  letI : Algebra Γ(X, U) (X.presheaf.stalk (j Q.genericPoint)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hxU⟩
  haveI := hU'.isLocalization_stalk ⟨_, hxU⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU'
  haveI := functionField_isScalarTower X U ⟨_, hxU⟩
  haveI : IsIntegrallyClosed (X.presheaf.stalk (j Q.genericPoint)) :=
    IsNormal.stalk_normal (j Q.genericPoint)
  set 𝔮 := (hU'.primeIdealOf ⟨_, hxU⟩).asIdeal with h𝔮
  haveI := hdvrQ
  have hkerp : RingHom.ker (j.stalkMap Q.genericPoint).hom = p :=
    Ideal.ext fun a => RingHom.mem_ker.trans (hkerT a)
  let eT : (X.presheaf.stalk (j Q.genericPoint) ⧸ p) ≃+* T.presheaf.stalk Q.genericPoint :=
    (Ideal.quotEquivOfEq hkerp.symm).trans (RingHom.quotientKerEquivOfSurjective
      (SurjectiveOnStalks.stalkMap_surjective j Q.genericPoint))
  -- the base `D = k[X₀, …, X_n]` and its algebra structures
  letI : Algebra (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) := ν.toRingHom.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq fun c => (ν.commutes c).symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) := ⟨hνint⟩
  haveI := finiteType_sectionAlgebra sX hU'
  haveI : Algebra.FiniteType (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  haveI : Module.Finite (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) := Algebra.IsIntegral.finite
  haveI : FaithfulSMul (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hν
  letI : Algebra (MvPolynomial (Fin (n' + 1 + 1)) k) (X.presheaf.stalk (j Q.genericPoint)) :=
    ((algebraMap Γ(X, U) (X.presheaf.stalk (j Q.genericPoint))).comp
      (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U)
      (X.presheaf.stalk (j Q.genericPoint)) := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra (MvPolynomial (Fin (n' + 1 + 1)) k) X.functionField :=
    ((algebraMap Γ(X, U) X.functionField).comp
      (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower (MvPolynomial (Fin (n' + 1 + 1)) k) (X.presheaf.stalk (j Q.genericPoint))
      X.functionField := IsScalarTower.of_algebraMap_eq fun d => by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin (n' + 1 + 1)) k) Γ(X, U) X.functionField,
      IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (j Q.genericPoint))
        X.functionField]
    rfl
  -- the chart in the notation of the base
  have hDK : ∀ d, algebraMap (X.presheaf.stalk (j Q.genericPoint)) X.functionField
      (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) (X.presheaf.stalk (j Q.genericPoint)) d) =
      algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) X.functionField d := fun d =>
    (IsScalarTower.algebraMap_apply _ _ _ d).symm
  have hDKinj : Function.Injective (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
      X.functionField) := (IsFractionRing.injective Γ(X, U) X.functionField).comp hν
  have mkν : ∀ (z : X) (hz : z ⤳ j Q.genericPoint), ∃ νz : (letI := stalkAlgebra sX z;
      MvPolynomial (Fin (n' + 1 + 1)) k →ₐ[k] X.presheaf.stalk z), ∀ d, νz d =
        (X.presheaf.stalkSpecializes hz).hom (algebraMap _
          (X.presheaf.stalk (j Q.genericPoint)) d) := mkν₀
  have hνK : ∀ (z : X) (hz : z ⤳ j Q.genericPoint) (νz : (letI := stalkAlgebra sX z;
      MvPolynomial (Fin (n' + 1 + 1)) k →ₐ[k] X.presheaf.stalk z)), (∀ d, νz d =
        (X.presheaf.stalkSpecializes hz).hom (algebraMap _
          (X.presheaf.stalk (j Q.genericPoint)) d)) → ∀ d,
      algebraMap (X.presheaf.stalk z) X.functionField (νz d) =
        algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) X.functionField d := fun z hz νz hνz d =>
    (hνK₀ z hz νz hνz d).trans (hDK d)
  have hinj : Function.Injective ((algebraMap (X.presheaf.stalk (j Q.genericPoint))
      X.functionField).comp (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
        (X.presheaf.stalk (j Q.genericPoint)))) := fun a b h => hDKinj (by
    simpa only [RingHom.comp_apply, hDK] using h)
  have halg : ∀ (z : X) (hz : z ⤳ j Q.genericPoint) (y : X.presheaf.stalk z),
      ∃ a b : X.presheaf.stalk z,
      ((X.presheaf.stalkSpecializes hz).hom.comp (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
        (X.presheaf.stalk (j Q.genericPoint)))).IsIntegralElem a ∧
      ((X.presheaf.stalkSpecializes hz).hom.comp (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
        (X.presheaf.stalk (j Q.genericPoint)))).IsIntegralElem b ∧ IsUnit b ∧ y * b = a :=
    fun z hz y => exists_isIntegralElem_mul_eq 𝔮 ν.toRingHom hνint
      (X.presheaf.stalkSpecializes hz).hom (fun y => by
        letI := (X.presheaf.stalkSpecializes hz).hom.toAlgebra
        haveI := MMP.Intersection.isLocalization_stalkSpecializes hz
        obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj ((IsLocalRing.maximalIdeal
          (X.presheaf.stalk z)).comap (X.presheaf.stalkSpecializes hz).hom).primeCompl y
        exact ⟨a, s, IsLocalization.map_units _ s, h⟩) y
  letI := stalkAlgebra (j ≫ sX) Q.genericPoint
  letI := functionFieldAlgebra (j ≫ sX)
  have hνT : ∀ a, νT a = (j.stalkMap Q.genericPoint).hom (algebraMap _
      (X.presheaf.stalk (j Q.genericPoint)) (MvPolynomial.rename Fin.succ a)) := hνT₀
  obtain ⟨νy, hνy⟩ := mkν _ hyx
  obtain ⟨hX0m, hX00, hfamT, hy⟩ := hνyfacts νy hνy
  -- the chart along `P`
  have hPx : P.genericPoint ⤳ j Q.genericPoint := by rwa [← hjT]
  obtain ⟨νP, hνP⟩ := mkν _ hPx
  have hcomapP := comap_maximalIdeal_stalkSpecializes_eq_of_eq hjT.symm hPx hyx
  letI := stalkAlgebra sX P.genericPoint
  have hνPinj : Function.Injective νP := fun a b h => hDKinj (by
    rw [← hνK _ hPx νP hνP, ← hνK _ hPx νP hνP, h])
  have hfP : (IsLocalRing.maximalIdeal (X.presheaf.stalk P.genericPoint)).comap νP =
      Ideal.span {MvPolynomial.X 0} := by
    rw [← hpX]
    ext d
    have h1 : d ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk P.genericPoint)).comap νP ↔
        algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) (X.presheaf.stalk (j Q.genericPoint)) d ∈
          (IsLocalRing.maximalIdeal (X.presheaf.stalk P.genericPoint)).comap
            (X.presheaf.stalkSpecializes hPx).hom := by
      rw [Ideal.mem_comap, Ideal.mem_comap, hνP]
    rw [h1, hcomapP]
    exact Iff.rfl
  have halgP : ∀ y : X.presheaf.stalk P.genericPoint, ∃ a b : X.presheaf.stalk P.genericPoint,
      (νP : MvPolynomial (Fin (n' + 1 + 1)) k →+* _).IsIntegralElem a ∧
      (νP : MvPolynomial (Fin (n' + 1 + 1)) k →+* _).IsIntegralElem b ∧ IsUnit b ∧
        y * b = a := by
    rw [show (νP : MvPolynomial (Fin (n' + 1 + 1)) k →+* _) = (X.presheaf.stalkSpecializes
      hPx).hom.comp (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
        (X.presheaf.stalk (j Q.genericPoint))) from RingHom.ext hνP]
    exact halg _ hPx
  have hfamP : (fun i => KaehlerDifferential.D k X.functionField
      (algebraMap (X.presheaf.stalk P.genericPoint) X.functionField (νP (MvPolynomial.X i)))) =
      fun i => KaehlerDifferential.D k X.functionField
        (algebraMap (X.presheaf.stalk (j Q.genericPoint)) X.functionField
          (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) (X.presheaf.stalk (j Q.genericPoint))
            (MvPolynomial.X i))) := by
    funext i
    rw [hνK _ hPx νP hνP, hDK]
  have hfamy : (fun i => KaehlerDifferential.D k X.functionField
      (algebraMap (X.presheaf.stalk (j (genericPoint T))) X.functionField
        (νy (MvPolynomial.X i)))) =
      fun i => KaehlerDifferential.D k X.functionField
        (algebraMap (X.presheaf.stalk (j Q.genericPoint)) X.functionField
          (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) (X.presheaf.stalk (j Q.genericPoint))
            (MvPolynomial.X i))) := by
    funext i
    rw [hνK _ hyx νy hνy, hDK]
  obtain ⟨-, -, -, -, -, -, -, hιP, -⟩ :=
    exists_ordForm_smul_tprod_ιMulti_eq sX hd P νP hνPinj (MvPolynomial.X_ne_zero 0) hfP halgP
  rw [hfamP] at hιP
  -- `α = F dX₀ ∧ ⋯ ∧ dX_n`
  obtain ⟨σ, hσdef⟩ : ∃ σ : RationalPluriForms sX (n' + 1 + 1) 1,
      σ = ((PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
        exteriorPower.ιMulti X.functionField (n' + 1 + 1) (fun i =>
          KaehlerDifferential.D k X.functionField
            (algebraMap (X.presheaf.stalk (j Q.genericPoint)) X.functionField
              (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
                (X.presheaf.stalk (j Q.genericPoint)) (MvPolynomial.X i))))) :
        TensorPower X.functionField 1
          (⋀[X.functionField]^(n' + 1 + 1) Ω[X.functionField⁄k])) :
            RationalPluriForms sX (n' + 1 + 1) 1) := ⟨_, rfl⟩
  have hσ0 : σ ≠ 0 := fun h => hιP <| tprod_fin_one_injective (F := X.functionField) <|
    (hσdef.symm.trans h).trans (MultilinearMap.map_coord_zero _ (0 : Fin 1) rfl).symm
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sX) (d := n' + 1 + 1) (by rw [hdim]; norm_cast)
  have hrank : Module.finrank X.functionField (RationalPluriForms sX (n' + 1 + 1) 1) = 1 := by
    let bb : Module.Basis Unit X.functionField (RationalPluriForms sX (n' + 1 + 1) 1) :=
      ZTensorPower.basis b₀ 1
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  obtain ⟨F, hF⟩ := (finrank_eq_one_iff_of_nonzero' σ hσ0).mp hrank α
  have hα : α = ((F • PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
        exteriorPower.ιMulti X.functionField (n' + 1 + 1) (fun i =>
          KaehlerDifferential.D k X.functionField
            (algebraMap (X.presheaf.stalk (j Q.genericPoint)) X.functionField
              (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
                (X.presheaf.stalk (j Q.genericPoint)) (MvPolynomial.X i))))) :
        TensorPower X.functionField 1
          (⋀[X.functionField]^(n' + 1 + 1) Ω[X.functionField⁄k])) :
            RationalPluriForms sX (n' + 1 + 1) 1) := by
    subst hσdef
    exact hF.symm
  -- the bound along `P`: `F x₀ ∈ 𝒪_{X,P}`
  have hαP' := hαP
  rw [hα, ← hfamP] at hαP'
  obtain ⟨aP, haP, -⟩ := exists_mul_eq_of_neg_one_le_ordForm sX hd P νP hνPinj
    (MvPolynomial.X_ne_zero 0) hfP halgP F hαP'
  obtain ⟨g₀, hg₀⟩ := exists_algebraMap_eq_of_eq hjT aP
  have hFg : F * algebraMap _ X.functionField (νy (MvPolynomial.X 0)) =
      algebraMap _ X.functionField g₀ := by
    rw [hg₀, ← haP, hνK _ hyx νy hνy, hνK _ hPx νP hνP]
  letI := (X.presheaf.stalkSpecializes hyx).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (j (genericPoint T))) p :=
    MMP.Intersection.isLocalization_stalkSpecializes hyx
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj p.primeCompl g₀
  have has' : g₀ * (X.presheaf.stalkSpecializes hyx).hom s =
      (X.presheaf.stalkSpecializes hyx).hom a := has
  have hs : (s : X.presheaf.stalk (j Q.genericPoint)) ∉ p := s.2
  have hFP : F * algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) X.functionField
      (MvPolynomial.X 0) * algebraMap _ X.functionField (s : X.presheaf.stalk (j Q.genericPoint)) =
      algebraMap _ X.functionField a := by
    have h1 := congrArg (algebraMap (X.presheaf.stalk (j (genericPoint T))) X.functionField) has'
    rwa [map_mul, algebraMap_stalkSpecializes', algebraMap_stalkSpecializes', ← hFg,
      hνK _ hyx νy hνy] at h1
  -- the bounds along the other prime divisors through `x`
  have hFE : ∀ (E : Ideal (X.presheaf.stalk (j Q.genericPoint))) [E.IsPrime],
      IsDiscreteValuationRing (Localization.AtPrime E) → E ≠ p →
      ∀ π : MvPolynomial (Fin (n' + 1 + 1)) k, π ≠ 0 →
        E.comap (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
          (X.presheaf.stalk (j Q.genericPoint))) = Ideal.span {π} →
        ∃ s ∉ E, ∃ a ∈ E, F * algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) X.functionField π *
          algebraMap _ X.functionField s = algebraMap _ X.functionField a := by
    intro E _ hdvr hEp π hπ0 hEπ
    haveI := hdvr
    obtain ⟨s', hs', a', ha', h'⟩ := exists_mul_mem_of_ordForm_nonneg sX hd
      (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k) (X.presheaf.stalk (j Q.genericPoint)))
      mkν hinj halg F E hπ0 hEπ fun Γ hΓ hΓE => by
        rw [← hα]
        refine hαE Γ ?_ fun hΓP => hEp ?_
        · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
          exact hΓ
        · rw [← hΓE, hpdef]
          exact comap_maximalIdeal_stalkSpecializes_eq_of_eq (by rw [hΓP]; exact hjT.symm) hΓ hyx
    exact ⟨s', hs', a', ha', by rwa [← hDK]⟩
  -- the ring-level bound
  obtain ⟨m, hm, hmeq⟩ := exists_mem_maximalIdeal_of_residue_ring k
    (D := MvPolynomial (Fin (n' + 1 + 1)) k) (R := Γ(X, U))
    (A := X.presheaf.stalk (j Q.genericPoint)) (K := X.functionField) 𝔮 p
    (x₀ := MvPolynomial.X 0) (w := MvPolynomial.rename Fin.succ w') (MvPolynomial.X_ne_zero 0)
    (Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime) hpX hw'X hv
    hFE hs hFP
  -- the residue
  obtain ⟨e, he, hres', -⟩ :=
    exists_isPoincareResidue_smul_tprod_ιMulti sX hd j P hjT νy hX0m hX00 hy hFg
  rw [hfamy, ← hα] at hres'
  have hρ := IsPoincareResidue.unique_of_isClosedImmersion P hjT hres hres'
  rw [hρ, ← hfamT]
  -- the order of the residue at `Q`
  haveI := Q.isDiscreteValuationRing_localRing
  have hsqT : ∀ a, algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
      ((j.stalkMap Q.genericPoint).hom a) =
      (j.stalkMap (genericPoint T)).hom ((X.presheaf.stalkSpecializes hyx).hom a) := fun a =>
    (Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ (genericPoint_specializes _) a).symm
  have hg₀T : (j.stalkMap (genericPoint T)).hom g₀ *
      algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
        ((j.stalkMap Q.genericPoint).hom s) =
      algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
        ((j.stalkMap Q.genericPoint).hom a) := by
    rw [hsqT, hsqT, ← map_mul, has']
  have hπQs : (j.stalkMap Q.genericPoint).hom s ≠ 0 := fun h => hs ((hkerT s).mp h)
  haveI : CharZero T.functionField :=
    charZero_of_injective_algebraMap (algebraMap k T.functionField).injective
  have he0 : (e : T.functionField) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  by_cases hg₀0 : (j.stalkMap (genericPoint T)).hom g₀ = 0
  · rw [hg₀0, mul_zero, zero_smul]
    exact (PrimeDivisor.ordForm_zero Q).ge
  -- the relation `w̄ ā = s̄ m` at `Q`
  have heTmk : ∀ a, eT (Ideal.Quotient.mk p a) = (j.stalkMap Q.genericPoint).hom a :=
    fun a => rfl
  have hrelT := congrArg (fun z => algebraMap (T.presheaf.stalk Q.genericPoint)
    T.functionField (eT z)) hmeq
  simp only [map_mul, heTmk] at hrelT
  have hwν : (j.stalkMap Q.genericPoint).hom (algebraMap (MvPolynomial (Fin (n' + 1 + 1)) k)
      (X.presheaf.stalk (j Q.genericPoint)) (MvPolynomial.rename Fin.succ w')) = νT w' :=
    (hνT w').symm
  rw [hwν, hwQ, map_mul, map_pow] at hrelT
  have hmT : eT m ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk Q.genericPoint) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal _).mp hm
    simpa using hu.map eT.symm
  have hord := one_sub_le_ord_of_mul_eq Q hg₀0 hπQs htQ huQ hmT hg₀T hrelT
  have horde : T.ord (e : T.functionField) Q.genericPoint = 0 := by
    rw [show (e : T.functionField) = algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
      (e : T.presheaf.stalk Q.genericPoint) by simp]
    refine Q.ord_algebraMap_of_isUnit ?_
    rw [← map_natCast (algebraMap k (T.presheaf.stalk Q.genericPoint))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr he.ne')).map _
  rw [hordT _ (mul_ne_zero he0 hg₀0), Scheme.ord_mul he0 hg₀0, horde]
  omega

end MMP.Fourfold
