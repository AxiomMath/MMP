module
public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.Curves.MulticrossNormalization
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Separable
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationStalkCompletion

/-!
# Normalization at a split formal node

Let `R` be a reduced one-dimensional local ring essentially of finite type over a field `k`,
with residue field `K`, whose completion is a split node: `R̂ ≃ K[[u, v]]/(uv)`. Then the
normalization `B` of `R` (the integral closure of `R` in its total ring of fractions) is a finite
`R`-module with exactly two maximal ideals `𝔪₁, 𝔪₂` over the maximal ideal of `R`. The local
rings `B_{𝔪ᵢ}` are discrete valuation rings, and their completions are identified with `K[[u]]`
and `K[[v]]` so that the map `R → B_{𝔪ᵢ} → B̂_{𝔪ᵢ}` becomes, through `R → R̂ ≃ K[[u, v]]/(uv)`,
the restriction to the branch `v = 0`, resp. `u = 0`.

## Main results

* `MMP.exists_adicCompletion_localization_ringEquiv_powerSeries_of_splitNode`.

## Implementation notes

The completion of a local ring `A` is `AdicCompletion (IsLocalRing.maximalIdeal A) A`. The total
ring of fractions is any localization `Q` of `R` at its nonzerodivisors, and the normalization is
any `B` with `IsIntegralClosure B R Q`. The identification `R̂ ≃ K[[u, v]]/(uv)` is an
isomorphism of rings, the completion not being canonically a `K`-algebra. Restriction to the
branch `v = 0` is the substitution `u ↦ X, v ↦ 0` of `MvPowerSeries.subst`, read on any lift
to `K[[u, v]]` of a class in the quotient; the compatibility is asserted on the image of `R`,
which is dense in `R̂`.

The proof: `B` is Noetherian and Nagata, `R` being essentially of finite type over a field. The
completion of `B` along `𝔪_R B` is the integral closure of `R̂` in its total ring of fractions
(`IsLocalRing.exists_injective_range_eq_integralClosure_adicCompletion_fractionRing`), hence,
through `e` and `K[[u, v]]/(uv) ≃ {(f, g) : f(0) = g(0)}`
(`Stacks.Curves.quotientAlgEquivMulticross`), it is `K[[t]] × K[[t]]`
(`Stacks.Curves.integralClosureMulticrossAlgEquiv`). It is also the product of the completed
local rings of `B` above `𝔪_R` (`AdicCompletion.nonempty_algEquiv_pi_primesOver`). A ring
isomorphism between two products of local rings matches the factors, since it matches their
primitive idempotents; this yields the two maximal ideals and the two completions. The local
rings are discrete valuation rings because `B` is normal of dimension one and a nonzerodivisor
of `𝔪_R` stays a nonzerodivisor in `B`.

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013]
-/

@[expose] public section

open IsLocalRing

namespace MMP

/-- A local ring essentially of finite type over a field is a Nagata ring. -/
private theorem isNagataRing_of_essFiniteType (k : Type*) [Field k] (R : Type*) [CommRing R]
    [IsLocalRing R] [Algebra k R] [Algebra.EssFiniteType k R] : IsNagataRing R :=
  isNagataRing_of_isQuasiExcellent
    ((isQuasiExcellent_and_isExcellent_of_essFiniteType (R := k) (S := R)).2
      (isExcellent_of_standard_classes_and_finiteType.{_, 0}.1 k)).1

/-- The normalization of `R` is the integral closure of `R` in its total ring of fractions. -/
private theorem nonempty_integralClosure_fractionRing_algEquiv
    (R : Type*) [CommRing R] (Q B : Type*) [CommRing Q] [Algebra R Q]
    [IsLocalization (nonZeroDivisors R) Q]
    [CommRing B] [Algebra R B] [Algebra B Q] [IsScalarTower R B Q] [IsIntegralClosure B R Q] :
    Nonempty (integralClosure R (FractionRing R) ≃ₐ[R] B) := by
  let eQ : FractionRing R ≃ₐ[R] Q :=
    IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R) Q
  have e1 := (integralClosure R (FractionRing R)).equivMapOfInjective eQ.toAlgHom eQ.injective
  rw [integralClosure_map_algEquiv eQ] at e1
  exact ⟨e1.trans (IsIntegralClosure.equiv R (integralClosure R Q) Q B)⟩

/-! ### Ring isomorphisms between products of local rings -/

section PiLocal

/-- An idempotent of a local ring is `0` or `1`. -/
private theorem eq_zero_or_eq_one_of_isIdempotentElem {A : Type*} [CommRing A] [IsLocalRing A]
    {e : A} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr (by simpa using (h.mul_left_inj).1 (by rw [he.eq, one_mul]))
  · refine Or.inl ((h.mul_right_inj).1 ?_)
    rw [mul_zero, sub_mul, one_mul, he.eq, sub_self]

/-- `e` is a primitive idempotent: a nonzero idempotent which every idempotent either kills or
fixes. -/
private def IsPrimitive {A : Type*} [CommRing A] (e : A) : Prop :=
  IsIdempotentElem e ∧ e ≠ 0 ∧ ∀ f : A, IsIdempotentElem f → f * e = 0 ∨ f * e = e

private theorem IsPrimitive.map {A A' : Type*} [CommRing A] [CommRing A'] (Φ : A ≃+* A') {e : A}
    (he : IsPrimitive e) : IsPrimitive (Φ e) := by
  refine ⟨he.1.map Φ, fun h => he.2.1 (Φ.injective (by rw [h, map_zero])), fun f hf => ?_⟩
  rcases he.2.2 (Φ.symm f) (hf.map Φ.symm) with h | h
  · exact Or.inl (by simpa using congrArg Φ h)
  · exact Or.inr (by simpa using congrArg Φ h)

private theorem mul_single_one {ι : Type*} [DecidableEq ι] {L : ι → Type*}
    [∀ i, CommRing (L i)] (f : ∀ i, L i) (i : ι) : f * Pi.single i 1 = Pi.single i (f i) := by
  rw [← Pi.single_mul_right, mul_one]

private theorem single_one_injective {ι : Type*} [DecidableEq ι] {L : ι → Type*}
    [∀ i, CommRing (L i)] [∀ i, Nontrivial (L i)] {i i' : ι}
    (h : (Pi.single i 1 : ∀ i, L i) = Pi.single i' 1) : i = i' := by
  by_contra hne
  simpa [Pi.single_eq_of_ne hne] using congrFun h i

variable {ι : Type*} {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, IsLocalRing (L i)]

/-- The primitive idempotents of a product of local rings are the unit vectors. -/
private theorem isPrimitive_pi_iff [DecidableEq ι] (e : ∀ i, L i) :
    IsPrimitive e ↔ ∃ i, e = Pi.single i 1 := by
  constructor
  · rintro ⟨he, hne, hprim⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hei : e i = 1 := (eq_zero_or_eq_one_of_isIdempotentElem
      (congrFun he.eq i : e i * e i = e i)).resolve_left hi
    refine ⟨i, ?_⟩
    have hidem : IsIdempotentElem (Pi.single i (1 : L i) : ∀ i, L i) := by
      simp [IsIdempotentElem, mul_single_one]
    rcases hprim _ hidem with h | h <;> rw [mul_comm, mul_single_one, hei] at h
    · exact absurd (congrFun h i) (by simp)
    · exact h.symm
  · rintro ⟨i, rfl⟩
    refine ⟨by simp [IsIdempotentElem, mul_single_one], fun h => by simpa using congrFun h i,
      fun f hf => ?_⟩
    rw [mul_single_one]
    rcases eq_zero_or_eq_one_of_isIdempotentElem (congrFun hf.eq i : f i * f i = f i) with h | h
    · exact Or.inl (by rw [h, Pi.single_zero])
    · exact Or.inr (by rw [h])

/-- A ring isomorphism between two products of local rings matches the factors: there is a
bijection `σ` of the index sets and isomorphisms `L i ≃+* P (σ i)` through which the
isomorphism acts factorwise. -/
private theorem exists_equiv_ringEquiv_of_ringEquiv_pi {κ : Type*} {P : κ → Type*}
    [∀ j, CommRing (P j)] [∀ j, IsLocalRing (P j)] (Θ : (∀ i, L i) ≃+* ∀ j, P j) :
    ∃ (σ : ι ≃ κ) (θ : ∀ i, L i ≃+* P (σ i)), ∀ x i, θ i (x i) = Θ x (σ i) := by
  classical
  have hσ : ∀ i, ∃ j, Θ (Pi.single i 1) = Pi.single j 1 := fun i =>
    (isPrimitive_pi_iff _).1 (((isPrimitive_pi_iff _).2 ⟨i, rfl⟩).map Θ)
  have hτ : ∀ j, ∃ i, Θ.symm (Pi.single j 1) = Pi.single i 1 := fun j =>
    (isPrimitive_pi_iff _).1 (((isPrimitive_pi_iff _).2 ⟨j, rfl⟩).map Θ.symm)
  choose σ hσ using hσ
  have hbij : Function.Bijective σ := by
    refine ⟨fun i i' h => single_one_injective (Θ.injective (by rw [hσ, hσ, h])), fun j => ?_⟩
    obtain ⟨i, hi⟩ := hτ j
    refine ⟨i, single_one_injective (L := P) ?_⟩
    rw [← hσ, ← hi, RingEquiv.apply_symm_apply]
  have hcarry : ∀ (i : ι) (a : L i),
      Θ (Pi.single i a) = Pi.single (σ i) (Θ (Pi.single i a) (σ i)) := by
    intro i a
    rw [← mul_single_one, ← hσ, ← map_mul, mul_single_one, Pi.single_eq_same]
  have hkey : ∀ (x : ∀ i, L i) (i : ι), Θ (Pi.single i (x i)) (σ i) = Θ x (σ i) := by
    intro x i
    rw [← mul_single_one, map_mul, hσ, Pi.mul_apply, Pi.single_eq_same, mul_one]
  let θ' : ∀ i, L i →+* P (σ i) := fun i =>
    { toFun := fun a => Θ (Pi.single i a) (σ i)
      map_one' := by rw [hσ, Pi.single_eq_same]
      map_mul' := fun a b => by rw [← Pi.mul_apply, ← map_mul, ← Pi.single_mul]
      map_zero' := by simp
      map_add' := fun a b => by rw [← Pi.add_apply, ← map_add, ← Pi.single_add] }
  have hθbij : ∀ i, Function.Bijective (θ' i) := by
    intro i
    refine ⟨(injective_iff_map_eq_zero (θ' i)).2 fun a ha => ?_, fun b => ?_⟩
    · have h0 : Θ (Pi.single i a) = 0 := by
        rw [hcarry]
        exact Pi.single_eq_zero_iff.2 ha
      simpa using congrFun (Θ.injective (h0.trans (map_zero Θ).symm)) i
    · refine ⟨Θ.symm (Pi.single (σ i) b) i, ?_⟩
      change Θ (Pi.single i _) (σ i) = b
      rw [hkey, RingEquiv.apply_symm_apply, Pi.single_eq_same]
  exact ⟨Equiv.ofBijective σ hbij, fun i => RingEquiv.ofBijective (θ' i) (hθbij i), hkey⟩

end PiLocal

/-! ### The normalization of `R` -/

/-- A nonzerodivisor of `R` stays a nonzerodivisor in its normalization. -/
private theorem algebraMap_mem_nonZeroDivisors_normalization
    (R : Type*) [CommRing R] (Q B : Type*) [CommRing Q] [Algebra R Q]
    [IsLocalization (nonZeroDivisors R) Q]
    [CommRing B] [Algebra R B] [Algebra B Q] [IsScalarTower R B Q] [IsIntegralClosure B R Q]
    {f : R} (hf : f ∈ nonZeroDivisors R) : algebraMap R B f ∈ nonZeroDivisors B := by
  refine mem_nonZeroDivisors_of_injective (IsIntegralClosure.algebraMap_injective B R Q) ?_
  rw [← IsScalarTower.algebraMap_apply]
  exact (IsLocalization.map_units Q ⟨f, hf⟩).mem_nonZeroDivisors

/-- The normalization of `R` is a normal ring. -/
private theorem isNormalRing_normalization
    (R : Type*) [CommRing R] [IsReduced R] [IsNoetherianRing R] (Q B : Type*) [CommRing Q]
    [Algebra R Q] [IsLocalization (nonZeroDivisors R) Q]
    [CommRing B] [Algebra R B] [Algebra B Q] [IsScalarTower R B Q] [IsIntegralClosure B R Q] :
    IsNormalRing B := by
  obtain ⟨eB⟩ := nonempty_integralClosure_fractionRing_algEquiv R Q B
  exact IsNormalRing.congr eB.toRingEquiv
    (isNormalRing_integralClosure_fractionRing_of_finite_minimalPrimes
      (minimalPrimes.finite_of_isNoetherianRing R))

/-- The localization of the normalization at a prime above the maximal ideal of a reduced
one-dimensional Nagata local ring is a discrete valuation ring. -/
private theorem isDiscreteValuationRing_localization_normalization
    (R : Type*) [CommRing R] [IsLocalRing R] [IsReduced R] (hN : IsNagataRing R)
    (hdim : ringKrullDim R = 1)
    (Q B : Type*) [CommRing Q] [Algebra R Q] [IsLocalization (nonZeroDivisors R) Q]
    [CommRing B] [Algebra R B] [Algebra B Q] [IsScalarTower R B Q] [IsIntegralClosure B R Q]
    [Module.Finite R B] (q : Ideal B) [q.IsPrime] (hq : q ∈ (maximalIdeal R).primesOver B) :
    ∃ _ : IsDomain (Localization.AtPrime q), IsDiscreteValuationRing (Localization.AtPrime q) := by
  have : IsNoetherianRing R := hN.1
  have : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  obtain ⟨f, hfm, hLA, -⟩ :=
    exists_common_fractionRing_localization_and_injective_tensorProduct.{_, 0} hN hdim
  have hf : f ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_injective (IsFractionRing.injective R (FractionRing R))
      (IsLocalization.map_units (FractionRing R) ⟨f, Submonoid.mem_powers f⟩).mem_nonZeroDivisors
  have hinj : Function.Injective (algebraMap R B) := .of_comp (f := algebraMap B Q) (by
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact IsLocalization.injective Q le_rfl)
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hinj
  have hdimB : ringKrullDim B = 1 := by
    rw [← Algebra.IsIntegral.ringKrullDim_eq R B, hdim]
  have hqOver : q.comap (algebraMap R B) = maximalIdeal R := by
    simpa [Ideal.under_def] using hq.2.over.symm
  have hqf : algebraMap R B f ∈ q := by
    rwa [← Ideal.mem_comap, hqOver]
  have hqheight : q.height = 1 := by
    have hge : 1 ≤ q.height :=
      (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
        (algebraMap_mem_nonZeroDivisors_normalization R Q B hf)).trans
        (Ideal.height_mono ((Ideal.span_singleton_le_iff_mem _).mpr hqf))
    have hle : q.height ≤ 1 := by
      have hh := Ideal.height_le_ringKrullDim_of_isPrime (I := q)
      rw [hdimB] at hh
      exact_mod_cast hh
    simpa using le_antisymm hle hge
  have hdimL : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
    exact_mod_cast hqheight
  obtain ⟨hdomQ, hclosedQ⟩ := isNormalRing_normalization R Q B q
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ ‹IsNoetherianRing B›
  have hitem : IsNoetherianRing (Localization.AtPrime q) ∧ IsLocalRing (Localization.AtPrime q) ∧
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) ∧
      ringKrullDim (Localization.AtPrime q) = 1 :=
    ⟨inferInstance, inferInstance, hdomQ, hclosedQ, hdimL⟩
  exact (isDiscreteValuationRing_tfae (Localization.AtPrime q)).out 5 1 |>.mp hitem

/-! ### The completed normalization of a split node -/

/-- A ring isomorphism carries the integral closure of a ring in its total ring of fractions to
that of the target. -/
private theorem map_integralClosure_fractionRing_ringEquivOfRingEquiv {A N : Type*} [CommRing A]
    [CommRing N] (ε : A ≃+* N) :
    (integralClosure A (FractionRing A)).toSubring.map
        (IsFractionRing.ringEquivOfRingEquiv ε : FractionRing A ≃+* FractionRing N).toRingHom =
      (integralClosure N (FractionRing N)).toSubring := by
  set Φ : FractionRing A ≃+* FractionRing N := IsFractionRing.ringEquivOfRingEquiv ε
  have hΦ : ∀ y : A, Φ (algebraMap A _ y) = algebraMap N _ (ε y) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap ε
  ext x
  simp only [Subring.mem_map, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact IsIntegral.map_of_comp_eq ε.toRingHom Φ.toRingHom
      (RingHom.ext fun y => (hΦ y).symm) hy
  · intro hx
    refine ⟨Φ.symm x, IsIntegral.map_of_comp_eq ε.symm.toRingHom Φ.symm.toRingHom
      (RingHom.ext fun n => Φ.injective ?_) hx, Φ.apply_symm_apply x⟩
    change Φ (algebraMap A _ (ε.symm n)) = Φ (Φ.symm (algebraMap N _ n))
    rw [hΦ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-- The completion of the normalization `B'` of a reduced Nagata local ring of dimension at
most one is the integral closure of the completion in its total ring of fractions, transported
along any ring isomorphism `ε` out of the completion. -/
private theorem exists_ringEquiv_adicCompletion_integralClosure (R : Type*) [CommRing R]
    [IsLocalRing R] [IsReduced R] (hN : IsNagataRing R) (hdim : ringKrullDim R ≤ 1)
    {N : Type*} [CommRing N] (ε : AdicCompletion (maximalIdeal R) R ≃+* N) :
    ∃ Ψ : AdicCompletion ((maximalIdeal R).map (algebraMap R (integralClosure R (FractionRing R))))
        (integralClosure R (FractionRing R)) ≃+* integralClosure N (FractionRing N),
      ∀ r : R, Ψ (algebraMap (integralClosure R (FractionRing R)) _
          (algebraMap R (integralClosure R (FractionRing R)) r)) =
        algebraMap N _ (ε (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) := by
  have : IsNoetherianRing R := hN.1
  let Rh := AdicCompletion (maximalIdeal R) R
  let B' := integralClosure R (FractionRing R)
  have : Module.Finite R B' := module_finite_integralClosure_fractionRing hN
  -- Tag 0C1R
  obtain ⟨qF, hqF, g, hg, hgr, -, hgB⟩ :=
    IsLocalRing.exists_injective_range_eq_integralClosure_adicCompletion_fractionRing
      (A := R) (B := B') hN hdim (integralClosure R (FractionRing R)).val
      Subtype.val_injective (Subalgebra.range_val _)
  let Φ : FractionRing Rh ≃+* FractionRing N := IsFractionRing.ringEquivOfRingEquiv ε
  have hΦ : ∀ y : Rh, Φ (algebraMap Rh _ y) = algebraMap N _ (ε y) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap ε
  have hmap := map_integralClosure_fractionRing_ringEquivOfRingEquiv ε
  let Ψ₀ : AdicCompletion ((maximalIdeal R).map (algebraMap R B')) B' ≃+*
      integralClosure N (FractionRing N) :=
    ((RingEquiv.ofBijective g.rangeRestrict
      ⟨fun a b h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩).trans
        (RingEquiv.subringCongr hgr)).trans (Φ.subringMap.trans (RingEquiv.subringCongr hmap))
  have hΨ₀ : ∀ c, (Ψ₀ c : FractionRing N) = Φ (g c) := fun c => rfl
  refine ⟨Ψ₀, fun r => Subtype.ext ?_⟩
  rw [hΨ₀, hgB]
  change Φ (qF (algebraMap R (FractionRing R) r)) = _
  rw [hqF, hΦ]
  rfl

/-- The completion of the normalization of a split node, as the product of the completed local
rings of the normalization above the maximal ideal, is `K[[t]] × K[[t]]`, the map from `R` being
restriction to the two branches. -/
private theorem exists_ringEquiv_pi_adicCompletion
    (k : Type*) [Field k] (R : Type*) [CommRing R] [IsLocalRing R] [IsReduced R]
    [Algebra k R] [Algebra.EssFiniteType k R] (hdim : ringKrullDim R = 1)
    (e : AdicCompletion (maximalIdeal R) R ≃+*
      MvPowerSeries (Fin 2) (ResidueField R) ⧸
        Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 :
          MvPowerSeries (Fin 2) (ResidueField R))})
    (Q B : Type*) [CommRing Q] [Algebra R Q] [IsLocalization (nonZeroDivisors R) Q]
    [CommRing B] [Algebra R B] [Algebra B Q] [IsScalarTower R B Q] [IsIntegralClosure B R Q]
    [Module.Finite R B] :
    ∃ Θ : (∀ q : (maximalIdeal R).primesOver B,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)) ≃+*
        (Fin 2 → PowerSeries (ResidueField R)),
      ∀ (r : R) (f : MvPowerSeries (Fin 2) (ResidueField R)),
        Ideal.Quotient.mk _ f = e (algebraMap R (AdicCompletion (maximalIdeal R) R) r) →
          Θ (fun q => algebraMap (Localization.AtPrime q.1) _
              (algebraMap B (Localization.AtPrime q.1) (algebraMap R B r))) 0 =
            MvPowerSeries.subst ![PowerSeries.X, 0] f ∧
          Θ (fun q => algebraMap (Localization.AtPrime q.1) _
              (algebraMap B (Localization.AtPrime q.1) (algebraMap R B r))) 1 =
            MvPowerSeries.subst ![0, PowerSeries.X] f := by
  classical
  have hN : IsNagataRing R := isNagataRing_of_essFiniteType k R
  have : IsNoetherianRing R := hN.1
  let K := ResidueField R
  let Rh := AdicCompletion (maximalIdeal R) R
  let N := Stacks.Curves.multicross K 2
  let ε : Rh ≃+* N := e.trans (Stacks.Curves.quotientAlgEquivMulticross (k := K)).toRingEquiv
  let B' := integralClosure R (FractionRing R)
  have : Module.Finite R B' := module_finite_integralClosure_fractionRing hN
  obtain ⟨eB⟩ := nonempty_integralClosure_fractionRing_algEquiv R Q B
  obtain ⟨Ψ₀, hΨ⟩ := exists_ringEquiv_adicCompletion_integralClosure R hN hdim.le ε
  -- Tag 07N9
  have : IsLocalization.AtPrime R (maximalIdeal R) :=
    IsLocalization.of_le_isUnit fun a ha => (notMem_maximalIdeal (R := R)).mp ha
  obtain ⟨E⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver (R := R) (S := B)
    (maximalIdeal R) R (fun q => Localization.AtPrime q.1)
  let T : TensorProduct R B Rh ≃ₐ[R] AdicCompletion ((maximalIdeal R).map (algebraMap R B')) B' :=
    (Algebra.TensorProduct.congr eB.symm AlgEquiv.refl).trans
      ((Algebra.TensorProduct.comm R B' Rh).trans (ofTensorProductAlgEquiv (maximalIdeal R) B'))
  let Θ := E.symm.toRingEquiv.trans (T.toRingEquiv.trans
    (Ψ₀.trans (Stacks.Curves.integralClosureMulticrossAlgEquiv K).toRingEquiv))
  refine ⟨Θ, fun r f hf => ?_⟩
  have hx : (fun q : (maximalIdeal R).primesOver B => algebraMap (Localization.AtPrime q.1)
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1))
        (algebraMap B (Localization.AtPrime q.1) (algebraMap R B r))) =
      algebraMap B _ (algebraMap R B r) := by
    funext q
    rw [Pi.algebraMap_apply]
    exact (IsScalarTower.algebraMap_apply B (Localization.AtPrime q.1) _ _).symm
  have hT : T (E.symm (algebraMap B _ (algebraMap R B r))) =
      algebraMap B' _ (algebraMap R B' r) := by
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hε : ε (algebraMap R Rh r) = Stacks.Curves.multicrossBranchHom f := by
    change Stacks.Curves.quotientAlgEquivMulticross (e (algebraMap R Rh r)) = _
    rw [← hf]
    rfl
  have hval : Θ (fun q => algebraMap (Localization.AtPrime q.1) _
        (algebraMap B (Localization.AtPrime q.1) (algebraMap R B r))) =
      Stacks.Curves.branchHom f := by
    rw [hx]
    change Stacks.Curves.integralClosureMulticrossAlgEquiv K
      (Ψ₀ (T (E.symm (algebraMap B _ (algebraMap R B r))))) = _
    rw [hT, hΨ, AlgEquiv.commutes, hε]
    rfl
  rw [hval, Stacks.Curves.branchHom_apply, Stacks.Curves.branchHom_apply]
  refine ⟨congrArg (MvPowerSeries.subst · f) ?_, congrArg (MvPowerSeries.subst · f) ?_⟩ <;>
    funext j <;> fin_cases j <;> simp [Stacks.Curves.branchSubst]

/-- **Normalization at a split formal node.** Let `R` be a reduced one-dimensional local ring
essentially of finite type over a field `k`, with `R̂ ≃ K[[u, v]]/(uv)`, `K` the residue field,
and let `B` be the integral closure of `R` in its total ring of fractions `Q`. Then `B` is finite
over `R` and has exactly two primes `𝔪₁ ≠ 𝔪₂` over the maximal ideal of `R`, both maximal; the
localizations `B_{𝔪ᵢ}` are discrete valuation rings; and there are isomorphisms
`B̂_{𝔪₁} ≃ K[[t]]`, `B̂_{𝔪₂} ≃ K[[t]]` under which `R → B̂_{𝔪₁}` is `R → R̂ ≃ K[[u, v]]/(uv)`
followed by `u ↦ t, v ↦ 0`, and `R → B̂_{𝔪₂}` is the same followed by `u ↦ 0, v ↦ t`. -/
@[mmp "lem_mmp_split_node_normalization_completions"]
public theorem exists_adicCompletion_localization_ringEquiv_powerSeries_of_splitNode
    (k : Type*) [Field k] (R : Type*) [CommRing R] [IsLocalRing R] [IsReduced R]
    [Algebra k R] [Algebra.EssFiniteType k R] (hdim : ringKrullDim R = 1)
    (e : AdicCompletion (maximalIdeal R) R ≃+*
      MvPowerSeries (Fin 2) (ResidueField R) ⧸
        Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 :
          MvPowerSeries (Fin 2) (ResidueField R))})
    (Q B : Type*) [CommRing Q] [Algebra R Q] [IsLocalization (nonZeroDivisors R) Q]
    [CommRing B] [Algebra R B] [Algebra B Q] [IsScalarTower R B Q] [IsIntegralClosure B R Q] :
    Module.Finite R B ∧
      ∃ (m₁ m₂ : Ideal B) (_ : m₁.IsMaximal) (_ : m₂.IsMaximal),
        m₁ ≠ m₂ ∧ (maximalIdeal R).primesOver B = {m₁, m₂} ∧
        (∃ _ : IsDomain (Localization.AtPrime m₁),
          IsDiscreteValuationRing (Localization.AtPrime m₁)) ∧
        (∃ _ : IsDomain (Localization.AtPrime m₂),
          IsDiscreteValuationRing (Localization.AtPrime m₂)) ∧
        ∃ (φ₁ : AdicCompletion (maximalIdeal (Localization.AtPrime m₁))
              (Localization.AtPrime m₁) ≃+* PowerSeries (ResidueField R))
          (φ₂ : AdicCompletion (maximalIdeal (Localization.AtPrime m₂))
              (Localization.AtPrime m₂) ≃+* PowerSeries (ResidueField R)),
          ∀ (r : R) (f : MvPowerSeries (Fin 2) (ResidueField R)),
            Ideal.Quotient.mk _ f = e (algebraMap R (AdicCompletion (maximalIdeal R) R) r) →
              φ₁ (algebraMap (Localization.AtPrime m₁) _
                  (algebraMap B (Localization.AtPrime m₁) (algebraMap R B r))) =
                MvPowerSeries.subst ![PowerSeries.X, 0] f ∧
              φ₂ (algebraMap (Localization.AtPrime m₂) _
                  (algebraMap B (Localization.AtPrime m₂) (algebraMap R B r))) =
                MvPowerSeries.subst ![0, PowerSeries.X] f := by
  have hN : IsNagataRing R := isNagataRing_of_essFiniteType k R
  have : IsNoetherianRing R := hN.1
  have := module_finite_integralClosure_fractionRing hN
  obtain ⟨eB⟩ := nonempty_integralClosure_fractionRing_algEquiv R Q B
  have : Module.Finite R B := Module.Finite.equiv eB.toLinearEquiv
  have : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  obtain ⟨Θ, hΘ⟩ := exists_ringEquiv_pi_adicCompletion k R hdim e Q B
  obtain ⟨σ, θ, hθ⟩ := exists_equiv_ringEquiv_of_ringEquiv_pi Θ
  have hmax : ∀ q : (maximalIdeal R).primesOver B, q.1.IsMaximal := fun q =>
    haveI := q.2.2
    Ideal.IsMaximal.of_liesOver_isMaximal q.1 (maximalIdeal R)
  refine ⟨‹Module.Finite R B›, (σ.symm 0).1, (σ.symm 1).1, hmax _, hmax _, fun h => ?_, ?_,
    isDiscreteValuationRing_localization_normalization R hN hdim Q B _ (σ.symm 0).2,
    isDiscreteValuationRing_localization_normalization R hN hdim Q B _ (σ.symm 1).2,
    θ (σ.symm 0), θ (σ.symm 1), fun r f hf => ?_⟩
  · exact zero_ne_one (σ.symm.injective (Subtype.ext h))
  · ext I
    refine ⟨fun hI => ?_, fun hI => ?_⟩
    · have hσI : σ ⟨I, hI⟩ = 0 ∨ σ ⟨I, hI⟩ = 1 := by
        rcases Fin.exists_fin_two.mp ⟨σ ⟨I, hI⟩, rfl⟩ with h | h <;> simp [h]
      rcases hσI with h | h
      · left
        rw [← h, Equiv.symm_apply_apply]
      · right
        rw [Set.mem_singleton_iff, ← h, Equiv.symm_apply_apply]
    · rcases hI with rfl | rfl <;> exact (σ.symm _).2
  · obtain ⟨h0, h1⟩ := hΘ r f hf
    have hθ' := hθ (fun q => algebraMap (Localization.AtPrime q.1) _
      (algebraMap B (Localization.AtPrime q.1) (algebraMap R B r)))
    exact ⟨(hθ' (σ.symm 0)).trans (by rw [Equiv.apply_symm_apply, h0]),
      (hθ' (σ.symm 1)).trans (by rw [Equiv.apply_symm_apply, h1])⟩

end MMP

end
