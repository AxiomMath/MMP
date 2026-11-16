module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.CanonicalDualizingSheaf
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.Group
public import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueRegular
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Cohomology.Duality.AdjunctionSequence
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
public import MMP.AlgebraicGeometry.Divisor.PullbackExistence

/-!
# The residue different of an adjunction step

Let `M` be a normal variety of dimension `n + 1` over a field `k` of characteristic zero, `B` a
`ℚ`-divisor on `M` and `j : S ⟶ M` a normal prime component of the reduced boundary of `B`, with
`(S, B_S)` an adjunction step of `(M, B)` (`MMP.Fourfold.IsAdjunctionStep`): `B_S` is the residue
different of Kollár [SMMP, Def. 4.2], defined by `(div τ₀ + B)|_S = div(Res_S τ₀) + B_S` for one
nonzero rational top form `τ₀` with a simple pole along `S`. Then the same holds for every such
form: if `τ` has a simple pole along `S`, `ρ = Res_S τ` is its Poincaré residue and `div τ + B` is
`ℚ`-Cartier, the restriction of `div τ + B` to `S` is `div ρ + B_S`. In particular `B_S` is
determined by `(M, B)` and `j`.

Where the different `Diff_S(B - S)` of FA 16.5, 16.6 is defined, through the embedded dualizing
sheaf and the restriction `i^w` of Weil divisorial subsheaves, it is the residue different.

## Main definitions

* `MMP.Fourfold.HasOrderAt`: a subsheaf `𝓕 ⊆ K(X)` has order `a` along a prime divisor `Γ`,
  `𝓕_Γ = t_Γ^a 𝒪_{X,Γ}`.
* `MMP.Fourfold.QHasOrderAt`: the order of a class in `WSh(X)_ℚ` along `Γ`.

## Main results

* `MMP.Fourfold.exists_notMem_range_mul_mem_range`: for a prime `p` minimal over `ϖ ≠ 0` in a
  Noetherian domain `A`, some `g ∉ A` of the fraction field has `g p ⊆ A`.
* `MMP.Fourfold.PrimeDivisor.ordGE_iff_le_ord`, `MMP.Fourfold.HasOrderAt.ordGE_germ`: the order of
  a section of a subsheaf of order `a` along `Γ` is at least `a`.
* `MMP.Fourfold.QWeilDivisorialSheaf.IsSum.add_eq_of_qHasOrderAt`: orders are additive along
  sums in `WSh(X)_ℚ`.
* `MMP.Fourfold.WeilDivisor.hasOrderAt_sheaf`: `𝒪(D)` has order `-n_Γ` along `Γ`.
* `MMP.Fourfold.WeilDivisorialSubsheaf.exists_hasOrderAt`: on an integral Noetherian scheme every
  Weil divisorial subsheaf has an order along every prime divisor.
* `MMP.Fourfold.germ_restrictAlong_eq_mul`: restriction `f ↦ f|_S` is multiplicative on germs.
* `MMP.Fourfold.stalkSet_weilRestrictionCartier`: if `𝓕_{j(P)} = f 𝒪_{X,j(P)}` for a section `f`
  of `𝓕` regular along `S`, then `(i^w_C 𝓕)_P = (f|_S)_P 𝒪_{S,P}` at a point `P` of codimension
  `≤ 1`; `MMP.Fourfold.hasOrderAt_weilRestrictionCartier` gives its order along a prime divisor.
* `MMP.Fourfold.stalkSet_restrictionImage_subset`,
  `MMP.Fourfold.germ_restrictAlong_mul_mem_stalkSet_restrictionImage`: the stalk of the image
  `ε(i^*𝓛)` is spanned over `𝒪_{S,P}` by the germs `(l|_S)_P`.
* `MMP.Fourfold.isRegularAlong_of_mem_reflexivePowNat`: sections of `𝓛^[n+1]`, `𝓛 ∈ WSh_S(X)`,
  are regular along `S`.
* `MMP.Fourfold.DifferentHypotheses.coeff_eq_neg_one`: an embedding `ω = 𝒪(K)` of the dualizing
  sheaf satisfying `(⋆)` has `coeff_S K = -1`.
* `MMP.Fourfold.Divisor.exists_isDivisorialSection_of_forall_mem_support`,
  `MMP.Fourfold.Divisor.ord_eq_neg_coeff_of_stalkSet_eq`: a rational function satisfying the order
  bounds of `𝒪_X(D)` at the primes through `x` is a section near `x`, and a generator `f` of
  `𝒪_X(D)_x` has `v_E(f) = -d_E` along every prime through `x`.
* `MMP.Fourfold.Divisor.reflexivePowNat_sheaf_toWeilDivisor`: `𝒪_X(D)^[n+1] = 𝒪_X((n+1)D)`.
* `MMP.Fourfold.IsPoincareResidue.exists_unit_smul`: changing the form by a unit along `S`.
* `MMP.Fourfold.hasOrderAt_embeddedDualizingSheaf`: `Ω_S` has order `-ord_Q Res_S τ₀` along `Q`
  when `ω = 𝒪_X(div τ₀)`.
* `MMP.Fourfold.exists_isUnit_hasOrderAt_weilRestrictionCartier`: the order of `i^w_C(𝓛^[n+1])`
  along `Q` is that of the restriction of a generator at `j(η_Q)`.
* `MMP.Fourfold.exists_coeff_eq_of_isDifferentDivisor`: the coefficients of the different
  `Diff_S((B - S)⁺)`.
* `MMP.Fourfold.isAdjunctionStep_of_isDifferentDivisor`: the different of FA 16.6 is the residue
  different.
* `MMP.Fourfold.IsAdjunctionStep.coeff_eq_one`: the component `S` has coefficient one in `B`.
* `MMP.Fourfold.IsAdjunctionStep.isPullback_divisorOfForm_add_of_isPoincareResidue`: the residue
  different restricts `div τ + B` to `div(Res_S τ) + B_S` for every form `τ` with a simple pole
  along `S`.
* `MMP.Fourfold.IsAdjunctionStep.unique`: the residue different is well defined.

## Implementation notes

The witness `ω ⊆ K(M)` of the dualizing sheaf entering `MMP.Flips.IsDifferentDivisor` is
`𝒪_M(div τ₀)` for a nonzero rational top form `τ₀`
(`MMP.Flips.IsDualizingSheaf.exists_eq_sheaf_toWeilDivisor`). The comparison with FA 16.6
computes the embedded dualizing sheaf `Ω_S` as `𝒪_S(div Res_S τ₀)` from the surjectivity and
effectivity of residues at the codimension-one points of `S`, the restriction `i^w` of a Weil
divisorial subsheaf which is invertible in codimension one along `S` as the pull-back of divisors,
and then passes from `τ₀` to `τ` through `Res_S(f τ₀) = f|_S Res_S τ₀`. For a subboundary `B`,
writing `B - S = Δ⁺ - Δ⁻` with `Δ⁺, Δ⁻ ≥ 0` and `Δ⁻` `ℚ`-Cartier, the computation is made for the
effective part `Δ⁺`, and the restriction of `Δ⁻` is then subtracted using the additivity of the
pull-back of `ℚ`-Cartier divisors.

The independence of the residue different from the form: another form is `τ = b τ₀` for a unit
`b` of `𝒪_{M,S}`, with `Res_S τ = b̄ Res_S τ₀`; `div τ + B = (div τ₀ + B) + div b`, and the
pull-back of the principal divisor `div b` along `j` is `div b̄`
(`MMP.Mori.Divisor.isPullback_principalDivisor`).

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Definition 4.2
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.5, 16.6
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Elements with a simple pole along a height-one prime -/

/-- A prime `p` minimal over an ideal `I` of a Noetherian ring is associated to `A/I`: there is
`b ∉ I` with `p b ⊆ I`. -/
theorem exists_notMem_mul_mem_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A]
    {I p : Ideal A} (hp : p ∈ I.minimalPrimes) :
    ∃ b ∉ I, ∀ y ∈ p, y * b ∈ I := by
  have h := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    (R := A) (M := A ⧸ I)
  rw [Ideal.annihilator_quotient] at h
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp (h hp)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have key : ∀ y, y ∈ p ↔ y * b ∈ I := by
    intro y
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem,
      map_mul, Algebra.smul_def]
    rfl
  exact ⟨b, fun hb => hpp.ne_top ((Ideal.eq_top_iff_one _).mpr ((key 1).mpr (by simpa using hb))),
    fun y hy => (key y).mp hy⟩

/-- **An element of `p⁻¹ ∖ A`.** If `p` is minimal among the primes of the Noetherian domain `A`
containing `ϖ ≠ 0`, there is `g` in the fraction field with `g ∉ A` and `g p ⊆ A`; in particular
`g` lies in `A_q` for every prime `q ⊉ p`. -/
theorem exists_notMem_range_mul_mem_range {A K : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] {p : Ideal A} [p.IsPrime]
    {ϖ : A} (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ p)
    (hp : ∀ q : Ideal A, q.IsPrime → ϖ ∈ q → q ≤ p → q = p) :
    ∃ g : K, g ∉ Set.range (algebraMap A K) ∧
      ∀ y ∈ p, g * algebraMap A K y ∈ Set.range (algebraMap A K) := by
  have hmin : p ∈ (Ideal.span {ϖ}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hϖ⟩, fun q hq hqp => ?_⟩
    exact (hp q hq.1 ((Ideal.span_singleton_le_iff_mem _).mp hq.2) hqp).ge
  obtain ⟨b, hb, hyb⟩ := exists_notMem_mul_mem_of_mem_minimalPrimes hmin
  have hϖK : algebraMap A K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hϖ0
  refine ⟨algebraMap A K b / algebraMap A K ϖ, ?_, fun y hy => ?_⟩
  · rintro ⟨a, ha⟩
    apply hb
    rw [eq_div_iff hϖK, ← map_mul] at ha
    rw [← IsFractionRing.injective A K ha]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self ϖ)
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hyb y hy)
    refine ⟨c, ?_⟩
    rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hϖK, ← map_mul, ← map_mul, hc, mul_comm]

/-! ### Orders of subsheaves of `K(X)` along a prime divisor -/

section Order

open MMP.Flips MMP.Flips.RationalFunctionsSubmodule

universe u

variable {X : Scheme.{u}}

/-- The `ℤ`-submodule `c · 𝒪_{X,x}` of `K(X)_x`, for `c ∈ K(X)_x`. -/
def principalStalk (x : X) (c : (rationalFunctionsPresheaf X).stalk x) :
    Submodule ℤ ((rationalFunctionsPresheaf X).stalk x) where
  carrier := Set.range fun a : X.presheaf.stalk x =>
    c * (structureStalkToRationalFunctionsStalk X x).hom a
  zero_mem' := ⟨0, by dsimp only; rw [map_zero, mul_zero]⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by dsimp only; rw [map_add, mul_add]⟩
  smul_mem' := by
    rintro n _ ⟨a, rfl⟩
    exact ⟨n • a, by dsimp only; rw [map_zsmul, mul_smul_comm]⟩

/-- `𝓕` is generated at `x` by `c` exactly when its stalk at `x` is `c · 𝒪_{X,x}`. -/
theorem isGeneratedAt_iff_stalk_eq {F : RationalFunctionsSubmodule X} {x : X}
    {c : ((rationalFunctionsPresheaf X).stalk x)ˣ} :
    F.IsGeneratedAt x c ↔ F.stalk x = principalStalk x c :=
  ⟨(SetLike.coe_injective ·), congrArg SetLike.coe⟩

/-- `c 𝒪_{X,x} · d 𝒪_{X,x} = cd 𝒪_{X,x}`. -/
theorem principalStalk_mul (x : X) (c d : (rationalFunctionsPresheaf X).stalk x) :
    principalStalk x c * principalStalk x d = principalStalk x (c * d) := by
  refine le_antisymm (Submodule.mul_le.mpr ?_) fun g hg => ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨a * b, by dsimp only; rw [map_mul]; ring⟩
  · obtain ⟨a, rfl⟩ := hg
    have := Submodule.mul_mem_mul (show c * (structureStalkToRationalFunctionsStalk X x).hom a ∈
      principalStalk x c from ⟨a, rfl⟩) (show d * (structureStalkToRationalFunctionsStalk X x).hom 1
        ∈ principalStalk x d from ⟨1, rfl⟩)
    convert this using 1
    rw [map_one]
    ring

/-- `(c 𝒪_{X,x})^(n+1) = c^(n+1) 𝒪_{X,x}`. -/
theorem principalStalk_pow (x : X) (c : (rationalFunctionsPresheaf X).stalk x) (n : ℕ) :
    principalStalk x c ^ (n + 1) = principalStalk x (c ^ (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, principalStalk_mul, ← pow_succ]

variable [IsReduced X] [IsNoetherian X]

/-- `𝓕` has order `a` along the prime divisor `Γ`: `𝓕_Γ = t^a 𝒪_{X,Γ}` for the uniformizer `t`
of `𝒪_{X,Γ}`. The sheaf `𝒪_X(D)` has order `-n_Γ`. -/
def HasOrderAt (F : RationalFunctionsSubmodule X) (Γ : WeilDivisorPrime X) (a : ℤ) : Prop :=
  F.IsGeneratedAt Γ.1.genericPoint (Γ.uniformizerUnit ^ a)

/-- The generic point of a prime divisor has coheight at most `1`. -/
theorem coheight_genericPoint_le_one_of_weilDivisorPrime (Γ : WeilDivisorPrime X) :
    Order.coheight Γ.1.genericPoint ≤ 1 :=
  (MMP.Mori.PrimeDivisor.coheight_genericPoint Γ.1).le

/-- If `𝓕` has order `a` along `Γ`, then `𝓕_Γ = t^a 𝒪_{X,Γ}`. -/
theorem HasOrderAt.stalk_eq {F : RationalFunctionsSubmodule X} {Γ : WeilDivisorPrime X} {a : ℤ}
    (h : HasOrderAt F Γ a) :
    F.stalk Γ.1.genericPoint = principalStalk _ (Γ.uniformizerUnit ^ a).val :=
  isGeneratedAt_iff_stalk_eq.mp h

/-- `𝓕` has order `a` along `Γ` if and only if `𝓕_Γ = t^a 𝒪_{X,Γ}`. -/
theorem hasOrderAt_iff_stalk_eq {F : RationalFunctionsSubmodule X} {Γ : WeilDivisorPrime X}
    {a : ℤ} : HasOrderAt F Γ a ↔
      F.stalk Γ.1.genericPoint = principalStalk _ (Γ.uniformizerUnit ^ a).val :=
  isGeneratedAt_iff_stalk_eq

/-- Orders add under products: if `𝓕` has order `a` and `𝓖` order `b` along `Γ`, then `𝓕 · 𝓖`
has order `a + b`. -/
theorem HasOrderAt.mul {F G : RationalFunctionsSubmodule X} {Γ : WeilDivisorPrime X} {a b : ℤ}
    (hF : HasOrderAt F Γ a) (hG : HasOrderAt G Γ b) : HasOrderAt (F.mul G) Γ (a + b) := by
  rw [hasOrderAt_iff_stalk_eq]
  change (mulImage F G).saturation.stalk _ = _
  rw [stalk_saturation _ (coheight_genericPoint_le_one_of_weilDivisorPrime Γ), stalk_mulImage,
    hF.stalk_eq, hG.stalk_eq, principalStalk_mul, zpow_add, Units.val_mul]

/-- If `𝓕` has order `a` along `Γ`, then `𝓕^[n+1]` has order `(n + 1) a`. -/
theorem HasOrderAt.reflexivePowNat_succ {F : RationalFunctionsSubmodule X} {Γ : WeilDivisorPrime X}
    {a : ℤ} (h : HasOrderAt F Γ a) (n : ℕ) :
    HasOrderAt (F.reflexivePowNat (n + 1)) Γ ((n + 1 : ℕ) * a) := by
  rw [hasOrderAt_iff_stalk_eq,
    stalk_reflexivePowNat_succ _ (coheight_genericPoint_le_one_of_weilDivisorPrime Γ), h.stalk_eq,
    principalStalk_pow, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm]

/-- If `𝓕` has order `a` along `Γ` and `n > 0`, then `𝓕^[n]` has order `n a`. -/
theorem HasOrderAt.reflexivePowNat_of_pos {F : RationalFunctionsSubmodule X}
    {Γ : WeilDivisorPrime X} {a : ℤ} (h : HasOrderAt F Γ a) {n : ℕ} (hn : 0 < n) :
    HasOrderAt (F.reflexivePowNat n) Γ (n * a) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  simpa using h.reflexivePowNat_succ n

private theorem not_exists_eq_uniformizerUnit_zpow_neg [CompactSpace X]
    (Γ : WeilDivisorPrime X) {k : ℕ} (hk : 0 < k) :
    ¬ ∃ w : X.presheaf.stalk Γ.1.genericPoint,
      (structureStalkToRationalFunctionsStalk X _).hom w =
        ((Γ.uniformizerUnit ^ (-(k : ℤ)) : (_)ˣ) : (rationalFunctionsPresheaf X).stalk _) := by
  rintro ⟨w, hw⟩
  have ht : Γ.uniformizerUnit.val =
      (structureStalkToRationalFunctionsStalk X _).hom Γ.uniformizer :=
    Γ.isUnit_uniformizer.unit_spec
  have h1 : (structureStalkToRationalFunctionsStalk X _).hom (w * Γ.uniformizer ^ k) =
      (structureStalkToRationalFunctionsStalk X _).hom 1 := by
    rw [map_mul, map_pow, hw, ← ht, map_one, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      ← zpow_natCast, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  have h2 := wshC_structure_stalk_injective _ h1
  have hu : IsUnit (Γ.uniformizer ^ k) :=
    ⟨⟨_, w, by rw [mul_comm]; exact h2, h2⟩, rfl⟩
  exact Γ.irreducible_uniformizer.not_isUnit ((isUnit_pow_iff hk.ne').mp hu)

/-- The order of `𝓕` along `Γ` is unique. -/
theorem HasOrderAt.unique [CompactSpace X] {F : RationalFunctionsSubmodule X}
    {Γ : WeilDivisorPrime X} {a b : ℤ} (ha : HasOrderAt F Γ a) (hb : HasOrderAt F Γ b) :
    a = b := by
  have key : ∀ a b : ℤ, HasOrderAt F Γ a → HasOrderAt F Γ b → a ≤ b := by
    intro a b ha hb
    by_contra hlt
    push Not at hlt
    have hmem : (Γ.uniformizerUnit ^ b).val ∈
        principalStalk _ (Γ.uniformizerUnit ^ a).val := by
      rw [← ha.stalk_eq, hb.stalk_eq]
      exact ⟨1, by dsimp only; rw [map_one, mul_one]⟩
    obtain ⟨w, hw⟩ := hmem
    dsimp only at hw
    refine not_exists_eq_uniformizerUnit_zpow_neg Γ (k := (a - b).toNat) (by omega) ⟨w, ?_⟩
    have hk : (((a - b).toNat : ℕ) : ℤ) = a - b := Int.toNat_of_nonneg (by omega)
    rw [hk, show -(a - b) = -a + b by ring, zpow_add, Units.val_mul, ← hw, ← mul_assoc,
      ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]
  exact le_antisymm (key a b ha hb) (key b a hb ha)

/-- A class `c ∈ WSh(X)_ℚ` has order `r ∈ ℚ` along `Γ`: `c = (1/n)𝓛` with `𝓛` of order `a`
along `Γ` and `r = a / n`. -/
def QHasOrderAt (c : QWeilDivisorialSheaf X) (Γ : WeilDivisorPrime X) (r : ℚ) : Prop :=
  ∃ (L : WeilDivisorialSubsheaf X) (n : ℕ+) (a : ℤ), c = L.divNat n ∧
    HasOrderAt L.toRationalFunctionsSubmodule Γ a ∧ r = a / n

/-- If `𝓛` has order `a` along `Γ`, then `(1/n)𝓛` has order `a / n`. -/
theorem HasOrderAt.qHasOrderAt_divNat {L : WeilDivisorialSubsheaf X} {Γ : WeilDivisorPrime X}
    {a : ℤ} (h : HasOrderAt L.toRationalFunctionsSubmodule Γ a) (n : ℕ+) :
    QHasOrderAt (L.divNat n) Γ (a / n) :=
  ⟨L, n, a, rfl, h, rfl⟩

/-- Representatives of the same class have proportional orders. -/
theorem HasOrderAt.div_eq_div_of_divNat_eq [CompactSpace X] {L L' : WeilDivisorialSubsheaf X}
    {n n' : ℕ+} (hc : L.divNat n = L'.divNat n') {Γ : WeilDivisorPrime X} {a a' : ℤ}
    (ha : HasOrderAt L.toRationalFunctionsSubmodule Γ a)
    (ha' : HasOrderAt L'.toRationalFunctionsSubmodule Γ a') :
    (a : ℚ) / n = a' / n' := by
  obtain ⟨m, hm, h⟩ := WeilDivisorialSubsheaf.divNat_eq_divNat_iff.mp hc
  simp only [RationalFunctionsSubmodule.reflexivePow_natCast] at h
  have h1 := ha.reflexivePowNat_of_pos (n := m * n') (by positivity)
  have h2 := ha'.reflexivePowNat_of_pos (n := m * n) (by positivity)
  rw [h] at h1
  have := h1.unique h2
  have hn : (n : ℚ) ≠ 0 := by positivity
  have hn' : (n' : ℚ) ≠ 0 := by positivity
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [div_eq_div_iff hn hn']
  have := congrArg (fun z : ℤ => (z : ℚ)) this
  push_cast at this
  apply mul_left_cancel₀ hm'
  linear_combination this

/-- The order of a class of `WSh(X)_ℚ` along `Γ` is unique. -/
theorem QHasOrderAt.unique [CompactSpace X] {c : QWeilDivisorialSheaf X}
    {Γ : WeilDivisorPrime X} {r r' : ℚ} (h : QHasOrderAt c Γ r) (h' : QHasOrderAt c Γ r') :
    r = r' := by
  obtain ⟨L, n, a, rfl, ha, rfl⟩ := h
  obtain ⟨L', n', a', hc, ha', rfl⟩ := h'
  exact HasOrderAt.div_eq_div_of_divNat_eq hc ha ha'

/-- On a scheme all of whose Weil divisorial subsheaves have an order along `Γ`, every class of
`WSh(X)_ℚ` has one. -/
theorem QWeilDivisorialSheaf.exists_qHasOrderAt {Γ : WeilDivisorPrime X}
    (hΓ : ∀ L : WeilDivisorialSubsheaf X, ∃ a, HasOrderAt L.toRationalFunctionsSubmodule Γ a)
    (c : QWeilDivisorialSheaf X) : ∃ r, QHasOrderAt c Γ r := by
  induction c using Quotient.inductionOn with
  | h p =>
    obtain ⟨a, ha⟩ := hΓ p.1
    exact ⟨_, ha.qHasOrderAt_divNat p.2⟩

/-- **Orders are additive along `IsSum`.** -/
theorem QWeilDivisorialSheaf.IsSum.add_eq_of_qHasOrderAt [CompactSpace X]
    {c₁ c₂ c₃ : QWeilDivisorialSheaf X}
    (h : QWeilDivisorialSheaf.IsSum c₁ c₂ c₃) {Γ : WeilDivisorPrime X}
    (hΓ : ∀ L : WeilDivisorialSubsheaf X, ∃ a, HasOrderAt L.toRationalFunctionsSubmodule Γ a)
    {r₁ r₂ r₃ : ℚ} (h₁ : QHasOrderAt c₁ Γ r₁) (h₂ : QHasOrderAt c₂ Γ r₂)
    (h₃ : QHasOrderAt c₃ Γ r₃) : r₁ + r₂ = r₃ := by
  obtain ⟨L₁, L₂, L₃, n₁, n₂, n₃, rfl, rfl, rfl, m, hm, hsum⟩ := h
  obtain ⟨a₁, ha₁⟩ := hΓ L₁
  obtain ⟨a₂, ha₂⟩ := hΓ L₂
  obtain ⟨a₃, ha₃⟩ := hΓ L₃
  rw [h₁.unique (ha₁.qHasOrderAt_divNat n₁), h₂.unique (ha₂.qHasOrderAt_divNat n₂),
    h₃.unique (ha₃.qHasOrderAt_divNat n₃)]
  simp only [RationalFunctionsSubmodule.reflexivePow_natCast] at hsum
  have e₁ := ((ha₁.reflexivePowNat_of_pos n₂.pos).mul
    (ha₂.reflexivePowNat_of_pos n₁.pos)).reflexivePowNat_of_pos (n := m * n₃) (by positivity)
  have e₂ := ha₃.reflexivePowNat_of_pos (n := m * (n₁ * n₂)) (by positivity)
  rw [hsum] at e₁
  have := congrArg (fun z : ℤ => (z : ℚ)) (e₁.unique e₂)
  push_cast at this
  have hn₁ : (n₁ : ℚ) ≠ 0 := by positivity
  have hn₂ : (n₂ : ℚ) ≠ 0 := by positivity
  have hn₃ : (n₃ : ℚ) ≠ 0 := by positivity
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp
  apply mul_left_cancel₀ hm'
  linear_combination this

/-- **The order of `𝒪(D)` along `Γ` is `-n_Γ`** (FA 16.2.2): on a reduced pure-dimensional
scheme of finite type over a field, `𝒪(D)_Γ = t_Γ^{-n_Γ} 𝒪_{X,Γ}`. -/
theorem WeilDivisor.hasOrderAt_sheaf {k : Type u} [Field k] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) (D : MMP.Flips.WeilDivisor X)
    (Γ : WeilDivisorPrime X) : HasOrderAt D.sheaf Γ (-D Γ) := by
  obtain ⟨L, hL, hgen⟩ := exists_weilDivisorialSubsheaf_sheaf_isGeneratedAt π hd D
  exact hL ▸ hgen Γ

omit [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsNoetherian X] in
/-- On an integral scheme every germ of `K(X)` at `x` is a fraction `a / b` of germs of
`𝒪_{X,x}` with `b ≠ 0`. -/
theorem exists_mul_structureStalkToRationalFunctionsStalk_eq [IsIntegral X] {x : X}
    (f : (rationalFunctionsPresheaf X).stalk x) :
    ∃ a b : X.presheaf.stalk x, b ≠ 0 ∧
      f * (structureStalkToRationalFunctionsStalk X x).hom b =
        (structureStalkToRationalFunctionsStalk X x).hom a := by
  obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (rationalFunctionsPresheaf X) f
  have hirr : irreducibleComponents X = {Set.univ} := irreducibleComponents_eq_singleton
  let Z₀ : irreducibleComponents X := ⟨Set.univ, by rw [hirr]; rfl⟩
  have hsub : ∀ Z : irreducibleComponents X, Z = Z₀ := fun Z =>
    Subtype.ext (Set.mem_singleton_iff.mp (hirr ▸ Z.2))
  have hZV : componentGenericPoint X Z₀ ∈ V :=
    (genericPoint_mem_iff Z₀ V).mpr ⟨x, hV, Set.mem_univ x⟩
  have hsp : componentGenericPoint X Z₀ ⤳ x :=
    (isGenericPoint_componentGenericPoint X Z₀).specializes (Set.mem_univ x)
  letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (componentGenericPoint X Z₀)) :=
    (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have hloc := Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hsp
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk (componentGenericPoint X Z₀))).under
      (X.presheaf.stalk x)).primeCompl (s ⟨Z₀, hZV⟩)
  have hb : (b : X.presheaf.stalk x) ≠ 0 := fun h0 => b.2 (by rw [h0]; exact zero_mem _)
  refine ⟨a, b, hb, ?_⟩
  obtain ⟨Wa, hWa, aa', rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  obtain ⟨Wb, hWb, bb', hbb'⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf (b : X.presheaf.stalk x)
  let U : X.Opens := V ⊓ Wa ⊓ Wb
  have hU : x ∈ U := ⟨⟨hV, hWa⟩, hWb⟩
  let iV : U ⟶ V := homOfLE (inf_le_left.trans inf_le_left)
  let iA : U ⟶ Wa := homOfLE (inf_le_left.trans inf_le_right)
  let iB : U ⟶ Wb := homOfLE inf_le_right
  have hφ : ∀ (W : X.Opens) (hW : x ∈ W) (c : Γ(X, W)),
      (structureStalkToRationalFunctionsStalk X x).hom (X.presheaf.germ W x hW c) =
        (rationalFunctionsPresheaf X).germ W x hW
          ((toRationalFunctionsPresheaf X).app (Opposite.op W) c) :=
    fun W hW c => TopCat.Presheaf.stalkFunctor_map_germ_apply W x hW _ c
  rw [← hbb', hφ, hφ, ← TopCat.Presheaf.germ_res_apply _ iV x hU,
    ← TopCat.Presheaf.germ_res_apply _ iA x hU, ← TopCat.Presheaf.germ_res_apply _ iB x hU,
    ← map_mul]
  congr 1
  funext Z
  obtain ⟨Z, hZU⟩ := Z
  obtain rfl := hsub Z
  change s ⟨Z₀, _⟩ * X.presheaf.germ Wb _ _ bb' = X.presheaf.germ Wa _ _ aa'
  have e₁ : X.presheaf.germ Wb _ (iB.le hZU) bb' = algebraMap _ _ (b : X.presheaf.stalk x) := by
    rw [← hbb']
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hWb hsp bb').symm
  have e₂ : X.presheaf.germ Wa _ (iA.le hZU) aa' = algebraMap _ _ (X.presheaf.germ Wa x hWa aa') :=
    (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hWa hsp aa').symm
  rw [e₁, e₂, ← hab, IsLocalization.mk'_spec]

/-- **Every Weil divisorial subsheaf has an order along each prime divisor.** -/
theorem WeilDivisorialSubsheaf.exists_hasOrderAt [IsIntegral X] (L : WeilDivisorialSubsheaf X)
    (Γ : WeilDivisorPrime X) : ∃ a, HasOrderAt L.toRationalFunctionsSubmodule Γ a := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  set η := Γ.1.genericPoint
  set φ := (structureStalkToRationalFunctionsStalk X η).hom
  obtain ⟨f, hf⟩ := L.principal_codim_one η (coheight_genericPoint_le_one_of_weilDivisorPrime Γ)
  obtain ⟨a, b, hb, hab⟩ := exists_mul_structureStalkToRationalFunctionsStalk_eq f.val
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact hb (wshC_structure_stalk_injective η (by
      rw [map_zero]; exact (Units.isUnit f).mul_right_eq_zero.mp hab))
  obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha
    Γ.irreducible_uniformizer
  obtain ⟨k, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb
    Γ.irreducible_uniformizer
  refine ⟨(i : ℤ) - k, ?_⟩
  have ht : Γ.uniformizerUnit.val = φ Γ.uniformizer := Γ.isUnit_uniformizer.unit_spec
  -- `f = t^(i - k) φ(u w⁻¹)`
  have hfe : (f : (rationalFunctionsPresheaf X).stalk η) =
      (Γ.uniformizerUnit ^ ((i : ℤ) - k)).val * φ ((u * w⁻¹ : (X.presheaf.stalk η)ˣ) : _) := by
    have hw : φ (w : X.presheaf.stalk η) * φ ((w⁻¹ : (X.presheaf.stalk η)ˣ) : _) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have htk : (Γ.uniformizerUnit ^ (k : ℤ)).val * (Γ.uniformizerUnit ^ (-(k : ℤ))).val = 1 := by
      rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
    rw [map_mul, map_mul, map_pow, map_pow, ← ht, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_natCast] at hab
    calc (f : (rationalFunctionsPresheaf X).stalk η)
        = f * (φ w * (Γ.uniformizerUnit ^ (k : ℤ)).val) *
            (φ ((w⁻¹ : (X.presheaf.stalk η)ˣ) : _) * (Γ.uniformizerUnit ^ (-(k : ℤ))).val) := by
          rw [show ∀ p q r s' : (rationalFunctionsPresheaf X).stalk η,
            f * (p * q) * (r * s') = f * (p * r) * (q * s') from fun _ _ _ _ => by ring, hw, htk]
          ring
      _ = φ u * (Γ.uniformizerUnit ^ (i : ℤ)).val *
            (φ ((w⁻¹ : (X.presheaf.stalk η)ˣ) : _) * (Γ.uniformizerUnit ^ (-(k : ℤ))).val) := by
          rw [hab]
      _ = _ := by
          rw [sub_eq_add_neg, zpow_add, Units.val_mul, Units.val_mul, map_mul]
          ring
  change L.stalkSet η = _
  rw [hf]
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨((u * w⁻¹ : (X.presheaf.stalk η)ˣ) : _) * c, ?_⟩
    dsimp only
    rw [hfe, map_mul]
    ring
  · rintro ⟨c, rfl⟩
    refine ⟨((u * w⁻¹ : (X.presheaf.stalk η)ˣ)⁻¹ : (X.presheaf.stalk η)ˣ) * c, ?_⟩
    dsimp only
    rw [hfe, map_mul, mul_assoc, ← mul_assoc (φ _), ← map_mul, Units.mul_inv, map_one, one_mul]

end Order

/-! ### The simple pole of the canonical form along `S` -/

section SimplePole

open MMP.Flips MMP.Flips.RationalFunctionsSubmodule

universe u

/-- A prime divisor of a locally Noetherian normal scheme, as a prime divisor of FA 16.2.1. -/
def PrimeDivisor.toWeilDivisorPrime {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (P : Mori.PrimeDivisor X) : WeilDivisorPrime X :=
  ⟨P, inferInstance, P.isDiscreteValuationRing_localRing⟩

/-- **The embedding `ω = 𝒪(K)` has a simple pole along `S`.** Under the hypotheses `(⋆)`
of FA 16.6 (`MMP.Flips.DifferentHypotheses`) for `S = P`, if the dualizing sheaf is embedded as
`ω = 𝒪_X(K)`, then `coeff_P K = -1`. -/
theorem DifferentHypotheses.coeff_eq_neg_one {k : Type u} [Field k] {X S : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [IsNormal X] {j : S ⟶ X} [IsClosedImmersion j]
    {π : X ⟶ Spec (.of k)} {d : ℕ} {ω ωXS : WeilDivisorialSubsheaf X} {DS : MMP.Flips.WeilDivisor X}
    {B : QWeilDivisor X} (hH : DifferentHypotheses j π d ω ωXS DS B)
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    {K : Mori.Divisor X} (hω : ω.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor K).sheaf) :
    K.coeff P = -1 := by
  classical
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have : LocallyOfFiniteType π := hH.isNormalVariety.1.toLocallyOfFiniteType
  have hd := hH.isDualizingSheaf.1
  set Γ : WeilDivisorPrime X := PrimeDivisor.toWeilDivisorPrime P
  -- a component of `S` maps to the generic point of `P`
  have : Nonempty S := by
    obtain ⟨y, hy⟩ : (P.support : Set X).Nonempty :=
      ⟨P.genericPoint, primeDivisor_genericPoint_mem_support P⟩
    rw [← hP] at hy
    obtain ⟨z, -⟩ := hy
    exact ⟨z⟩
  obtain ⟨Z, -⟩ := exists_mem_irreducibleComponents (Classical.arbitrary S)
  obtain ⟨Γ', hΓ'⟩ := hH.exists_weilDivisorPrime ⟨_, Z.2⟩
  have hΓ'P : Γ'.1 = P := by
    refine eq_of_genericPoint_mem_primeDivisor_support ?_
    rw [hΓ']
    change _ ∈ (P.support : Set X)
    rw [← hP]
    exact ⟨_, rfl⟩
  have hgen : Γ.1.genericPoint = j.base (componentGenericPoint S ⟨_, Z.2⟩) := by
    rw [← hΓ', hΓ'P]; rfl
  -- the orders of `ω`, `𝒪(S)` and `ω_X(S)` along `P`
  have h₁ : HasOrderAt ω.toRationalFunctionsSubmodule Γ (-K.coeff P) := by
    rw [hω]
    have := WeilDivisor.hasOrderAt_sheaf π hd (Divisor.toWeilDivisor K) Γ
    rwa [Divisor.toWeilDivisor_apply] at this
  have hDS : DS Γ = 1 := by
    rw [hH.coeff_divisor Γ, if_pos ⟨_, hgen⟩]
  have h₂ : HasOrderAt DS.sheaf Γ (-1) := by
    have := WeilDivisor.hasOrderAt_sheaf π hd DS Γ
    rwa [hDS] at this
  have h₃ : HasOrderAt ωXS.toRationalFunctionsSubmodule Γ (-K.coeff P + -1) := by
    rw [hH.twist_eq]
    exact h₁.mul h₂
  have h₀ : HasOrderAt ωXS.toRationalFunctionsSubmodule Γ 0 := by
    have hsupp := hH.mem_goodSupportSubsheaves.2 _
      (maximal_closure_image_genericPoint j ⟨_, Z.2⟩)
    simp only [WeilDivisorialSubsheaf.support, Set.mem_ofPred_eq, not_not] at hsupp
    rw [← hgen] at hsupp
    change ωXS.stalkSet Γ.1.genericPoint = _
    rw [hsupp, stalkSet_saturation (coheight_genericPoint_le_one_of_weilDivisorPrime Γ),
      stalkSet_unit]
    simp
  have := h₃.unique h₀
  omega

end SimplePole

/-! ### Restriction of rational functions regular along `S` -/

section Restriction

open MMP.Flips MMP.Flips.RationalFunctionsSubmodule Opposite TopologicalSpace

universe u

variable {X S : Scheme.{u}} (j : S ⟶ X)

/-- The value of `f|_S` at the generic point of a component of `S` is the image of any preimage
in `𝒪_{X,ξ}` of the germ of `f`. -/
theorem restrictAlong_apply_of_germ_eq [IsReduced X] [IsLocallyNoetherian X] [CompactSpace X]
    {V : X.Opens} {f : ToType ((rationalFunctionsPresheaf X).obj (op V))}
    (hf : IsRegularAlong j f)
    (Z : {Z : irreducibleComponents S // componentGenericPoint S Z ∈ j ⁻¹ᵁ V})
    (c : X.presheaf.stalk (j.base (componentGenericPoint S Z.1)))
    (hc : (structureStalkToRationalFunctionsStalk X _).hom c =
      (rationalFunctionsPresheaf X).germ V _ Z.2 f) :
    restrictAlong j f hf Z = (j.stalkMap _).hom c := by
  unfold restrictAlong
  rw [wshC_structure_stalk_injective _ ((Classical.choose_spec (hf Z.1 Z.2)).trans hc.symm)]

/-- **Restriction is multiplicative on germs.** If `f_x = f₁_x · b` at `x = j(P)` with
`b ∈ 𝒪_{X,x}`, then `(f|_S)_P = (f₁|_S)_P · b|_S`. -/
theorem germ_restrictAlong_eq_mul [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [IsIntegral S] {W W₁ : X.Opens} {f : ToType ((rationalFunctionsPresheaf X).obj (op W))}
    {f₁ : ToType ((rationalFunctionsPresheaf X).obj (op W₁))}
    (hf : IsRegularAlong j f) (hf₁ : IsRegularAlong j f₁) {P : S} (hP : j.base P ∈ W)
    (hP₁ : j.base P ∈ W₁) (b : X.presheaf.stalk (j.base P))
    (hb : (rationalFunctionsPresheaf X).germ W _ hP f =
      (rationalFunctionsPresheaf X).germ W₁ _ hP₁ f₁ *
        (structureStalkToRationalFunctionsStalk X _).hom b) :
    (rationalFunctionsPresheaf S).germ (j ⁻¹ᵁ W) P hP (restrictAlong j f hf) =
      (rationalFunctionsPresheaf S).germ (j ⁻¹ᵁ W₁) P hP₁ (restrictAlong j f₁ hf₁) *
        (structureStalkToRationalFunctionsStalk S P).hom ((j.stalkMap P).hom b) := by
  let ZS : irreducibleComponents S :=
    ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩
  let ZX : irreducibleComponents X :=
    ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩
  apply rationalFunctionsStalkEval_injective P ZS
  rw [map_mul, rationalFunctionsStalkEval_germ P ZS (U := j ⁻¹ᵁ W) hP,
    rationalFunctionsStalkEval_germ P ZS (U := j ⁻¹ᵁ W₁) hP₁,
    rationalFunctionsStalkEval_structure]
  have hS : componentGenericPoint S ZS ∈ j ⁻¹ᵁ W :=
    componentGenericPoint_mem_of_nonempty ZS ⟨P, hP⟩
  have hS₁ : componentGenericPoint S ZS ∈ j ⁻¹ᵁ W₁ :=
    componentGenericPoint_mem_of_nonempty ZS ⟨P, hP₁⟩
  obtain ⟨c, hc⟩ := hf ZS hS
  obtain ⟨c₁, hc₁⟩ := hf₁ ZS hS₁
  rw [restrictAlong_apply_of_germ_eq j hf ⟨ZS, hS⟩ c hc,
    restrictAlong_apply_of_germ_eq j hf₁ ⟨ZS, hS₁⟩ c₁ hc₁]
  have hsp : componentGenericPoint S ZS ⤳ P := componentGenericPoint_specializes ZS P
  have hsp' : j.base (componentGenericPoint S ZS) ⤳ j.base P := j.base.hom.map_specializes hsp
  have key : c = c₁ * (X.presheaf.stalkSpecializes hsp').hom b := by
    apply wshC_structure_stalk_injective
    apply rationalFunctionsStalkEval_injective _ ZX
    rw [map_mul, map_mul, hc, hc₁, rationalFunctionsStalkEval_germ _ ZX (U := W) hS,
      rationalFunctionsStalkEval_germ _ ZX (U := W₁) hS₁, rationalFunctionsStalkEval_structure]
    have h2 := congrArg (rationalFunctionsStalkEval (j.base P) ZX).hom hb
    rw [map_mul, rationalFunctionsStalkEval_germ, rationalFunctionsStalkEval_germ,
      rationalFunctionsStalkEval_structure] at h2
    rw [h2, ← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
  rw [key, map_mul, Scheme.Hom.stalkSpecializes_stalkMap_apply]

/-- The germs `(f|_S)_P · a`, for a section `f` of `𝓕` regular along `S` and `a ∈ 𝒪_{S,P}`, lie
in the stalk of `i^w_C 𝓕`. -/
theorem germ_restrictAlong_mul_mem_stalkSet [IsIntegral X] [IsLocallyNoetherian X]
    [CompactSpace X] [IsIntegral S] {F : RationalFunctionsSubmodule X} {W : X.Opens}
    {f : ToType ((rationalFunctionsPresheaf X).obj (op W))} (hfF : f ∈ F.sections W)
    (hf : IsRegularAlong j f) {P : S} (hP : j.base P ∈ W) (a : S.presheaf.stalk P) :
    (rationalFunctionsPresheaf S).germ (j ⁻¹ᵁ W) P hP (restrictAlong j f hf) *
        (structureStalkToRationalFunctionsStalk S P).hom a ∈
      (weilRestrictionCartier j F).stalkSet P := by
  obtain ⟨V, hPV, a', rfl⟩ := S.presheaf.exists_germ_eq a
  let V' : S.Opens := V ⊓ j ⁻¹ᵁ W
  have hPV' : P ∈ V' := ⟨hPV, hP⟩
  let iV : V' ⟶ V := homOfLE inf_le_left
  let iW : V' ⟶ j ⁻¹ᵁ W := homOfLE inf_le_right
  refine ⟨V', hPV', S.presheaf.map iV.op a' •
    (rationalFunctionsPresheaf S).map iW.op (restrictAlong j f hf), ?_, ?_⟩
  · intro P' hP' hc f₁ hf₁ W₁ hP₁ f₁' hf₁' hgerm
    have hmem : (rationalFunctionsPresheaf X).germ W _ hP'.2 f ∈ F.stalkSet (j.base P') :=
      ⟨W, hP'.2, f, hfF, rfl⟩
    rw [hf₁] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨(j.stalkMap P').hom b * S.presheaf.germ V' P' hP' (S.presheaf.map iV.op a'), ?_⟩
    rw [germ_smul_rationalFunctions, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply,
      germ_restrictAlong_eq_mul j hf hf₁' hP'.2 hP₁ b (by rw [hgerm]; exact hb.symm), map_mul]
    ring
  · rw [germ_smul_rationalFunctions, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply]
    ring

/-- The germs `(l|_S)_P · a`, for a section `l` of `𝓛` regular along `S` and `a ∈ 𝒪_{S,P}`, lie in
the stalk of the image `ε(i^*𝓛)`. -/
theorem germ_restrictAlong_mul_mem_stalkSet_restrictionImage {L : RationalFunctionsSubmodule X}
    {W : X.Opens} {l : ToType ((rationalFunctionsPresheaf X).obj (op W))} (hlL : l ∈ L.sections W)
    (hl : IsRegularAlong j l) {P : S} (hP : j.base P ∈ W) (a : S.presheaf.stalk P) :
    (rationalFunctionsPresheaf S).germ (j ⁻¹ᵁ W) P hP (restrictAlong j l hl) *
        (structureStalkToRationalFunctionsStalk S P).hom a ∈
      (restrictionImage j L).stalkSet P := by
  obtain ⟨V, hPV, a', rfl⟩ := S.presheaf.exists_germ_eq a
  let V' : S.Opens := V ⊓ j ⁻¹ᵁ W
  have hPV' : P ∈ V' := ⟨hPV, hP⟩
  let iV : V' ⟶ V := homOfLE inf_le_left
  let iW : V' ⟶ j ⁻¹ᵁ W := homOfLE inf_le_right
  refine ⟨V', hPV', S.presheaf.map iV.op a' •
    (rationalFunctionsPresheaf S).map iW.op (restrictAlong j l hl), ?_, ?_⟩
  · exact mem_localClosure_of_mem (Submodule.smul_mem _ _
      (Submodule.subset_span ⟨W, inf_le_right, l, hlL, hl, rfl⟩))
  · rw [germ_smul_rationalFunctions, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply]
    ring

/-- **Induction on the stalk of `ε(i^*𝓛)`.** A subset of `K(S)_P` containing `0` and the germs
`(l|_S)_P` of restrictions of sections of `𝓛` regular along `S`, and closed under sums and
multiplication by `𝒪_{S,P}`, contains the stalk of `ε(i^*𝓛)` at `P`. -/
theorem stalkSet_restrictionImage_subset {L : RationalFunctionsSubmodule X} {P : S}
    {T : Set ((rationalFunctionsPresheaf S).stalk P)} (h0 : 0 ∈ T)
    (hadd : ∀ g h, g ∈ T → h ∈ T → g + h ∈ T)
    (hmul : ∀ (a : S.presheaf.stalk P) g, g ∈ T →
      (structureStalkToRationalFunctionsStalk S P).hom a * g ∈ T)
    (hgen : ∀ (W : X.Opens) (hP : j.base P ∈ W)
      (l : ToType ((rationalFunctionsPresheaf X).obj (op W))), l ∈ L.sections W →
      ∀ hl : IsRegularAlong j l,
        (rationalFunctionsPresheaf S).germ (j ⁻¹ᵁ W) P hP (restrictAlong j l hl) ∈ T) :
    (restrictionImage j L).stalkSet P ⊆ T := by
  rintro _ ⟨V, hV, s, hs, rfl⟩
  obtain ⟨W', i, hPW', hmem⟩ := hs P hV
  rw [← TopCat.Presheaf.germ_res_apply _ i P hPW']
  generalize (rationalFunctionsPresheaf S).map i.op s = t at hmem ⊢
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨W, h, l, hlL, hl, rfl⟩ := hx
    rw [TopCat.Presheaf.germ_res_apply]
    exact hgen W (h hPW') l hlL hl
  | zero => rw [map_zero]; exact h0
  | add x y _ _ hx hy => rw [map_add]; exact hadd _ _ hx hy
  | smul r x _ hx => rw [germ_smul_rationalFunctions]; exact hmul _ _ hx

/-- **The stalk of `i^w_C 𝓕` at a point of codimension `≤ 1`.** If `𝓕_x = f · 𝒪_{X,x}` at
`x = j(P)` for a section `f` of `𝓕` regular along `S`, then `(i^w_C 𝓕)_P = (f|_S)_P · 𝒪_{S,P}`. -/
theorem stalkSet_weilRestrictionCartier [IsIntegral X] [IsLocallyNoetherian X]
    [CompactSpace X] [IsIntegral S] {F : RationalFunctionsSubmodule X} {W : X.Opens}
    {f : ToType ((rationalFunctionsPresheaf X).obj (op W))} (hfF : f ∈ F.sections W)
    (hf : IsRegularAlong j f) {P : S} (hP : j.base P ∈ W) (hc : Order.coheight P ≤ 1)
    (f₀ : ((rationalFunctionsPresheaf X).stalk (j.base P))ˣ)
    (hf₀ : (f₀ : (rationalFunctionsPresheaf X).stalk (j.base P)) =
      (rationalFunctionsPresheaf X).germ W _ hP f)
    (hgen : F.stalkSet (j.base P) = Set.range fun a : X.presheaf.stalk (j.base P) =>
      (f₀ : (rationalFunctionsPresheaf X).stalk (j.base P)) *
        (structureStalkToRationalFunctionsStalk X (j.base P)).hom a) :
    (weilRestrictionCartier j F).stalkSet P = Set.range fun a : S.presheaf.stalk P =>
      (rationalFunctionsPresheaf S).germ (j ⁻¹ᵁ W) P hP (restrictAlong j f hf) *
        (structureStalkToRationalFunctionsStalk S P).hom a := by
  ext g
  constructor
  · rintro ⟨V, hV, s, hs, rfl⟩
    obtain ⟨a, ha⟩ := hs P hV hc f₀ hgen W hP f hf hf₀.symm
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, rfl⟩
    exact germ_restrictAlong_mul_mem_stalkSet j hfF hf hP a

/-- On an integral scheme a germ of `K(X)` with nonzero value is a unit. -/
theorem isUnit_of_rationalFunctionsStalkEval_ne_zero [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {x : X}
    (Z : irreducibleComponents X) {g : (rationalFunctionsPresheaf X).stalk x}
    (hg : (rationalFunctionsStalkEval x Z).hom g ≠ 0) : IsUnit g := by
  obtain ⟨U, hxU, s, rfl⟩ := (rationalFunctionsPresheaf X).exists_germ_eq g
  rw [rationalFunctionsStalkEval_germ] at hg
  have := subsingleton_irreducibleComponents (X := X)
  obtain ⟨φ, hφ⟩ := exists_units_eq_of_ne_zero ⟨x, hxU⟩ s fun Z' => by
    obtain ⟨Z', h'⟩ := Z'
    obtain rfl : Z' = Z := Subsingleton.elim _ _
    exact hg
  let s' : ToType ((rationalFunctionsPresheaf X).obj (op ⊤)) := fun Z' =>
    ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z'.1
  refine IsUnit.of_mul_eq_one ((rationalFunctionsPresheaf X).germ ⊤ x trivial s') ?_
  apply rationalFunctionsStalkEval_injective x Z
  rw [map_mul, rationalFunctionsStalkEval_germ,
    rationalFunctionsStalkEval_germ x Z (U := ⊤) trivial s',
    map_one]
  simp only [s']
  rw [← hφ Z, ← Pi.mul_apply, Units.mul_inv, Pi.one_apply]

/-- **Orders from valuations.** If `𝓕_Γ = g₀ · 𝒪_{X,Γ}` and `v_Γ(g₀) = a`, then `𝓕` has order
`a` along `Γ`. -/
theorem hasOrderAt_of_stalkSet_eq [IsIntegral X] [IsNoetherian X] [IsNormal X]
    {F : RationalFunctionsSubmodule X} {Γ : WeilDivisorPrime X}
    {g₀ : (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint} {a : ℤ}
    (hv : Γ.1.valuation ((rationalFunctionsStalkEval _ Γ.1.component).hom g₀) = WithZero.exp a)
    (hF : F.stalkSet Γ.1.genericPoint = Set.range fun b : X.presheaf.stalk Γ.1.genericPoint =>
      g₀ * (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom b) :
    HasOrderAt F Γ a := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have hu : IsUnit g₀ := isUnit_of_rationalFunctionsStalkEval_ne_zero Γ.1.component (by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.zero_ne_coe hv)
  change F.stalkSet _ = _
  rw [hF]
  ext g
  have h1 := mem_range_unit_mul_iff_ordGE Γ.1 hu.unit (v := a) (by rwa [hu.unit_spec]) g
  rw [hu.unit_spec] at h1
  rw [h1, ← mem_range_uniformizerUnit_zpow_mul_iff_ordGE Γ a g]

/-- **The order of `i^w_C 𝓕` along a prime divisor `Q` of `S`.** If `𝓕` is generated at
`x = j(η_Q)` by a section `f` regular along `S`, and `c ∈ 𝒪_{X,ξ}` is the germ of `f` at the
generic point `ξ` of `S`, then `i^w_C 𝓕` has order `v_Q(c|_S)` along `Q`. -/
theorem hasOrderAt_weilRestrictionCartier [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [IsIntegral S] [IsNoetherian S] [IsNormal S] {F : RationalFunctionsSubmodule X} {W : X.Opens}
    {f : ToType ((rationalFunctionsPresheaf X).obj (op W))} (hfF : f ∈ F.sections W)
    (hf : IsRegularAlong j f) (Q : WeilDivisorPrime S) (hQ : j.base Q.1.genericPoint ∈ W)
    (f₀ : ((rationalFunctionsPresheaf X).stalk (j.base Q.1.genericPoint))ˣ)
    (hf₀ : (f₀ : (rationalFunctionsPresheaf X).stalk (j.base Q.1.genericPoint)) =
      (rationalFunctionsPresheaf X).germ W _ hQ f)
    (hgen : F.stalkSet (j.base Q.1.genericPoint) =
      Set.range fun a : X.presheaf.stalk (j.base Q.1.genericPoint) =>
        (f₀ : (rationalFunctionsPresheaf X).stalk (j.base Q.1.genericPoint)) *
          (structureStalkToRationalFunctionsStalk X (j.base Q.1.genericPoint)).hom a)
    (hW : j.base (componentGenericPoint S Q.1.component) ∈ W)
    (c : X.presheaf.stalk (j.base (componentGenericPoint S Q.1.component)))
    (hc : (structureStalkToRationalFunctionsStalk X _).hom c =
      (rationalFunctionsPresheaf X).germ W _ hW f) {a : ℤ}
    (hv : Q.1.valuation ((j.stalkMap _).hom c) = WithZero.exp a) :
    HasOrderAt (weilRestrictionCartier j F) Q a := by
  refine hasOrderAt_of_stalkSet_eq (g₀ := (rationalFunctionsPresheaf S).germ (j ⁻¹ᵁ W)
    Q.1.genericPoint hQ (restrictAlong j f hf)) ?_ (stalkSet_weilRestrictionCartier j hfF hf hQ
      (coheight_genericPoint_le_one_of_weilDivisorPrime Q) f₀ hf₀ hgen)
  rwa [rationalFunctionsStalkEval_germ _ _ (U := j ⁻¹ᵁ W) hQ,
    restrictAlong_apply_of_germ_eq j hf ⟨Q.1.component, hW⟩ c hc]

/-- **Sections of reflexive powers are regular along `S`.** If `S` has pure codimension one and
`𝓛 ∈ WSh_S(X)`, every section of `𝓛^[n+1]` is regular along `S`: at a generic point `ξ` of `S`,
`𝓛^[n+1]_ξ = (𝓛_ξ)^{n+1} = 𝒪_{X,ξ}`. -/
theorem isRegularAlong_of_mem_reflexivePowNat [IsClosedImmersion j]
    (hS : ∀ Z : irreducibleComponents S, Order.coheight (j.base (componentGenericPoint S Z)) ≤ 1)
    {L : WeilDivisorialSubsheaf X} (hL : L ∈ goodSupportSubsheaves (closedRange j)) (n : ℕ)
    {V : X.Opens} {l : ToType ((rationalFunctionsPresheaf X).obj (op V))}
    (hl : l ∈ (L.toRationalFunctionsSubmodule.reflexivePowNat (n + 1)).sections V) :
    IsRegularAlong j l := by
  intro Z h
  set ξ := j.base (componentGenericPoint S Z)
  let T : Submodule ℤ ((rationalFunctionsPresheaf X).stalk ξ) :=
    (structureStalkToRationalFunctionsStalk X ξ).hom.range.toAddSubgroup.toIntSubmodule
  have hT : ∀ a b, a ∈ T → b ∈ T → a * b ∈ T := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, map_mul _ a b⟩
  have hsupp := hL.2 _ (maximal_closure_image_genericPoint j Z)
  simp only [WeilDivisorialSubsheaf.support, Set.mem_ofPred_eq, not_not] at hsupp
  have h1 : L.toRationalFunctionsSubmodule.stalk ξ ≤ T := by
    intro g hg
    rw [mem_stalk] at hg
    change g ∈ L.stalkSet ξ at hg
    rw [hsupp, ← mem_stalk, stalk_saturation _ (hS Z), mem_stalk] at hg
    exact unit_stalkSet_subset _ hg
  have hpow : ∀ m : ℕ, L.toRationalFunctionsSubmodule.stalk ξ ^ (m + 1) ≤ T := by
    intro m
    induction m with
    | zero => simpa using h1
    | succ m ih =>
      rw [pow_succ]
      exact Submodule.mul_le.mpr fun a ha b hb => hT a b (ih ha) (h1 hb)
  have hmem := germ_mem_stalk _ h hl
  rw [stalk_reflexivePowNat_succ _ (hS Z)] at hmem
  exact hpow n hmem

/-- On an integral normal scheme, for `z ≠ 0` in the function field of the component of `E`,
`v_E(z) ≥ a` is `ord_E z ≥ a` in the function field. -/
theorem PrimeDivisor.ordGE_iff_le_ord [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (E : Mori.PrimeDivisor X) {z : X.presheaf.stalk (componentGenericPoint X E.component)}
    (hz : z ≠ 0) (a : ℤ) :
    E.OrdGE a z ↔
      a ≤ X.ord ((MMP.Positivity.componentToFunctionField E.component).hom z) E.genericPoint := by
  have key : ∀ (y : X) (_ : y = genericPoint X) (w : X.presheaf.stalk y), w ≠ 0 → IsUnit w := by
    rintro y rfl w hw
    exact IsUnit.mk0 (w : X.functionField) hw
  set u := (key _ (componentGenericPoint_eq_genericPoint E.component) z hz).unit
  have hu : (u : X.presheaf.stalk _) = z := IsUnit.unit_spec _
  rw [← hu, ← MMP.CyclicChartDifferent.Aux.ordUnit_eq_ord, Mori.PrimeDivisor.OrdGE,
    PrimeDivisor.valuation_eq_exp_ordUnit, WithZero.exp_le_exp]
  simp [u.ne_zero]

/-- A section of a subsheaf of order `a` along `Γ` has order `≥ a` along `Γ`. -/
theorem HasOrderAt.ordGE_germ [IsIntegral X] [IsNoetherian X] [IsNormal X]
    {F : RationalFunctionsSubmodule X} {Γ : WeilDivisorPrime X} {a : ℤ} (hF : HasOrderAt F Γ a)
    {W : X.Opens} {s : ToType ((rationalFunctionsPresheaf X).obj (op W))}
    (hs : s ∈ F.sections W) (hΓ : Γ.1.genericPoint ∈ W) :
    Γ.1.OrdGE a ((rationalFunctionsStalkEval _ Γ.1.component).hom
      ((rationalFunctionsPresheaf X).germ W _ hΓ s)) := by
  have : CompactSpace X := IsNoetherian.toCompactSpace
  rw [← mem_range_uniformizerUnit_zpow_mul_iff_ordGE]
  have hmem : (rationalFunctionsPresheaf X).germ W _ hΓ s ∈ F.stalkSet Γ.1.genericPoint :=
    ⟨W, hΓ, s, hs, rfl⟩
  rwa [← mem_stalk, hF.stalk_eq] at hmem

end Restriction

/-! ### Generators of divisorial sheaves at a point -/

section Generators

open MMP.Flips Opposite

universe u

/-- **Spreading sections of `𝒪_X(D)`.** If a unit `φ` of `K(X)` satisfies `v_E(φ) ≥ -d_E` along
every prime divisor `E` through `x`, then `φ` is a section of `𝒪_X(D)` on a neighbourhood of `x`:
the complement of the support of the negative part of `D + div φ`. -/
theorem Divisor.exists_isDivisorialSection_of_forall_mem_support {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (D : Divisor X)
    (φ : (RationalFunctions X)ˣ) (x : X)
    (h : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → -D.coeff E ≤ E.ord φ) :
    ∃ W : X.Opens, x ∈ W ∧
      D.IsDivisorialSection W (fun Z => (φ : RationalFunctions X) Z.1) := by
  set F : Divisor X := (D + principalDivisor φ) ⊓ 0
  have hF : ∀ E : Mori.PrimeDivisor X, F.coeff E = min (D.coeff E + E.ord φ) 0 := fun E => by
    rw [← coeff_principalDivisor, ← DivisorWithCoeffs.coeff_add]
    rfl
  refine ⟨⟨(F.supp : Set X)ᶜ, F.isClosed_supp.isOpen_compl⟩, fun hx => ?_, fun E hE => ?_⟩
  · obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    have := h E hxE
    exact hE (by rw [hF]; omega)
  · have h0 : F.coeff E = 0 := by
      by_contra hne
      obtain ⟨y, hyE, hyU⟩ := hE
      exact hyU (DivisorWithCoeffs.support_subset_supp hne hyE)
    rw [hF] at h0
    exact PrimeDivisor.OrdGE.mono (Or.inr (E.valuation_component φ).ge) (by omega)

/-- On an integral scheme every nonzero rational function is the value of a unit of `K(X)`. -/
theorem exists_units_componentToFunctionField_eq {X : Scheme.{u}} [IsIntegral X]
    {g : X.functionField} (hg : g ≠ 0) :
    ∃ χ : (RationalFunctions X)ˣ, ∀ Z,
      (MMP.Positivity.componentToFunctionField Z).hom (χ.val Z) = g := by
  have hmem : ∀ Z : irreducibleComponents X, genericPoint X ∈ Z.1 := fun Z =>
    Z.2.2 (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _) trivial
  let j : ∀ Z : irreducibleComponents X,
      X.functionField →+* X.presheaf.stalk (componentGenericPoint X Z) := fun Z =>
    (X.presheaf.stalkSpecializes
      ((isGenericPoint_componentGenericPoint X Z).specializes (hmem Z))).hom
  refine ⟨Units.map (RingHom.pi j).toMonoidHom (Units.mk0 g hg), fun Z => ?_⟩
  change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom g = g
  rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- A generization `z` of `x` is the point of `Spec 𝒪_{X,x}` given by its prime `𝔪_z ∩ 𝒪_{X,x}`. -/
theorem fromSpecStalk_comap_maximalIdeal_eq {X : Scheme.{u}} {x z : X} (hz : z ⤳ x) :
    X.fromSpecStalk x ⟨(IsLocalRing.maximalIdeal (X.presheaf.stalk z)).comap
      (X.presheaf.stalkSpecializes hz).hom, Ideal.comap_isPrime _ _⟩ = z := by
  have : z ∈ Set.range (X.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hz
  obtain ⟨q, rfl⟩ := this
  have e : (⟨(IsLocalRing.maximalIdeal (X.presheaf.stalk (X.fromSpecStalk x q))).comap
      (X.presheaf.stalkSpecializes hz).hom, Ideal.comap_isPrime _ _⟩ :
        PrimeSpectrum (X.presheaf.stalk x)) = q :=
    PrimeSpectrum.ext (MMP.Intersection.comap_maximalIdeal_stalkSpecializes_fromSpecStalk x q)
  rw [e]

/-- **Generators of `𝒪_X(D)` at a point.** On an integral Noetherian normal scheme, if
`𝒪_X(D)_x = f · 𝒪_{X,x}` for a unit `f` of `K(X)_x`, then `v_E(f) = -d_E` along every prime
divisor `E` through `x`. -/
theorem Divisor.ord_eq_neg_coeff_of_stalkSet_eq {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (D : Divisor X) {x : X}
    (f : ((rationalFunctionsPresheaf X).stalk x)ˣ)
    (hf : (Divisor.toWeilDivisor D).sheaf.stalkSet x = Set.range fun a : X.presheaf.stalk x =>
      (f : (rationalFunctionsPresheaf X).stalk x) *
        (structureStalkToRationalFunctionsStalk X x).hom a)
    (Z : irreducibleComponents X) (E : Mori.PrimeDivisor X) (hxE : x ∈ E.support) :
    X.ord ((MMP.Positivity.componentToFunctionField Z).hom
      ((rationalFunctionsStalkEval x Z).hom f)) E.genericPoint = -D.coeff E := by
  classical
  have hsub := subsingleton_irreducibleComponents (X := X)
  set ev : (rationalFunctionsPresheaf X).stalk x →+* X.functionField :=
    (MMP.Positivity.componentToFunctionField Z).hom.comp (rationalFunctionsStalkEval x Z).hom
    with hev
  have ev_germ : ∀ (W : X.Opens) (hW : x ∈ W)
      (s : ToType ((rationalFunctionsPresheaf X).obj (op W))),
      ev ((rationalFunctionsPresheaf X).germ W x hW s) =
        (MMP.Positivity.componentToFunctionField Z).hom
          (s ⟨Z, componentGenericPoint_mem_of_nonempty Z ⟨x, hW⟩⟩) := fun W hW s => by
    simp only [hev, RingHom.comp_apply, rationalFunctionsStalkEval_germ]
  have ev_structure : ∀ a : X.presheaf.stalk x,
      ev ((structureStalkToRationalFunctionsStalk X x).hom a) =
        algebraMap (X.presheaf.stalk x) X.functionField a := fun a => by
    simp only [hev, RingHom.comp_apply, rationalFunctionsStalkEval_structure]
    exact MMP.CyclicChartDifferent.Aux.componentToFunctionField_stalkSpecializes X Z _ a
  change X.ord (ev f) E.genericPoint = _
  set g := ev f with hgdef
  have hg0 : g ≠ 0 := (f.isUnit.map ev).ne_zero
  have hspec : ∀ E' : Mori.PrimeDivisor X, x ∈ E'.support → E'.genericPoint ⤳ x := by
    intro E' h
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at h
    exact h
  -- `v_E(g) ≥ -D_E` along every prime through `x`
  have hge : ∀ E' : Mori.PrimeDivisor X, x ∈ E'.support →
      -D.coeff E' ≤ X.ord g E'.genericPoint := by
    intro E' hxE'
    have hmem : (f : (rationalFunctionsPresheaf X).stalk x) ∈
        (Divisor.toWeilDivisor D).sheaf.stalkSet x := by
      rw [hf]; exact ⟨1, by simp⟩
    obtain ⟨W, hW, s, hs, hsf⟩ := hmem
    rw [sheaf_toWeilDivisor_sections] at hs
    have h1 := hs E' ⟨x, hxE', hW⟩
    obtain rfl : Z = E'.component := Subsingleton.elim _ _
    have h2 := ev_germ W hW s
    rw [hsf] at h2
    have h3 : g = _ := h2
    rw [h3] at hg0 ⊢
    exact (PrimeDivisor.ordGE_iff_le_ord E' (fun h => hg0 (by rw [h, map_zero])) _).mp h1
  -- elements of `𝒪_{X,x}` have order `≥ 0` along every prime through `x`
  have hA : ∀ E' : Mori.PrimeDivisor X, x ∈ E'.support → ∀ c : X.presheaf.stalk x,
      algebraMap _ X.functionField c ≠ 0 →
        0 ≤ X.ord (algebraMap _ X.functionField c) E'.genericPoint := by
    intro E' hxE' c hc
    have h1 : E'.divisorialValuation (algebraMap _ X.functionField c) ≤ 1 := by
      rw [E'.divisorialValuation_le_one_iff,
        ← MMP.Mori.algebraMap_stalkSpecializes (hspec E' hxE')]
      exact ⟨_, rfl⟩
    rw [E'.divisorialValuation_eq_exp_neg_ord hc, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  refine le_antisymm ?_ (hge E hxE)
  by_contra hlt
  push Not at hlt
  -- the prime `p` of `E` in `A = 𝒪_{X,x}`, with `A_p = 𝒪_{X,E}` a DVR
  have hsp := hspec E hxE
  set p := (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)).comap
    (X.presheaf.stalkSpecializes hsp).hom with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  letI := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  haveI := MMP.Intersection.isLocalization_stalkSpecializes hsp
  haveI := E.isDiscreteValuationRing_localRing
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk E.genericPoint)
  obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.surj p.primeCompl t
  have hsu : IsUnit (algebraMap (X.presheaf.stalk x) (X.presheaf.stalk E.genericPoint) s) :=
    IsLocalization.map_units _ s
  simp only at hys
  have hyK : algebraMap (X.presheaf.stalk x) X.functionField y =
      algebraMap _ X.functionField t *
        algebraMap _ X.functionField
          (algebraMap (X.presheaf.stalk x) (X.presheaf.stalk E.genericPoint) s) := by
    rw [← map_mul, hys]
    exact (MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' X hsp y).symm
  have ht0 : algebraMap (X.presheaf.stalk E.genericPoint) X.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht.ne_zero
  have hyK0 : algebraMap (X.presheaf.stalk x) X.functionField y ≠ 0 := by
    rw [hyK]; exact mul_ne_zero ht0 (hsu.map _).ne_zero
  have hyord : X.ord (algebraMap (X.presheaf.stalk x) X.functionField y) E.genericPoint = 1 := by
    rw [hyK, Scheme.ord_mul ht0 (hsu.map _).ne_zero, E.ord_algebraMap_of_isUnit hsu,
      MMP.Fourfold.ord_algebraMap_eq_one_of_irreducible E.coheight_genericPoint ht]
    rfl
  have hy0 : y ≠ 0 := fun h => hyK0 (by rw [h, map_zero])
  have hyp : y ∈ p := by
    rw [hp, Ideal.mem_comap]
    change algebraMap (X.presheaf.stalk x) (X.presheaf.stalk E.genericPoint) y ∈ _
    rw [← hys]
    exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr ht.not_isUnit)
  have hmin : ∀ q : Ideal (X.presheaf.stalk x), q.IsPrime → y ∈ q → q ≤ p → q = p := by
    intro q hq hyq hqp
    have hdisj : Disjoint (p.primeCompl : Set (X.presheaf.stalk x)) q :=
      Set.disjoint_left.mpr fun _ ha haq => ha (hqp haq)
    have hpr := IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl
      (X.presheaf.stalk E.genericPoint) q hq hdisj
    have hne : q.map (algebraMap (X.presheaf.stalk x) (X.presheaf.stalk E.genericPoint)) ≠ ⊥ := by
      intro h
      have := Ideal.mem_map_of_mem (algebraMap (X.presheaf.stalk x)
        (X.presheaf.stalk E.genericPoint)) hyq
      rw [h, Ideal.mem_bot, ← hys] at this
      exact ht.ne_zero (hsu.mul_left_eq_zero.mp this)
    have hmax := IsLocalRing.eq_maximalIdeal (hpr.isMaximal_of_ne_bot hne)
    rw [← IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl
      (X.presheaf.stalk E.genericPoint) hq hdisj, hmax]
    rfl
  obtain ⟨g₁, hg₁A, hg₁p⟩ := exists_notMem_range_mul_mem_range (K := X.functionField) hy0 hyp hmin
  have hg₁0 : g₁ ≠ 0 := by
    rintro rfl
    exact hg₁A ⟨0, map_zero _⟩
  -- `v_E(g₁) ≥ -1`
  have ha : -1 ≤ X.ord g₁ E.genericPoint := by
    obtain ⟨c, hc⟩ := hg₁p y hyp
    have := hA E hxE c (by rw [hc]; exact mul_ne_zero hg₁0 hyK0)
    rw [hc, Scheme.ord_mul hg₁0 hyK0, hyord] at this
    omega
  -- `v_{E'}(g₁) ≥ 0` along the other primes through `x`
  have hb : ∀ E' : Mori.PrimeDivisor X, x ∈ E'.support → E' ≠ E →
      0 ≤ X.ord g₁ E'.genericPoint := by
    intro E' hxE' hne
    have hsp' := hspec E' hxE'
    obtain ⟨y', hy'p, hy'⟩ : ∃ y' ∈ p, IsUnit ((X.presheaf.stalkSpecializes hsp').hom y') := by
      by_contra hno
      push Not at hno
      have hle : p ≤ (IsLocalRing.maximalIdeal (X.presheaf.stalk E'.genericPoint)).comap
          (X.presheaf.stalkSpecializes hsp').hom := fun a ha =>
        (IsLocalRing.mem_maximalIdeal _).mpr (hno a ha)
      have h1 := ((PrimeSpectrum.le_iff_specializes
        (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))
        ⟨_, Ideal.comap_isPrime _ _⟩).mp hle).map (X.fromSpecStalk x).continuous
      rw [fromSpecStalk_comap_maximalIdeal_eq hsp, fromSpecStalk_comap_maximalIdeal_eq hsp'] at h1
      refine hne (eq_of_genericPoint_mem_primeDivisor_support ?_)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact specializes_iff_mem_closure.mp h1
    obtain ⟨c', hc'⟩ := hg₁p y' hy'p
    have hy'K : algebraMap (X.presheaf.stalk x) X.functionField y' =
        algebraMap _ X.functionField ((X.presheaf.stalkSpecializes hsp').hom y') :=
      (MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' X hsp' y').symm
    have hy'0 : algebraMap (X.presheaf.stalk x) X.functionField y' ≠ 0 := by
      rw [hy'K]; exact (hy'.map _).ne_zero
    have hy'ord :
        X.ord (algebraMap (X.presheaf.stalk x) X.functionField y') E'.genericPoint = 0 := by
      rw [hy'K]; exact E'.ord_algebraMap_of_isUnit hy'
    have := hA E' hxE' c' (by rw [hc']; exact mul_ne_zero hg₁0 hy'0)
    rw [hc', Scheme.ord_mul hg₁0 hy'0, hy'ord] at this
    omega
  -- `g g₁` satisfies the bounds of `𝒪(D)` at `x`, so `g g₁ ∈ g 𝒪_{X,x}`
  obtain ⟨χ, hχ⟩ := exists_units_componentToFunctionField_eq (mul_ne_zero hg0 hg₁0)
  obtain ⟨W, hW, hWs⟩ := Divisor.exists_isDivisorialSection_of_forall_mem_support D χ x
    (fun E' hxE' => by
      rw [MMP.Positivity.ord_eq_ord_componentToFunctionField, hχ, Scheme.ord_mul hg0 hg₁0]
      by_cases hE' : E' = E
      · subst hE'; omega
      · have := hge E' hxE'; have := hb E' hxE' hE'; omega)
  have hmem : (rationalFunctionsPresheaf X).germ W x hW
      (fun Z' => (χ : RationalFunctions X) Z'.1) ∈ (Divisor.toWeilDivisor D).sheaf.stalkSet x :=
    ⟨W, hW, _, by rw [sheaf_toWeilDivisor_sections]; exact hWs, rfl⟩
  rw [hf] at hmem
  obtain ⟨a, ha'⟩ := hmem
  have h3 := congrArg ev ha'
  rw [map_mul, ev_structure] at h3
  erw [ev_germ W hW] at h3
  rw [hχ] at h3
  exact hg₁A ⟨a, mul_left_cancel₀ hg0 h3⟩

end Generators

/-! ### Changing the form -/

section ChangeForm

universe u

/-- **Changing the form.** Two nonzero rational top forms `τ`, `τ₀` with the same order along
`P` differ by a unit `b` of the local ring at the generic point of `T`, `τ = b τ₀`, and if
`ρ = Res_T τ` then `Res_T τ₀ = b̄⁻¹ ρ`
(`MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul`). -/
theorem IsPoincareResidue.exists_unit_smul {k : Type u} [Field k] [PerfectField k]
    {X T : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] [IsIntegral T] {j : T ⟶ X} {n : ℕ}
    (hdim : topologicalKrullDim X = n + 1) (P : Mori.PrimeDivisor X)
    (hjT : j (genericPoint T) = P.genericPoint)
    {τ τ₀ : RationalPluriForms sX (n + 1) 1} (hτ0 : τ ≠ 0) (hτ₀0 : τ₀ ≠ 0)
    (hτ : P.ordForm τ = P.ordForm τ₀) {ρ : RationalPluriForms (j ≫ sX) n 1}
    (hρ : IsPoincareResidue sX j n 1 τ ρ) :
    ∃ b : (X.presheaf.stalk (j (genericPoint T)))ˣ,
      τ = algebraMap _ X.functionField (b : X.presheaf.stalk (j (genericPoint T))) • τ₀ ∧
      IsPoincareResidue sX j n 1 τ₀
        ((j.stalkMap (genericPoint T)).hom ((b⁻¹ : (X.presheaf.stalk _)ˣ) : _) • ρ) := by
  letI := functionFieldAlgebra sX
  have hd : (Algebra.trdeg k X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sX) (d := n + 1) (by rw [hdim]; norm_cast)
  have hrank : Module.finrank X.functionField (RationalPluriForms sX (n + 1) 1) = 1 := by
    let bb : Module.Basis Unit X.functionField (RationalPluriForms sX (n + 1) 1) :=
      ZTensorPower.basis b₀ 1
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' τ₀ hτ₀0).mp hrank τ
  have hf0 : f ≠ 0 := by rintro rfl; exact hτ0 (by rw [← hf, zero_smul])
  have hford : X.ord f P.genericPoint = 0 := by
    have := P.ordForm_smul (sX := sX) hd hf0 hτ₀0
    rw [hf, hτ] at this
    omega
  have hfinv : X.ord f⁻¹ P.genericPoint = 0 := by
    have := Scheme.ord_mul (x := P.genericPoint) hf0 (inv_ne_zero hf0)
    rw [mul_inv_cancel₀ hf0, ord_one', hford] at this
    omega
  obtain ⟨a, ha⟩ := MMP.CyclicChartDifferent.Aux.exists_algebraMap_eq_of_ord_nonneg P hf0 hford.ge
  obtain ⟨a', ha'⟩ := MMP.CyclicChartDifferent.Aux.exists_algebraMap_eq_of_ord_nonneg P
    (inv_ne_zero hf0) hfinv.ge
  have hspP : j (genericPoint T) ⤳ P.genericPoint := specializes_of_eq hjT
  set sp := (X.presheaf.stalkSpecializes hspP).hom
  have hK : ∀ z, algebraMap _ X.functionField (sp z) = algebraMap _ X.functionField z :=
    MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' X hspP
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk (j (genericPoint T)))
      X.functionField) := IsFractionRing.injective _ _
  have hu : sp a * sp a' = 1 :=
    hinj (by rw [map_mul, hK, hK, ha, ha', mul_inv_cancel₀ hf0, map_one])
  let b : (X.presheaf.stalk (j (genericPoint T)))ˣ := ⟨sp a, sp a', hu, by rw [mul_comm, hu]⟩
  have hb : algebraMap _ X.functionField (b : X.presheaf.stalk (j (genericPoint T))) = f := by
    change algebraMap _ X.functionField (sp a) = f
    rw [hK, ha]
  refine ⟨b, by rw [hb, hf], ?_⟩
  have hres := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ
    ((b⁻¹ : (X.presheaf.stalk _)ˣ) : _)
  convert hres using 1
  rw [← hf, smul_smul, ← hb, ← map_mul, Units.inv_mul, map_one, one_smul]

end ChangeForm

/-! ### Orders of residues -/

section ResidueOrders

open MMP.Flips

universe u

/-- Under `(⋆)`, if `ω = 𝒪_X(K)` then `ω_X(S) = 𝒪_X(K + S)`. -/
theorem DifferentHypotheses.twist_eq_sheaf {k : Type u} [Field k] {X S : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [IsNormal X] {j : S ⟶ X} [IsClosedImmersion j]
    {π : X ⟶ Spec (.of k)} {d : ℕ} {ω ωXS : WeilDivisorialSubsheaf X}
    {DS : MMP.Flips.WeilDivisor X} {B : QWeilDivisor X} (hH : DifferentHypotheses j π d ω ωXS DS B)
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    {K : Mori.Divisor X} (hω : ω.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor K).sheaf) :
    ωXS.toRationalFunctionsSubmodule =
      (Divisor.toWeilDivisor (K + Finsupp.single P 1)).sheaf := by
  classical
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have : LocallyOfFiniteType π := hH.isNormalVariety.1.toLocallyOfFiniteType
  have hd := hH.isDualizingSheaf.1
  obtain ⟨K₁, hK₁⟩ := WeilDivisorialSubsheaf.exists_eq_sheaf_toWeilDivisor π hd ωXS
  rw [hK₁]
  congr 2
  ext E
  set Γ : WeilDivisorPrime X := PrimeDivisor.toWeilDivisorPrime E
  have h₁ : HasOrderAt ω.toRationalFunctionsSubmodule Γ (-K.coeff E) := by
    rw [hω]
    exact WeilDivisor.hasOrderAt_sheaf π hd (Divisor.toWeilDivisor K) Γ
  have hDS : DS Γ = DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℤ) : Mori.Divisor X) E := by
    rw [hH.coeff_divisor Γ]
    by_cases hEP : E = P
    · subst hEP
      rw [DivisorWithCoeffs.coeff_single_self, if_pos]
      have : Nonempty S := by
        obtain ⟨y, hy⟩ : (E.support : Set X).Nonempty :=
          ⟨E.genericPoint, primeDivisor_genericPoint_mem_support E⟩
        rw [← hP] at hy
        obtain ⟨z, -⟩ := hy
        exact ⟨z⟩
      obtain ⟨Z, -⟩ := exists_mem_irreducibleComponents (Classical.arbitrary S)
      obtain ⟨Γ', hΓ'⟩ := hH.exists_weilDivisorPrime ⟨_, Z.2⟩
      have hΓ'P : Γ'.1 = E := by
        refine eq_of_genericPoint_mem_primeDivisor_support ?_
        rw [hΓ']
        change _ ∈ (E.support : Set X)
        rw [← hP]
        exact ⟨_, rfl⟩
      exact ⟨⟨_, Z.2⟩, by rw [← hΓ', hΓ'P]; rfl⟩
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hEP), if_neg]
      rintro ⟨Z, hZ⟩
      apply hEP
      refine eq_of_genericPoint_mem_primeDivisor_support ?_
      change E.genericPoint ∈ (P.support : Set X)
      rw [← hP]
      exact ⟨_, hZ.symm⟩
  have h₂ : HasOrderAt DS.sheaf Γ (-DS Γ) := WeilDivisor.hasOrderAt_sheaf π hd DS Γ
  have h₃ : HasOrderAt ωXS.toRationalFunctionsSubmodule Γ (-K.coeff E + -DS Γ) := by
    rw [hH.twist_eq]
    exact h₁.mul h₂
  have h₄ : HasOrderAt ωXS.toRationalFunctionsSubmodule Γ (-K₁.coeff E) := by
    rw [hK₁]
    exact WeilDivisor.hasOrderAt_sheaf π hd (Divisor.toWeilDivisor K₁) Γ
  have := h₃.unique h₄
  rw [DivisorWithCoeffs.coeff_add, ← hDS]
  change K₁.coeff E = _
  omega

open Classical in
/-- **Residues of sections of `ω_X(S)` have no pole beyond `Res_S τ₀`.** If `ω = 𝒪_X(div τ₀)`
and `c` is a section of `ω_X(S) = 𝒪_X(div τ₀ + S)` near `j(η_Q)`, then
`v_Q(c|_S) ≥ -ord_Q(Res_S τ₀)`: `Res_S(c τ₀) = c|_S Res_S τ₀` has no pole along `Q`
(`MMP.Fourfold.zero_le_ordForm_of_isPoincareResidue`). -/
theorem le_ord_stalkMap_of_isPoincareResidue {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (hjT : j (genericPoint T) = P.genericPoint) (Q : Mori.PrimeDivisor T)
    {τ₀ : RationalPluriForms sX (n + 1) 1} (hτ₀0 : τ₀ ≠ 0)
    {ρ₀ : RationalPluriForms (j ≫ sX) n 1} (hρ₀0 : ρ₀ ≠ 0)
    (hρ₀ : IsPoincareResidue sX j n 1 τ₀ ρ₀) (c : X.presheaf.stalk (j (genericPoint T)))
    (hc0 : (j.stalkMap (genericPoint T)).hom c ≠ 0)
    (hc : ∀ E : Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support →
      -E.ordForm τ₀ - (if E = P then 1 else 0) ≤
        X.ord (algebraMap _ X.functionField c) E.genericPoint) :
    -Q.ordForm ρ₀ ≤ T.ord ((j.stalkMap (genericPoint T)).hom c) Q.genericPoint := by
  have : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (j ≫ sX)
  have hd : (Algebra.trdeg k X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (Algebra.trdeg k T.functionField).toNat = n := by
    have := MMP.CyclicChartDifferent.Aux.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  have hcK : algebraMap _ X.functionField c ≠ 0 := by
    intro h
    apply hc0
    rw [(map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h, map_zero]
  have hres := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ₀ c
  have hxP : j Q.genericPoint ∈ P.support := by
    change _ ∈ (P.support : Set X); rw [← hP]; exact ⟨_, rfl⟩
  have key := zero_le_ordForm_of_isPoincareResidue sX hX hdim j hT P hP Q (α := _ • τ₀)
    (by
      rw [P.ordForm_smul (sX := sX) hd hcK hτ₀0]
      have := hc P hxP
      rw [if_pos rfl] at this
      omega)
    (fun E hxE hEP => by
      rw [E.ordForm_smul (sX := sX) hd hcK hτ₀0]
      have := hc E hxE
      rw [if_neg hEP] at this
      omega) hres
  rw [Q.ordForm_smul (sX := j ≫ sX) hdT hc0 hρ₀0] at key
  omega

open Classical in
/-- **Some section of `ω_X(S)` restricts to order `-ord_Q(Res_S τ₀)`.** A form `g Res_S τ₀` with
no zero or pole along `Q` lifts to `σ = c τ₀` with `c` a section of `ω_X(S)` near `j(η_Q)`
(`MMP.Fourfold.exists_isPoincareResidue_of_le_ordForm_of_charZero`), and `c|_S = g` by uniqueness
of residues. -/
theorem exists_ord_stalkMap_eq_of_isPoincareResidue {k : Type} [Field k] [CharZero k]
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (hjT : j (genericPoint T) = P.genericPoint) (Q : Mori.PrimeDivisor T)
    {τ₀ : RationalPluriForms sX (n + 1) 1} (hτ₀0 : τ₀ ≠ 0) (hτ₀P : P.ordForm τ₀ = -1)
    {ρ₀ : RationalPluriForms (j ≫ sX) n 1} (hρ₀0 : ρ₀ ≠ 0)
    (hρ₀ : IsPoincareResidue sX j n 1 τ₀ ρ₀) :
    ∃ c : X.presheaf.stalk (j (genericPoint T)), (j.stalkMap (genericPoint T)).hom c ≠ 0 ∧
      (∀ E : Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support →
        -E.ordForm τ₀ - (if E = P then 1 else 0) ≤
          X.ord (algebraMap _ X.functionField c) E.genericPoint) ∧
      T.ord ((j.stalkMap (genericPoint T)).hom c) Q.genericPoint = -Q.ordForm ρ₀ := by
  have : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (j ≫ sX)
  have hd : (Algebra.trdeg k X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (Algebra.trdeg k T.functionField).toNat = n := by
    have := MMP.CyclicChartDifferent.Aux.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sX) (d := n + 1) (by rw [hdim]; norm_cast)
  have hrank : Module.finrank X.functionField (RationalPluriForms sX (n + 1) 1) = 1 := by
    let bb : Module.Basis Unit X.functionField (RationalPluriForms sX (n + 1) 1) :=
      ZTensorPower.basis b₀ 1
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  -- a form `g ρ₀` without zero or pole along `Q`, and a lift `σ = f τ₀` of it
  obtain ⟨g, hg0, hg⟩ := MMP.CyclicChartDifferent.Aux.exists_ord_eq Q (-Q.ordForm ρ₀)
  have hgρ : Q.ordForm (g • ρ₀) = 0 := by
    rw [Q.ordForm_smul (sX := j ≫ sX) hdT hg0 hρ₀0, hg]; ring
  obtain ⟨σ, hσP, hσE, hσres⟩ :=
    exists_isPoincareResidue_of_le_ordForm_of_charZero sX hX hdim j hT P hP Q (g • ρ₀) hgρ.ge
  obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' τ₀ hτ₀0).mp hrank σ
  have hspP : j (genericPoint T) ⤳ P.genericPoint := specializes_of_eq hjT
  -- `f` is regular along `P`
  have hres0 : ∀ c : X.presheaf.stalk (j (genericPoint T)), algebraMap _ X.functionField c = f →
      (j.stalkMap (genericPoint T)).hom c = g := by
    intro c hcf
    have hres := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ₀ c
    rw [hcf, hf] at hres
    have := isPoincareResidue_unique (sY := sX) hjT hσres hres
    exact (smul_left_injective _ hρ₀0 this).symm
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := hres0 0 (map_zero _)
    rw [map_zero] at this
    exact hg0 this.symm
  have hford : ∀ E : Mori.PrimeDivisor X, E.ordForm σ = X.ord f E.genericPoint + E.ordForm τ₀ :=
    fun E => by rw [← hf, E.ordForm_smul (sX := sX) hd hf0 hτ₀0]
  obtain ⟨a, ha⟩ := MMP.CyclicChartDifferent.Aux.exists_algebraMap_eq_of_ord_nonneg P hf0
    (by have := hford P; omega)
  set c := (X.presheaf.stalkSpecializes hspP).hom a
  have hc : algebraMap _ X.functionField c = f := by
    rw [MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes', ha]
  refine ⟨c, by rw [hres0 c hc]; exact hg0, fun E hxE => ?_, by rw [hres0 c hc, hg]⟩
  rw [hc]
  have := hford E
  split_ifs with hEP
  · subst hEP; omega
  · have := hσE E hxE hEP; omega

end ResidueOrders

/-! ### The embedded dualizing sheaf -/

section EmbeddedDualizing

open MMP.Flips MMP.Flips.RationalFunctionsSubmodule Opposite

universe u

/-- Transport of an element of `𝒪_{X,j(ζ)}` from a point `ζ = η_S` to the generic point. -/
theorem exists_stalkMap_eq_of_eq_genericPoint {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (j : S ⟶ X) {ζ : S} (e : ζ = genericPoint S) (c : X.presheaf.stalk (j ζ)) :
    ∃ c' : X.presheaf.stalk (j (genericPoint S)),
      algebraMap _ X.functionField c' = algebraMap _ X.functionField c ∧
      algebraMap (S.presheaf.stalk ζ) S.functionField ((j.stalkMap ζ).hom c) =
        (j.stalkMap (genericPoint S)).hom c' := by
  subst e
  exact ⟨c, rfl, MMP.CyclicChartDifferent.Aux.algebraMap_stalk_genericPoint S _⟩

/-- The value of `l|_S` at the generic point of `S`, for a section `l` regular along `S`. -/
theorem exists_restrictAlong_eq_stalkMap {X S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (j : S ⟶ X) (Q : Mori.PrimeDivisor S) {W : X.Opens} (hQ : j.base Q.genericPoint ∈ W)
    {l : ToType ((rationalFunctionsPresheaf X).obj (op W))} (hl : IsRegularAlong j l)
    (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ W) :
    ∃ c : X.presheaf.stalk (j (genericPoint S)),
      algebraMap _ X.functionField c =
        (MMP.Positivity.componentToFunctionField Z).hom (l ⟨Z, hZ⟩) ∧
      (MMP.Positivity.componentToFunctionField Q.component).hom
        ((rationalFunctionsStalkEval Q.genericPoint Q.component).hom
          ((rationalFunctionsPresheaf S).germ (j ⁻¹ᵁ W) Q.genericPoint hQ
            (restrictAlong j l hl))) = (j.stalkMap (genericPoint S)).hom c := by
  have hW : componentGenericPoint S Q.component ∈ j ⁻¹ᵁ W :=
    componentGenericPoint_mem_of_nonempty Q.component ⟨Q.genericPoint, hQ⟩
  obtain ⟨c, hc⟩ := hl Q.component hW
  obtain ⟨c', hc'1, hc'2⟩ := exists_stalkMap_eq_of_eq_genericPoint j
    (componentGenericPoint_eq_genericPoint Q.component) c
  refine ⟨c', ?_, ?_⟩
  · rw [hc'1]
    have h := congrArg (rationalFunctionsStalkEval _ Z).hom hc
    rw [rationalFunctionsStalkEval_structure, rationalFunctionsStalkEval_germ _ _ (U := W) hW] at h
    rw [← MMP.CyclicChartDifferent.Aux.componentToFunctionField_stalkSpecializes X Z
      (componentGenericPoint_specializes Z _), h]
  · rw [rationalFunctionsStalkEval_germ _ _ (U := j ⁻¹ᵁ W) hQ,
      restrictAlong_apply_of_germ_eq j hl ⟨Q.component, hW⟩ c hc]
    exact hc'2

open Classical in
/-- A nonzero section of `𝒪_X(K₀ + P)` near `x` has order `≥ -K₀_E - [E = P]` along every prime
divisor `E` through `x`. -/
theorem le_ord_of_mem_sections_add_single {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X]
    {n : ℕ} {P : Mori.PrimeDivisor X} {ωXS : WeilDivisorialSubsheaf X} {K₀ : Mori.Divisor X}
    (hωXS : ωXS.toRationalFunctionsSubmodule =
      (Divisor.toWeilDivisor (K₀ + Finsupp.single P 1)).sheaf)
    {τ₀ : RationalPluriForms sX (n + 1) 1}
    (hτ₀K : ∀ E : Mori.PrimeDivisor X, E.ordForm τ₀ = K₀.coeff E) {W : X.Opens} {x : X}
    (hx : x ∈ W) {l : ToType ((rationalFunctionsPresheaf X).obj (op W))}
    (hlL : l ∈ ωXS.toRationalFunctionsSubmodule.sections W) (Z : irreducibleComponents X)
    (hZ : componentGenericPoint X Z ∈ W)
    (hl0 : (MMP.Positivity.componentToFunctionField Z).hom (l ⟨Z, hZ⟩) ≠ 0)
    (E : Mori.PrimeDivisor X) (hxE : x ∈ E.support) :
    -E.ordForm τ₀ - (if E = P then 1 else 0) ≤
      X.ord ((MMP.Positivity.componentToFunctionField Z).hom (l ⟨Z, hZ⟩)) E.genericPoint := by
  have hsubX := subsingleton_irreducibleComponents (X := X)
  rw [hωXS, sheaf_toWeilDivisor_sections] at hlL
  have h1 := hlL E ⟨_, hxE, hx⟩
  obtain rfl : Z = E.component := Subsingleton.elim _ _
  rw [PrimeDivisor.ordGE_iff_le_ord E (fun h => hl0 (by rw [h, map_zero])),
    DivisorWithCoeffs.coeff_add] at h1
  rw [hτ₀K E]
  split_ifs with hEP
  · subst hEP; rw [DivisorWithCoeffs.coeff_single_self] at h1; convert h1 using 1; ring
  · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hEP)] at h1; omega

open Classical in
/-- The residue-regularity half of `hasOrderAt_embeddedDualizingSheaf`: the germs of
`ε(i^*ω_X(S))` along `Q` have order `≥ -ord_Q ρ₀`. -/
theorem ordGE_of_mem_stalkSet_restrictionImage {k : Type} [Field k] [CharZero k] {X S : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : S ⟶ X) [IsClosedImmersion j] [IsIntegral S] [IsNormal S] [IsNoetherian S]
    (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (hjT : j (genericPoint S) = P.genericPoint)
    {ωXS : WeilDivisorialSubsheaf X} {K₀ : Mori.Divisor X}
    (hωXS : ωXS.toRationalFunctionsSubmodule =
      (Divisor.toWeilDivisor (K₀ + Finsupp.single P 1)).sheaf)
    {τ₀ : RationalPluriForms sX (n + 1) 1} (hτ₀0 : τ₀ ≠ 0)
    (hτ₀K : ∀ E : Mori.PrimeDivisor X, E.ordForm τ₀ = K₀.coeff E)
    {ρ₀ : RationalPluriForms (j ≫ sX) n 1} (hρ₀0 : ρ₀ ≠ 0)
    (hρ₀ : IsPoincareResidue sX j n 1 τ₀ ρ₀) (Q : Mori.PrimeDivisor S)
    {g : (rationalFunctionsPresheaf S).stalk Q.genericPoint}
    (hg : g ∈ (restrictionImage j ωXS.toRationalFunctionsSubmodule).stalkSet Q.genericPoint) :
    Q.OrdGE (-Q.ordForm ρ₀) ((rationalFunctionsStalkEval Q.genericPoint Q.component).hom g) := by
  have hunit : ∀ (y : S) (_ : y = genericPoint S) (w : S.presheaf.stalk y), w ≠ 0 → IsUnit w := by
    rintro y rfl w hw
    exact IsUnit.mk0 (w : S.functionField) hw
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk (j (genericPoint S)))
      X.functionField) := IsFractionRing.injective _ _
  have hxP : j Q.genericPoint ∈ P.support := by
    rw [← hP]; exact ⟨_, rfl⟩
  refine stalkSet_restrictionImage_subset j (T := {g | Q.OrdGE (-Q.ordForm ρ₀)
    ((rationalFunctionsStalkEval Q.genericPoint Q.component).hom g)}) ?_ ?_ ?_ ?_ hg
  · rw [Set.mem_ofPred_eq, map_zero]; exact PrimeDivisor.OrdGE.zero _
  · intro g h hg hh
    rw [Set.mem_ofPred_eq, map_add]; exact hg.add hh
  · intro b g hg
    rw [Set.mem_ofPred_eq, map_mul, rationalFunctionsStalkEval_structure_primeDivisor]
    exact hg.toComponent_mul _
  · intro W hQ l hlL hl
    obtain ⟨c, hc1, hc2⟩ := exists_restrictAlong_eq_stalkMap j Q hQ hl P.component
      (P.componentGenericPoint_mem_of_nonempty ⟨_, hxP, hQ⟩)
    set v := (rationalFunctionsStalkEval Q.genericPoint Q.component).hom
        ((rationalFunctionsPresheaf S).germ (j ⁻¹ᵁ W) Q.genericPoint hQ (restrictAlong j l hl))
    change Q.OrdGE _ v
    by_cases hv : v = 0
    · rw [hv]; exact PrimeDivisor.OrdGE.zero _
    rw [PrimeDivisor.ordGE_iff_le_ord Q hv, hc2]
    have hv' : (j.stalkMap (genericPoint S)).hom c ≠ 0 := by
      rw [← hc2]
      exact ((hunit _ (componentGenericPoint_eq_genericPoint Q.component) v hv).map _).ne_zero
    refine le_ord_stalkMap_of_isPoincareResidue sX hX hdim j hT P hP hjT Q hτ₀0 hρ₀0 hρ₀ c hv'
      fun E hxE => ?_
    have hc0 : algebraMap _ X.functionField c ≠ 0 := fun h =>
      hv' (by rw [hinj (h.trans (map_zero _).symm), map_zero])
    rw [hc1] at hc0 ⊢
    exact le_ord_of_mem_sections_add_single hωXS hτ₀K hQ hlL _ _ hc0 E hxE

open Classical in
/-- The residue-lift half of `hasOrderAt_embeddedDualizingSheaf`: every germ along `Q` of order
`≥ -ord_Q ρ₀` lies in `ε(i^*ω_X(S))`. -/
theorem mem_stalkSet_restrictionImage_of_ordGE {k : Type} [Field k] [CharZero k] {X S : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : S ⟶ X) [IsClosedImmersion j] [IsIntegral S] [IsNormal S] [IsNoetherian S]
    (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (hjT : j (genericPoint S) = P.genericPoint)
    (hS : ∀ Z : irreducibleComponents S, Order.coheight (j.base (componentGenericPoint S Z)) ≤ 1)
    {ωXS : WeilDivisorialSubsheaf X} (hL : ωXS ∈ goodSupportSubsheaves (closedRange j))
    {K₀ : Mori.Divisor X} (hωXS : ωXS.toRationalFunctionsSubmodule =
      (Divisor.toWeilDivisor (K₀ + Finsupp.single P 1)).sheaf)
    {τ₀ : RationalPluriForms sX (n + 1) 1} (hτ₀0 : τ₀ ≠ 0)
    (hτ₀K : ∀ E : Mori.PrimeDivisor X, E.ordForm τ₀ = K₀.coeff E) (hτ₀P : P.ordForm τ₀ = -1)
    {ρ₀ : RationalPluriForms (j ≫ sX) n 1} (hρ₀0 : ρ₀ ≠ 0)
    (hρ₀ : IsPoincareResidue sX j n 1 τ₀ ρ₀) (Q : Mori.PrimeDivisor S)
    {g : (rationalFunctionsPresheaf S).stalk Q.genericPoint}
    (hg : Q.OrdGE (-Q.ordForm ρ₀) ((rationalFunctionsStalkEval Q.genericPoint Q.component).hom g)) :
    g ∈ (restrictionImage j ωXS.toRationalFunctionsSubmodule).stalkSet Q.genericPoint := by
  have hsubX := subsingleton_irreducibleComponents (X := X)
  have hunit : ∀ (y : S) (_ : y = genericPoint S) (w : S.presheaf.stalk y), w ≠ 0 → IsUnit w := by
    rintro y rfl w hw
    exact IsUnit.mk0 (w : S.functionField) hw
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk (j (genericPoint S)))
      X.functionField) := IsFractionRing.injective _ _
  have hxP : j Q.genericPoint ∈ P.support := by
    rw [← hP]; exact ⟨_, rfl⟩
  obtain ⟨c, hc0, hcb, hcord⟩ := exists_ord_stalkMap_eq_of_isPoincareResidue sX hX hdim j hT P
    hP hjT Q hτ₀0 hτ₀P hρ₀0 hρ₀
  have hcK : algebraMap _ X.functionField c ≠ 0 := fun h =>
    hc0 (by rw [hinj (h.trans (map_zero _).symm), map_zero])
  obtain ⟨χ, hχ⟩ := exists_units_componentToFunctionField_eq hcK
  obtain ⟨W, hQ, hWs⟩ := Divisor.exists_isDivisorialSection_of_forall_mem_support
    (K₀ + Finsupp.single P 1) χ (j Q.genericPoint) (fun E hxE => by
      rw [MMP.Positivity.ord_eq_ord_componentToFunctionField, hχ, DivisorWithCoeffs.coeff_add]
      have := hcb E hxE
      rw [hτ₀K E] at this
      split_ifs at this with hEP
      · subst hEP; rw [DivisorWithCoeffs.coeff_single_self]; omega
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hEP)]; omega)
  set s : ToType ((rationalFunctionsPresheaf X).obj (op W)) :=
    fun Z => (χ : RationalFunctions X) Z.1
  have hs : s ∈ ωXS.toRationalFunctionsSubmodule.sections W := by
    rwa [hωXS, sheaf_toWeilDivisor_sections]
  have hl := isRegularAlong_of_mem hS hL hs
  have hPW := P.componentGenericPoint_mem_of_nonempty ⟨_, hxP, hQ⟩
  obtain ⟨c', hc'1, hc'2⟩ := exists_restrictAlong_eq_stalkMap j Q hQ hl P.component hPW
  have hcc : c' = c := hinj (by rw [hc'1]; exact hχ _)
  rw [hcc] at hc'2
  set f₀ := (rationalFunctionsPresheaf S).germ (j ⁻¹ᵁ W) Q.genericPoint hQ (restrictAlong j s hl)
  set v := (rationalFunctionsStalkEval Q.genericPoint Q.component).hom f₀
  have hv : v ≠ 0 := fun h => hc0 (by rw [← hc'2, h, map_zero])
  have hvu := hunit _ (componentGenericPoint_eq_genericPoint Q.component) v hv
  have hf₀ : IsUnit f₀ := isUnit_of_rationalFunctionsStalkEval_ne_zero Q.component hv
  have hval : Q.valuation ((rationalFunctionsStalkEval Q.genericPoint Q.component).hom
      (hf₀.unit : (rationalFunctionsPresheaf S).stalk Q.genericPoint)) =
        WithZero.exp (-Q.ordForm ρ₀) := by
    rw [hf₀.unit_spec]
    change Q.valuation v = _
    rw [← hvu.unit_spec, PrimeDivisor.valuation_eq_exp_ordUnit,
      MMP.CyclicChartDifferent.Aux.ordUnit_eq_ord, hvu.unit_spec]
    congr 2
    rw [hc'2, hcord]
  obtain ⟨b, rfl⟩ := (mem_range_unit_mul_iff_ordGE Q hf₀.unit hval g).mpr hg
  rw [hf₀.unit_spec]
  exact germ_restrictAlong_mul_mem_stalkSet_restrictionImage j hs hl hQ b

open Classical in
/-- **The embedded dualizing sheaf is `𝒪_S(div Res_S τ₀)`.** If `ω_X(S) = 𝒪_X(div τ₀ + S)` for
a rational top form `τ₀` with a simple pole along `S` and `ρ₀ = Res_S τ₀`, then `Ω_S` has order
`-ord_Q ρ₀` along every prime divisor `Q` of `S`. The generators `(l|_S)_Q` of `ε(i^*ω_X(S))_Q`
are the residue multipliers `Res_S(l τ₀) = l|_S ρ₀`, of order `≥ -ord_Q ρ₀` by residue
regularity, with equality for a lift of a form without zero or pole along `Q`. -/
theorem hasOrderAt_embeddedDualizingSheaf {k : Type} [Field k] [CharZero k] {X S : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : S ⟶ X) [IsClosedImmersion j] [IsIntegral S] [IsNormal S] [IsLocallyNoetherian S]
    [CompactSpace S] [IsNoetherian S] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (hjT : j (genericPoint S) = P.genericPoint)
    (hS : ∀ Z : irreducibleComponents S, Order.coheight (j.base (componentGenericPoint S Z)) ≤ 1)
    {ωXS : WeilDivisorialSubsheaf X} (hL : ωXS ∈ goodSupportSubsheaves (closedRange j))
    {K₀ : Mori.Divisor X} (hωXS : ωXS.toRationalFunctionsSubmodule =
      (Divisor.toWeilDivisor (K₀ + Finsupp.single P 1)).sheaf)
    {τ₀ : RationalPluriForms sX (n + 1) 1} (hτ₀0 : τ₀ ≠ 0)
    (hτ₀K : ∀ E : Mori.PrimeDivisor X, E.ordForm τ₀ = K₀.coeff E) (hτ₀P : P.ordForm τ₀ = -1)
    {ρ₀ : RationalPluriForms (j ≫ sX) n 1} (hρ₀0 : ρ₀ ≠ 0)
    (hρ₀ : IsPoincareResidue sX j n 1 τ₀ ρ₀) (Q : Mori.PrimeDivisor S) :
    HasOrderAt (embeddedDualizingSheaf j ωXS) (PrimeDivisor.toWeilDivisorPrime Q)
      (-Q.ordForm ρ₀) := by
  set Γ : WeilDivisorPrime S := PrimeDivisor.toWeilDivisorPrime Q
  change (embeddedDualizingSheaf j ωXS).stalkSet Q.genericPoint = _
  rw [embeddedDualizingSheaf, stalkSet_saturation (show Order.coheight Q.genericPoint ≤ 1 from
    coheight_genericPoint_le_one_of_weilDivisorPrime Γ)]
  ext g
  refine Iff.trans ?_ (mem_range_uniformizerUnit_zpow_mul_iff_ordGE Γ _ g).symm
  exact ⟨ordGE_of_mem_stalkSet_restrictionImage sX hX hdim j hT P hP hjT hωXS hτ₀0 hτ₀K hρ₀0 hρ₀ Q,
    mem_stalkSet_restrictionImage_of_ordGE sX hX hdim j hT P hP hjT hS hL hωXS hτ₀0 hτ₀K hτ₀P hρ₀0
      hρ₀ Q⟩

end EmbeddedDualizing

/-! ### Generators of reflexive powers -/

section ReflexiveGenerators

open MMP.Flips MMP.Flips.RationalFunctionsSubmodule Opposite

universe u

/-- **Reflexive powers of `𝒪_X(D)`.** On an integral Noetherian normal scheme,
`𝒪_X(D)^[n+1] = 𝒪_X((n+1)D)`: both are saturated, with the same orders along every prime divisor
and equal to `K(X)` at the generic point. -/
theorem Divisor.reflexivePowNat_sheaf_toWeilDivisor {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [IsNormal X] (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π]
    {d : ℕ} (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) (D : Mori.Divisor X)
    (n : ℕ) :
    (Divisor.toWeilDivisor D).sheaf.reflexivePowNat (n + 1) =
      (Divisor.toWeilDivisor ((n + 1 : ℕ) • D)).sheaf := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  refine RationalFunctionsSubmodule.eq_of_stalkSet_eq (isSaturated_saturation _)
    (WeilDivisor.isSaturated_sheaf _) fun η hη => ?_
  by_cases hΓ : ∃ Γ : WeilDivisorPrime X, Γ.1.genericPoint = η
  · obtain ⟨Γ, rfl⟩ := hΓ
    have h1 :=
      (WeilDivisor.hasOrderAt_sheaf π hd (Divisor.toWeilDivisor D) Γ).reflexivePowNat_succ n
    have h2 := WeilDivisor.hasOrderAt_sheaf π hd (Divisor.toWeilDivisor ((n + 1 : ℕ) • D)) Γ
    have he : ((n + 1 : ℕ) : ℤ) * -(Divisor.toWeilDivisor D Γ) =
        -(Divisor.toWeilDivisor ((n + 1 : ℕ) • D) Γ) := by
      rw [Divisor.toWeilDivisor_apply, Divisor.toWeilDivisor_apply]
      change _ = -(((n + 1 : ℕ) • D : Mori.Divisor X) Γ.1)
      rw [Finsupp.smul_apply, nsmul_eq_mul]
      change _ = -(_ * DivisorWithCoeffs.coeff D Γ.1)
      ring
    rw [he] at h1
    rw [hasOrderAt_iff_stalk_eq] at h1 h2
    ext g
    rw [← mem_stalk, ← mem_stalk, h1, h2]
  · push Not at hΓ
    have hsurj := structureStalkToRationalFunctionsStalk_surjective
      (coheight_eq_zero_of_forall_ne hη hΓ)
    have huniv : ∀ D' : Mori.Divisor X, (Divisor.toWeilDivisor D').sheaf.stalkSet η = Set.univ := by
      intro D'
      obtain ⟨L, hL⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf π hd
        (Divisor.toWeilDivisor D')
      rw [WeilDivisor.stalkSet_sheaf_of_coeff_eq_zero hL hη (fun Γ hΓ' => absurd hΓ' (hΓ Γ))]
      ext g
      simp only [Set.mem_range, Set.mem_univ, iff_true, Units.val_one, one_mul]
      exact hsurj g
    rw [huniv]
    have htop : (Divisor.toWeilDivisor D).sheaf.stalk η = ⊤ := by
      ext g; rw [mem_stalk, huniv]; simp
    have hpow : ∀ m : ℕ,
        (⊤ : Submodule ℤ ((rationalFunctionsPresheaf X).stalk η)) ^ (m + 1) = ⊤ := by
      intro m
      induction m with
      | zero => exact pow_one _
      | succ m ih =>
        rw [pow_succ, ih]
        refine eq_top_iff.mpr fun g _ => ?_
        simpa using Submodule.mul_mem_mul (Submodule.mem_top (x := g))
          (Submodule.mem_top (x := (1 : (rationalFunctionsPresheaf X).stalk η)))
    ext g
    simp only [Set.mem_univ, iff_true]
    rw [← mem_stalk, stalk_reflexivePowNat_succ _ hη, htop, hpow]
    exact Submodule.mem_top

/-- If `𝓛 = 𝒪_X(D) ∈ WSh_S(X)` with `d_P = 0` and `𝓛^[n+1]` is invertible at `x = j(η_Q)`, then
some unit `c` of `𝒪_{X,j(η_S)}` has `v_E(c) = -(n+1) d_E` along every prime divisor through `x`
(`MMP.Fourfold.Divisor.ord_eq_neg_coeff_of_stalkSet_eq`), and `i^w_C(𝓛^[n+1])` has order
`v_Q(c|_S)` along `Q`. -/
theorem exists_isUnit_hasOrderAt_weilRestrictionCartier {k : Type u} [Field k] {X S : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [IsNormal X] (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π]
    {d : ℕ} (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    [IsIntegral S] [IsNoetherian S] [IsNormal S] (j : S ⟶ X) [IsClosedImmersion j]
    (hS : ∀ Z : irreducibleComponents S, Order.coheight (j.base (componentGenericPoint S Z)) ≤ 1)
    (P : Mori.PrimeDivisor X) (hjT : j (genericPoint S) = P.genericPoint)
    {L : WeilDivisorialSubsheaf X} (hL : L ∈ goodSupportSubsheaves (closedRange j))
    {D : Mori.Divisor X} (hLD : L.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor D).sheaf)
    (hDP : D.coeff P = 0) (n : ℕ) (Q : Mori.PrimeDivisor S)
    (hinv : (L.toRationalFunctionsSubmodule.reflexivePowNat (n + 1)).IsInvertibleAt
      (j Q.genericPoint)) :
    ∃ c : X.presheaf.stalk (j (genericPoint S)), IsUnit c ∧
      (∀ E : Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support →
        X.ord (algebraMap _ X.functionField c) E.genericPoint = -((n + 1 : ℕ) * D.coeff E)) ∧
      HasOrderAt (weilRestrictionCartier j (L.toRationalFunctionsSubmodule.reflexivePowNat (n + 1)))
        (PrimeDivisor.toWeilDivisorPrime Q)
        (S.ord ((j.stalkMap (genericPoint S)).hom c) Q.genericPoint) := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have : IsLocallyNoetherian S := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace S := IsNoetherian.toCompactSpace
  have hsubX := subsingleton_irreducibleComponents (X := X)
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  set x := j Q.genericPoint
  obtain ⟨f, hf⟩ := hinv
  have hf' := hf
  rw [hLD, Divisor.reflexivePowNat_sheaf_toWeilDivisor π hd D n] at hf'
  have hG := Divisor.ord_eq_neg_coeff_of_stalkSet_eq _ f hf' Z
  have hmem : (f : (rationalFunctionsPresheaf X).stalk x) ∈
      (L.toRationalFunctionsSubmodule.reflexivePowNat (n + 1)).stalkSet x := by
    rw [hf]; exact ⟨1, by simp⟩
  obtain ⟨W, hx, s, hs, hsf⟩ := hmem
  have hreg := isRegularAlong_of_mem_reflexivePowNat j hS hL n hs
  have hZ : componentGenericPoint X Z ∈ W := componentGenericPoint_mem_of_nonempty Z ⟨x, hx⟩
  obtain ⟨c, hc1, hc2⟩ := exists_restrictAlong_eq_stalkMap j Q hx hreg Z hZ
  have hcf : algebraMap _ X.functionField c = (MMP.Positivity.componentToFunctionField Z).hom
      ((rationalFunctionsStalkEval x Z).hom f) := by
    rw [hc1, ← hsf, rationalFunctionsStalkEval_germ _ _ (U := W) hx]
  have hord : ∀ E : Mori.PrimeDivisor X, x ∈ E.support →
      X.ord (algebraMap _ X.functionField c) E.genericPoint = -((n + 1 : ℕ) * D.coeff E) := by
    intro E hxE
    rw [hcf, hG E hxE]
    change -(((n + 1 : ℕ) • D : Mori.Divisor X) E) = _
    rw [Finsupp.smul_apply, nsmul_eq_mul]
    rfl
  have hxP : x ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
    exact (specializes_of_eq hjT.symm).trans
      (j.base.hom.map_specializes (genericPoint_specializes _))
  have hcP : X.ord (algebraMap _ X.functionField c) P.genericPoint = 0 := by
    rw [hord P hxP, hDP, mul_zero, neg_zero]
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk (j (genericPoint S)))
      X.functionField) := IsFractionRing.injective _ _
  have hc0 : algebraMap _ X.functionField c ≠ 0 := by
    rw [hcf]
    exact ((f.isUnit.map (rationalFunctionsStalkEval x Z).hom).map
      (MMP.Positivity.componentToFunctionField Z).hom).ne_zero
  -- `c` is a unit: its inverse has order `0` along `P`
  have hcu : IsUnit c := by
    have hinv0 : X.ord (algebraMap _ X.functionField c)⁻¹ P.genericPoint = 0 := by
      have := Scheme.ord_mul (x := P.genericPoint) hc0 (inv_ne_zero hc0)
      rw [mul_inv_cancel₀ hc0, ord_one', hcP] at this
      omega
    obtain ⟨a, ha⟩ := MMP.CyclicChartDifferent.Aux.exists_algebraMap_eq_of_ord_nonneg P
      (inv_ne_zero hc0) hinv0.ge
    have hspP : j (genericPoint S) ⤳ P.genericPoint := specializes_of_eq hjT
    refine IsUnit.of_mul_eq_one ((X.presheaf.stalkSpecializes hspP).hom a) (hinj ?_)
    rw [map_mul, MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes', ha,
      mul_inv_cancel₀ hc0, map_one]
  refine ⟨c, hcu, hord, ?_⟩
  -- the order of `i^w_C(𝓛^[n+1])` along `Q`
  set g₀ := (rationalFunctionsPresheaf S).germ (j ⁻¹ᵁ W) Q.genericPoint hx (restrictAlong j s hreg)
  set v := (rationalFunctionsStalkEval Q.genericPoint Q.component).hom g₀
  have hcS : (j.stalkMap (genericPoint S)).hom c ≠ 0 :=
    (hcu.map (j.stalkMap (genericPoint S)).hom).ne_zero
  have hv : v ≠ 0 := fun h => hcS (by rw [← hc2]; change _ = 0; rw [h, map_zero])
  have hvu : IsUnit v := by
    have key : ∀ (y : S) (_ : y = genericPoint S) (w : S.presheaf.stalk y), w ≠ 0 → IsUnit w := by
      rintro y rfl w hw
      exact IsUnit.mk0 (w : S.functionField) hw
    exact key _ (componentGenericPoint_eq_genericPoint Q.component) v hv
  have hst := stalkSet_weilRestrictionCartier j hs hreg hx
    (coheight_genericPoint_le_one_of_weilDivisorPrime (PrimeDivisor.toWeilDivisorPrime Q)) f
    hsf.symm hf
  have hval : Q.valuation v = WithZero.exp (S.ord ((j.stalkMap (genericPoint S)).hom c)
      Q.genericPoint) := by
    rw [← hvu.unit_spec, PrimeDivisor.valuation_eq_exp_ordUnit,
      MMP.CyclicChartDifferent.Aux.ordUnit_eq_ord, hvu.unit_spec, hc2]
  exact hasOrderAt_of_stalkSet_eq hval hst

end ReflexiveGenerators

/-! ### The coefficients of the different -/

section Coefficients

open MMP.Flips MMP.Flips.RationalFunctionsSubmodule Opposite

open Classical in
/-- **The coefficients of the different.** Let `j : S ⟶ M` be a closed immersion onto a prime
divisor `P` with `1 ≤ coeff_P B`, and `B_S = Diff_S((B - P)⁺)`, the different of the positive
part of `B - P` (so that `B_S` is the different entering the adjunction step
`MMP.Fourfold.IsAdjunctionStep`, before the negative part is restricted). For a form `τ` with a
simple pole along `P`, write `τ = b τ₀` with `ω = 𝒪_M(div τ₀)`. Then `coeff_P B = 1` and, along
each prime divisor `Q` of `S`, the coefficient of `B_S` is
`-ord_Q Res_S τ₀ - v_Q(f|_S)/k - v_Q(g|_S)/(k'm')`, for generators `f` of
`ω_M(S)^[k]` and `g` of `𝓛^[k']` at `j(η_Q)`, where `i^w (B - P)⁺ = (1/m') i^w 𝓛`: the orders of
`Ω_S` (`MMP.Fourfold.hasOrderAt_embeddedDualizingSheaf`) and of the restrictions
(`MMP.Fourfold.exists_isUnit_hasOrderAt_weilRestrictionCartier`) are additive along the sums
defining the different
(`MMP.Fourfold.QWeilDivisorialSheaf.IsSum.add_eq_of_qHasOrderAt`). -/
theorem exists_coeff_eq_of_isDifferentDivisor
    {k : Type} [Field k] [CharZero k] {M S : Scheme.{0}} {sM : M ⟶ Spec (.of k)} [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] [LocallyOfFiniteType sM]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {B : QDivisor M} {j : S ⟶ M} [IsClosedImmersion j] {BS : QDivisor S}
    (hT : IsNormalVariety k (j ≫ sM))
    {n : ℕ} (hdim : topologicalKrullDim M = n + 1)
    (P : Mori.PrimeDivisor M) (hP1 : 1 ≤ B.coeff P) (hP : Set.range j.base = (P.support : Set M))
    {d : ℕ} {ω ωXS : MMP.Flips.WeilDivisorialSubsheaf M} {DS : MMP.Flips.WeilDivisor M}
    (hS : MMP.Flips.IsDifferentDivisor j sM d ω ωXS DS
      (QDivisor.toQWeilDivisor (B - Finsupp.single P 1)⁺) (QDivisor.toQWeilDivisor BS))
    (τ : RationalPluriForms sM (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sM) n 1) (hρ : IsPoincareResidue sM j n 1 τ ρ)
    (hjT : j (genericPoint S) = P.genericPoint) :
    ∃ (τ₀ : RationalPluriForms sM (n + 1) 1) (K₀ : Mori.Divisor M)
      (b : (M.presheaf.stalk (j (genericPoint S)))ˣ),
      τ = algebraMap _ M.functionField (b : M.presheaf.stalk (j (genericPoint S))) • τ₀ ∧
      τ₀ ≠ 0 ∧ (∀ E : Mori.PrimeDivisor M, E.ordForm τ₀ = K₀.coeff E) ∧ K₀.coeff P = -1 ∧
      B.coeff P = 1 ∧
      ∀ Q : Mori.PrimeDivisor S, ∃ (k k' m' : ℕ) (cf cg : M.presheaf.stalk (j (genericPoint S))),
        0 < k ∧ 0 < k' ∧ 0 < m' ∧ IsUnit cf ∧ IsUnit cg ∧
        (∀ E : Mori.PrimeDivisor M, j Q.genericPoint ∈ E.support →
          M.ord (algebraMap _ M.functionField cf) E.genericPoint =
            -(k * (K₀.coeff E + if E = P then 1 else 0))) ∧
        (∀ E : Mori.PrimeDivisor M, j Q.genericPoint ∈ E.support →
          (M.ord (algebraMap _ M.functionField cg) E.genericPoint : ℚ) =
            -(k' * m' * max (B.coeff E - if E = P then 1 else 0) 0)) ∧
        BS.coeff Q = -Q.ordForm ((j.stalkMap (genericPoint S)).hom
            ((b⁻¹ : (M.presheaf.stalk _)ˣ) : M.presheaf.stalk (j (genericPoint S))) • ρ) -
          (S.ord ((j.stalkMap (genericPoint S)).hom cf) Q.genericPoint : ℚ) / k -
          (S.ord ((j.stalkMap (genericPoint S)).hom cg) Q.genericPoint : ℚ) / (k' * m') := by
  have : IsNoetherian M := {}
  have : IsNoetherian S := {}
  have hlftS : LocallyOfFiniteType (j ≫ sM) := hT.1.toLocallyOfFiniteType
  obtain ⟨hH, -, ⟨mc, Ec, Nc, hmE, hNc, rfl⟩, nB, Dd, N, hΔ,
    hN, -, D0, R, ⟨Ω, Mres, hΩ, ⟨hgoodω, e, hinv, Nm, hNm, rfl⟩, hsum1⟩,
    ⟨L, m', hLgood, hcL, Nr, nr, ⟨-, k', hinv', Nr', hNr', hNrNr⟩, rfl⟩, hsum2⟩ := hS
  have hX := hH.isNormalVariety
  have hd := hH.isDualizingSheaf.1
  have hS1 : ∀ Z : irreducibleComponents S,
      Order.coheight (j.base (componentGenericPoint S Z)) ≤ 1 :=
    fun Z => (hH.coheight_eq_one Z).le
  -- `(a)`: `ω = 𝒪(div τ₀)`
  obtain ⟨τ₀, hτ₀0, K₀, -, hτ₀K, hωK₀⟩ :=
    IsDualizingSheaf.exists_eq_sheaf_toWeilDivisor hX hH.isDualizingSheaf
  obtain rfl : d = n + 1 := by
    have h := hd Set.univ (by rw [irreducibleComponents_eq_singleton]; rfl)
    rw [(IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ M).isHomeomorph), hdim] at h
    exact_mod_cast h.symm
  have hK₀P : K₀.coeff P = -1 := DifferentHypotheses.coeff_eq_neg_one hH P hP hωK₀
  have hτ₀P : P.ordForm τ₀ = -1 := (hτ₀K P).trans hK₀P
  have hωXS := DifferentHypotheses.twist_eq_sheaf hH P hP hωK₀
  obtain ⟨b, hτb, hρ₀⟩ := IsPoincareResidue.exists_unit_smul hdim P hjT hτ0 hτ₀0
    (hτ.trans hτ₀P.symm) hρ
  -- `B_P = 1`
  have hBP : B.coeff P = 1 := by
    have h := hH.not_subset (PrimeDivisor.toWeilDivisorPrime P)
    rw [QDivisor.toQWeilDivisor_apply] at h
    change max (B.coeff P - DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℚ) : QDivisor M) P)
      0 ≠ 0 → P.genericPoint ∉ Set.range j.base at h
    rw [DivisorWithCoeffs.coeff_single_self] at h
    refine le_antisymm (not_lt.mp fun hlt => h ?_ ⟨_, hjT⟩) hP1
    rw [max_eq_left (by linarith)]
    linarith
  refine ⟨τ₀, K₀, b, hτb, hτ₀0, hτ₀K, hK₀P, hBP, fun Q => ?_⟩
  set Γ : WeilDivisorPrime S := PrimeDivisor.toWeilDivisorPrime Q
  have hΓ : ∀ L : WeilDivisorialSubsheaf S, ∃ a, HasOrderAt L.toRationalFunctionsSubmodule Γ a :=
    fun L => WeilDivisorialSubsheaf.exists_hasOrderAt L Γ
  have hcoQ : Order.coheight Q.genericPoint ≤ 1 :=
    coheight_genericPoint_le_one_of_weilDivisorPrime Γ
  set ρ₀ := (j.stalkMap (genericPoint S)).hom
    ((b⁻¹ : (M.presheaf.stalk _)ˣ) : M.presheaf.stalk (j (genericPoint S))) • ρ
  have hρ₀0 : ρ₀ ≠ 0 :=
    MMP.CyclicChartDifferent.Aux.isPoincareResidue_ne_zero sM hX hdim j hT P hP τ₀
    hτ₀0 hτ₀P ρ₀ hρ₀ Q
  have hif : ∀ E : Mori.PrimeDivisor M, ∀ r : ℤ,
      DivisorWithCoeffs.coeff (Finsupp.single P r : Mori.Divisor M) E = if E = P then r else 0 := by
    intro E r
    split_ifs with h
    · subst h; exact DivisorWithCoeffs.coeff_single_self _ _
    · exact DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h) _
  -- `Ω_S`
  have hOmega := HasOrderAt.qHasOrderAt_divNat (Γ := Γ) (L := Ω) (by
    rw [hΩ]
    exact hasOrderAt_embeddedDualizingSheaf sM hX hdim j hT P hP hjT hS1
      hH.mem_goodSupportSubsheaves hωXS hτ₀0 hτ₀K hτ₀P hρ₀0 hρ₀ Q) 1
  -- `i^w ω_X(S)`
  obtain ⟨kk, hkk⟩ : ∃ kk : ℕ, (e : ℕ) = kk + 1 := ⟨e - 1, by have := e.pos; omega⟩
  have hinvQ := hinv Q.genericPoint hcoQ
  rw [RationalFunctionsSubmodule.reflexivePow_natCast, hkk] at hinvQ
  have hDP : (K₀ + Finsupp.single P 1).coeff P = 0 := by
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_single_self, hK₀P]; norm_num
  obtain ⟨cf, hcfu, hcford, hcfQ⟩ := exists_isUnit_hasOrderAt_weilRestrictionCartier sM hd j hS1
    P hjT hH.mem_goodSupportSubsheaves hωXS hDP kk Q hinvQ
  have hMres := HasOrderAt.qHasOrderAt_divNat (Γ := Γ) (L := Nm)
    (by rw [hNm, RationalFunctionsSubmodule.reflexivePow_natCast, hkk]; exact hcfQ) e
  -- `B_S`
  have hdS : ∀ Z ∈ irreducibleComponents S, topologicalKrullDim Z =
      ((letI := functionFieldAlgebra (j ≫ sM); (Algebra.trdeg k S.functionField).toNat : ℕ) :
        WithBot ℕ∞) := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    rw [hZ, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ S).isHomeomorph]
    exact topologicalKrullDim_eq_toNat_trdeg (j ≫ sM)
  have hNo := HasOrderAt.qHasOrderAt_divNat (Γ := Γ) (L := N)
    (by rw [hN]; exact WeilDivisor.hasOrderAt_sheaf (j ≫ sM) hdS Dd Γ) nB
  -- `i^w B`
  obtain ⟨FL, hFL⟩ := WeilDivisorialSubsheaf.exists_eq_sheaf_toWeilDivisor sM hd L
  have hFLE : ∀ E : Mori.PrimeDivisor M,
      (FL.coeff E : ℚ) = m' * max (B.coeff E - if E = P then 1 else 0) 0 := by
    intro E
    set ΓE : WeilDivisorPrime M := PrimeDivisor.toWeilDivisorPrime E
    have h1 : HasOrderAt Nc.toRationalFunctionsSubmodule ΓE (-Ec ΓE) :=
      hNc ▸ WeilDivisor.hasOrderAt_sheaf sM hd Ec ΓE
    have h2 : HasOrderAt L.toRationalFunctionsSubmodule ΓE (-FL.coeff E) := by
      rw [hFL]; exact WeilDivisor.hasOrderAt_sheaf sM hd (Divisor.toWeilDivisor FL) ΓE
    have h3 := HasOrderAt.div_eq_div_of_divNat_eq hcL h1 h2
    have h4 := hmE ΓE
    rw [QDivisor.toQWeilDivisor_apply] at h4
    have h5 : DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℚ) : QDivisor M) E =
        if E = P then 1 else 0 := by
      split_ifs with h
      · subst h; exact DivisorWithCoeffs.coeff_single_self _ _
      · exact DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h) _
    change _ * max (B.coeff E - DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℚ) : QDivisor M) E)
      0 = _ at h4
    rw [h5] at h4
    have hmc : ((mc : ℕ) : ℚ) ≠ 0 := by positivity
    have hm' : ((m' : ℕ) : ℚ) ≠ 0 := by positivity
    rw [div_eq_div_iff hmc hm'] at h3
    push_cast at h3 h4
    apply mul_left_cancel₀ hmc
    linear_combination h3 - (m' : ℚ) * h4
  have hFLP : FL.coeff P = 0 := by
    have := hFLE P
    rw [hBP, if_pos rfl, sub_self, max_self, mul_zero] at this
    exact_mod_cast this
  obtain ⟨kk', hkk'⟩ : ∃ kk : ℕ, (k' : ℕ) = kk + 1 := ⟨k' - 1, by have := k'.pos; omega⟩
  have hinvQ' := hinv' Q.genericPoint hcoQ
  rw [RationalFunctionsSubmodule.reflexivePow_natCast, hkk'] at hinvQ'
  obtain ⟨cg, hcgu, hcgord, hcgQ⟩ := exists_isUnit_hasOrderAt_weilRestrictionCartier sM hd j hS1
    P hjT hLgood hFL hFLP kk' Q hinvQ'
  have hNr'o : HasOrderAt Nr'.toRationalFunctionsSubmodule Γ
      (S.ord ((j.stalkMap (genericPoint S)).hom cg) Q.genericPoint) := by
    rw [hNr', RationalFunctionsSubmodule.reflexivePow_natCast, hkk']; exact hcgQ
  obtain ⟨ar, har⟩ := WeilDivisorialSubsheaf.exists_hasOrderAt Nr Γ
  have hrel := HasOrderAt.div_eq_div_of_divNat_eq hNrNr har hNr'o
  have hRo := har.qHasOrderAt_divNat (m' * nr)
  obtain ⟨r0, hr0⟩ := QWeilDivisorialSheaf.exists_qHasOrderAt hΓ D0
  have e1 := QWeilDivisorialSheaf.IsSum.add_eq_of_qHasOrderAt hsum1 hΓ hOmega hr0 hMres
  have e2 := QWeilDivisorialSheaf.IsSum.add_eq_of_qHasOrderAt hsum2 hΓ hr0 hRo hNo
  have hBS := hΔ Γ
  rw [QDivisor.toQWeilDivisor_apply] at hBS
  refine ⟨kk + 1, kk' + 1, m', cf, cg, by omega, by omega, m'.pos, hcfu, hcgu, fun E hxE => ?_,
    fun E hxE => ?_, ?_⟩
  · rw [hcford E hxE, DivisorWithCoeffs.coeff_add, hif]
  · rw [hcgord E hxE]
    push_cast
    rw [hFLE E]
    ring
  · change BS.coeff Q = _ at hBS
    rw [hBS]
    have hk1 : ((e : ℕ) : ℚ) = ((kk + 1 : ℕ) : ℚ) := by rw [hkk]
    have hk1' : ((k' : ℕ) : ℚ) = ((kk' + 1 : ℕ) : ℚ) := by rw [hkk']
    have hmn : (((m' * nr : ℕ+) : ℕ) : ℚ) = ((m' : ℕ) : ℚ) * ((nr : ℕ) : ℚ) := by
      rw [PNat.mul_coe, Nat.cast_mul]
    have hone : (((1 : ℕ+) : ℕ) : ℚ) = 1 := by simp
    rw [hone, div_one, hk1] at e1
    rw [hmn] at e2
    rw [hk1'] at hrel
    have h6 : (ar : ℚ) / (((m' : ℕ) : ℚ) * ((nr : ℕ) : ℚ)) =
        (S.ord ((j.stalkMap (genericPoint S)).hom cg) Q.genericPoint : ℚ) /
          (((kk' + 1 : ℕ) : ℚ) * ((m' : ℕ) : ℚ)) := by
      rw [show (ar : ℚ) / (((m' : ℕ) : ℚ) * ((nr : ℕ) : ℚ)) =
        ((ar : ℚ) / ((nr : ℕ) : ℚ)) / ((m' : ℕ) : ℚ) by ring, hrel]
      ring
    rw [h6] at e2
    push_cast at e1 e2 ⊢
    linear_combination e2 - e1

end Coefficients

section ResidueDifferent

variable {k : Type} [Field k] {M S : Scheme.{0}} {j : S ⟶ M}

/-- The generic point of a closed subscheme `S` of `M` with support the prime divisor `P` maps to
the generic point of `P`. -/
private theorem genericPoint_eq_of_range_eq [IsIntegral S] [IsClosedImmersion j]
    {P : Mori.PrimeDivisor M} (hP : Set.range j.base = (P.support : Set M)) :
    j (genericPoint S) = P.genericPoint := by
  have h1 : IsGenericPoint (j (genericPoint S)) (P.support : Set M) := by
    have := (genericPoint_spec S).image j.base.hom.continuous
    rwa [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq, hP] at this
  have h2 : IsGenericPoint P.genericPoint (P.support : Set M) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isGenericPoint_closure
  exact h1.eq h2

/-- If `S ⊆ M` has generic point that of the prime divisor `P`, a `ℚ`-divisor `G` with
`coeff_P G = 0` does not contain `S` in its support. -/
private theorem notMem_supp_of_coeff_eq_zero [IsIntegral S] [IsLocallyNoetherian M] [IsNormal M]
    {P : Mori.PrimeDivisor M} (hjT : j (genericPoint S) = P.genericPoint) {G : QDivisor M}
    (hG : G.coeff P = 0) (Z : irreducibleComponents S) :
    j (componentGenericPoint S Z) ∉ G.supp := by
  intro hZ
  rw [componentGenericPoint_eq_genericPoint Z, hjT] at hZ
  obtain ⟨E, hE, hPE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
  obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hPE
  exact hE hG

/-- Pull-back of `ℚ`-Cartier `ℚ`-divisors is additive: `f^*(G₁ + G₂) = f^*G₁ + f^*G₂`. -/
private theorem isPullback_add_of_isQCartier {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y}
    {G₁ G₂ : QDivisor Y} (hG₁ : G₁.IsQCartier) (hG₂ : G₂.IsQCartier)
    {h₁ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₁.supp}
    {h₂ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₂.supp}
    {R₁ R₂ : QDivisor X} (p₁ : G₁.IsPullback f h₁ R₁) (p₂ : G₂.IsPullback f h₂ R₂)
    (h : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (G₁ + G₂).supp) :
    (G₁ + G₂).IsPullback f h (R₁ + R₂) := by
  intro m hm D hD hDc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨m₁, hm₁, A₁, hA₁, hA₁c⟩ := hG₁.exists_pos
  obtain ⟨m₂, hm₂, A₂, hA₂, hA₂c⟩ := hG₂.exists_pos
  obtain ⟨A₁', hA₁', p₁'⟩ := p₁ m₁ hm₁ A₁ hA₁ hA₁c
  obtain ⟨A₂', hA₂', p₂'⟩ := p₂ m₂ hm₂ A₂ hA₂ hA₂c
  have hsuppD : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ D.supp :=
    fun W hW => h W (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hD] at hW)
  have hsupp : ∀ {G : QDivisor Y} (A : Divisor Y) (c : ℤ), c ≠ 0 →
      Divisor.toQDivisor A = c • G →
      (∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G.supp) →
      ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ A.supp :=
    fun A c hc hA hG W hW => hG W (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hc hA] at hW)
  set N : ℤ := (m₁ : ℤ) * m₂
  have hN : N ≠ 0 := mul_ne_zero (by exact_mod_cast hm₁.ne') (by exact_mod_cast hm₂.ne')
  set A : Divisor Y := (m : ℤ) • ((m₂ : ℤ) • A₁ + (m₁ : ℤ) • A₂)
  have hAD : A = N • D := by
    apply Divisor.toQDivisor_injective
    simp only [A, N, map_zsmul, map_add, hA₁, hA₂, hD, smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  have hAc : A.IsCartier := ((hA₁c.zsmul _).add (hA₂c.zsmul _)).zsmul _
  have hA₁N : Divisor.toQDivisor ((m₂ : ℤ) • A₁) = N • G₁ := by
    simp only [map_zsmul, hA₁, smul_smul, N]; congr 1; ring
  have hA₂N : Divisor.toQDivisor ((m₁ : ℤ) • A₂) = N • G₂ := by
    simp only [map_zsmul, hA₂, smul_smul, N]
  have hsum : Divisor.toQDivisor ((m₂ : ℤ) • A₁ + (m₁ : ℤ) • A₂) = N • (G₁ + G₂) := by
    rw [map_add, hA₁N, hA₂N, smul_add]
  have hAq : Divisor.toQDivisor A = ((m : ℤ) * N) • (G₁ + G₂) := by
    simp only [A, map_zsmul, hsum, smul_smul]
  have pA := ((p₁'.zsmul hA₁c (m₂ : ℤ) (hsupp _ _ hN hA₁N h₁)).add (hA₁c.zsmul _)
    (hA₂c.zsmul _) (hsupp _ _ hN hsum h) (p₂'.zsmul hA₂c (m₁ : ℤ) (hsupp _ _ hN hA₂N h₂))).zsmul
    ((hA₁c.zsmul _).add (hA₂c.zsmul _)) (m : ℤ) (hsupp _ _ (mul_ne_zero hm' hN) hAq h)
  obtain ⟨D', hD'⟩ := hDc.exists_isPullback hsuppD
  refine ⟨D', ?_, hD'⟩
  have pND := hD'.zsmul hDc N (hsupp _ _ (mul_ne_zero hN hm') (by
    rw [map_zsmul, hD, smul_smul]) h)
  have heqQ := congrArg Divisor.toQDivisor (pA.eq hAc (pND.of_eq hAD.symm))
  simp only [map_zsmul, map_add, hA₁', hA₂', smul_smul] at heqQ
  ext E
  have := congrArg (fun G : QDivisor X => G.coeff E) heqQ
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, N] at this ⊢
  have hNq : ((m₁ : ℚ) * m₂) ≠ 0 := by positivity
  apply mul_left_cancel₀ hNq
  push_cast at this ⊢
  linear_combination -this

/-- **The residue different of the effective part.** Let `j : S ⟶ M` be a closed immersion onto
a prime divisor `P` with `1 ≤ coeff_P B` and `B_S = Diff_S((B - P)⁺)`, `M` a normal variety of
dimension `n + 1` over a field `k` of characteristic zero. For a nonzero rational top form `τ` on
`M` with a simple pole along `P` and its Poincaré residue `ρ = Res_S τ`, the restriction of
`div τ + (B - P)⁺ + P` to `S` is `div ρ + B_S`. -/
private theorem isPullback_divisorOfForm_add_posPart_of_isPoincareResidue [CharZero k]
    {sM : M ⟶ Spec (.of k)} [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] [LocallyOfFiniteType sM]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] [IsClosedImmersion j]
    {B : QDivisor M} {BS : QDivisor S} (hT : IsNormalVariety k (j ≫ sM))
    {n : ℕ} (hdim : topologicalKrullDim M = n + 1)
    (P : Mori.PrimeDivisor M) (hP1 : 1 ≤ B.coeff P) (hP : Set.range j.base = (P.support : Set M))
    {d : ℕ} {ω ωXS : MMP.Flips.WeilDivisorialSubsheaf M} {DS : MMP.Flips.WeilDivisor M}
    (hS : MMP.Flips.IsDifferentDivisor j sM d ω ωXS DS
      (QDivisor.toQWeilDivisor (B - Finsupp.single P 1)⁺) (QDivisor.toQWeilDivisor BS))
    (τ : RationalPluriForms sM (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sM) n 1) (hρ : IsPoincareResidue sM j n 1 τ ρ) :
    ∃ hgen : ∀ Z : irreducibleComponents S, j (componentGenericPoint S Z) ∉
        (Divisor.toQDivisor (divisorOfForm τ) +
          ((B - Finsupp.single P 1)⁺ + Finsupp.single P 1)).supp,
      (Divisor.toQDivisor (divisorOfForm τ) +
        ((B - Finsupp.single P 1)⁺ + Finsupp.single P 1)).IsPullback j hgen
          (Divisor.toQDivisor (divisorOfForm ρ) + BS) := by
  classical
  letI : LocallyOfFiniteType (j ≫ sM) := hT.1.toLocallyOfFiniteType
  have hNM : IsNoetherian M := {}
  have hsubM := subsingleton_irreducibleComponents (X := M)
  have hX := hS.1.isNormalVariety
  have hjT : j (genericPoint S) = P.genericPoint := genericPoint_eq_of_range_eq hP
  obtain ⟨τ₀, K₀, b, hτb, hτ₀0, hτ₀K, hK₀P, hBP, hQ⟩ :=
    exists_coeff_eq_of_isDifferentDivisor hT hdim P hP1 hP hS τ hτ0 hτ ρ hρ hjT
  set Bp : QDivisor M := (B - Finsupp.single P 1)⁺ + Finsupp.single P 1 with hBpdef
  have hcoe : ∀ E : Mori.PrimeDivisor M,
      Bp.coeff E = max (B.coeff E - if E = P then 1 else 0) 0 + if E = P then 1 else 0 := by
    intro E
    rw [hBpdef, DivisorWithCoeffs.coeff_add]
    change max (B.coeff E - DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℚ) : QDivisor M) E) 0 +
      DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℚ) : QDivisor M) E = _
    split_ifs with h
    · subst h; rw [DivisorWithCoeffs.coeff_single_self]
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h)]
  letI := functionFieldAlgebra sM
  letI := functionFieldAlgebra (j ≫ sM)
  have hd : (Algebra.trdeg k M.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sM) (by rw [hdim]; norm_cast)
  have hdT : (Algebra.trdeg k S.functionField).toNat = n := by
    have := MMP.CyclicChartDifferent.Aux.trdeg_add_one_of_eq_genericPoint (sY := sM) (j := j) P hjT
    omega
  set ψ := (j.stalkMap (genericPoint S)).hom
  have hb0 : algebraMap _ M.functionField (b : M.presheaf.stalk (j (genericPoint S))) ≠ 0 :=
    ((b.isUnit.map _).ne_zero)
  -- the order of `b`
  have hbord : ∀ E : Mori.PrimeDivisor M, M.ord (algebraMap _ M.functionField
      (b : M.presheaf.stalk (j (genericPoint S)))) E.genericPoint = E.ordForm τ - K₀.coeff E := by
    intro E
    have := E.ordForm_smul (sX := sM) hd hb0 hτ₀0
    rw [← hτb, hτ₀K E] at this
    omega
  -- the coefficient at `P`
  have hgen := notMem_supp_of_coeff_eq_zero hjT (G := Divisor.toQDivisor (divisorOfForm τ) + Bp) (by
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτ, hcoe,
      hBP, if_pos rfl]
    norm_num)
  refine ⟨hgen, fun m hm Dm hDm hDmc => ?_⟩
  have hBD : ∀ Z : irreducibleComponents S, j (componentGenericPoint S Z) ∉ Dm.supp :=
    fun Z hZ => hgen Z (by
      rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hDm] at hZ)
  refine ⟨Dm.pullback hDmc hBD, ?_, Divisor.isPullback_pullback hDmc _⟩
  ext Q
  change DivisorWithCoeffs.coeff (Divisor.toQDivisor (Dm.pullback hDmc hBD)) Q =
    DivisorWithCoeffs.coeff (((m : ℕ) : ℤ) • (Divisor.toQDivisor (divisorOfForm ρ) + BS)) Q
  rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toQDivisor, coeff_divisorOfForm, zsmul_eq_mul]
  obtain ⟨k, k', m', cf, cg, hk, hk', hm', hcfu, hcgu, hcford, hcgord, hBSQ⟩ := hQ Q
  set x := j Q.genericPoint with hx
  obtain ⟨U, hxU, φ, hφ⟩ := hDmc x
  have hE : (Q.support ∩ j ⁻¹ᵁ U).Nonempty :=
    ⟨Q.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support Q, hxU⟩
  have hcoef := Divisor.isPullback_pullback hDmc hBD U φ hφ Q hE
  rw [hcoef, MMP.CyclicChartDifferent.Aux.ordUnit_eq_ord]
  have hZU := Q.map_componentGenericPoint_mem j hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZU (hBD Q.component) (mem_pointComponent _)
  rw [pullbackComponent_eq hBD hφ hZU (mem_pointComponent _) a ha]
  obtain ⟨a', ha'1, ha'2⟩ := exists_stalkMap_eq_of_eq_genericPoint j
    (componentGenericPoint_eq_genericPoint Q.component) (a : M.presheaf.stalk _)
  have hψa : (MMP.Positivity.componentToFunctionField Q.component).hom
      ((Units.map (j.stalkMap (componentGenericPoint S Q.component)).hom.toMonoidHom a :
        (S.presheaf.stalk _)ˣ) : S.presheaf.stalk _) = ψ a' := ha'2
  rw [hψa]
  -- orders of the restriction of `φ`
  have hcomp : ∀ Z Z' : irreducibleComponents M,
      (MMP.Positivity.componentToFunctionField Z).hom ((φ : RationalFunctions M) Z) =
        (MMP.Positivity.componentToFunctionField Z').hom ((φ : RationalFunctions M) Z') := by
    intro Z Z'; obtain rfl := Subsingleton.elim Z Z'; rfl
  have ha'K : algebraMap _ M.functionField a' =
      (MMP.Positivity.componentToFunctionField (pointComponent
        (j (componentGenericPoint S Q.component)))).hom
        ((φ : RationalFunctions M) (pointComponent _)) := by
    rw [ha'1, ← MMP.CyclicChartDifferent.Aux.componentToFunctionField_stalkSpecializes M
      (pointComponent (j (componentGenericPoint S Q.component)))
      ((isGenericPoint_componentGenericPoint M _).specializes (mem_pointComponent _))
      (a : M.presheaf.stalk (j (componentGenericPoint S Q.component)))]
    exact congrArg (MMP.Positivity.componentToFunctionField _).hom ha
  have hDmE : ∀ E : Mori.PrimeDivisor M,
      (Dm.coeff E : ℚ) = m * ((E.ordForm τ : ℚ) + Bp.coeff E) := by
    intro E
    have := congrArg (fun G : QDivisor M => G.coeff E) hDm
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, coeff_divisorOfForm, zsmul_eq_mul] at this
    rw [this]; push_cast; ring
  have hφord : ∀ E : Mori.PrimeDivisor M, x ∈ E.support →
      M.ord (algebraMap _ M.functionField a') E.genericPoint = Dm.coeff E := by
    intro E hxE
    rw [ha'K, hφ E ⟨x, hxE, hxU⟩, MMP.Positivity.ord_eq_ord_componentToFunctionField, hcomp]
  -- the comparison `φ^{kk'm'} f^{mk'm'} g^{mk} = u^{mkk'm'} · (unit at x)`
  have hsp : j (genericPoint S) ⤳ x :=
    j.base.hom.map_specializes (genericPoint_specializes Q.genericPoint)
  obtain ⟨Z₀, hxZ₀⟩ := exists_mem_irreducibleComponents x
  have hfa0 : algebraMap _ M.functionField a' ≠ 0 := by
    rw [ha'K]
    exact (((φ.isUnit.map (Pi.evalRingHom _ (pointComponent _))).map
      (MMP.Positivity.componentToFunctionField _).hom).ne_zero)
  have hff0 : algebraMap _ M.functionField cf ≠ 0 := (hcfu.map _).ne_zero
  have hfg0 : algebraMap _ M.functionField cg ≠ 0 := (hcgu.map _).ne_zero
  set w' := algebraMap _ M.functionField a' ^ (k * k' * m') *
    algebraMap _ M.functionField cf ^ (m * k' * m') * algebraMap _ M.functionField cg ^ (m * k)
    with hw'def
  set v := algebraMap _ M.functionField (b : M.presheaf.stalk (j (genericPoint S))) ^
    (m * k * k' * m') with hvdef
  have hw'0 : w' ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hfa0) (pow_ne_zero _ hff0))
    (pow_ne_zero _ hfg0)
  have hv0 : v ≠ 0 := pow_ne_zero _ hb0
  have hword : ∀ E : Mori.PrimeDivisor M, x ∈ E.support →
      M.ord (w' * v⁻¹) E.genericPoint = 0 := by
    intro E hxE
    have hinv : M.ord v⁻¹ E.genericPoint = -M.ord v E.genericPoint := by
      have := Scheme.ord_mul (x := E.genericPoint) hv0 (inv_ne_zero hv0)
      rw [mul_inv_cancel₀ hv0, ord_one'] at this
      omega
    rw [Scheme.ord_mul hw'0 (inv_ne_zero hv0), hinv,
      Scheme.ord_mul (mul_ne_zero (pow_ne_zero _ hfa0) (pow_ne_zero _ hff0)) (pow_ne_zero _ hfg0),
      Scheme.ord_mul (pow_ne_zero _ hfa0) (pow_ne_zero _ hff0),
      MMP.CyclicChartDifferent.Aux.ord_pow' hfa0, MMP.CyclicChartDifferent.Aux.ord_pow' hff0,
      MMP.CyclicChartDifferent.Aux.ord_pow' hfg0, MMP.CyclicChartDifferent.Aux.ord_pow' hb0,
      hφord E hxE, hcford E hxE, hbord E]
    have h1 := hcgord E hxE
    have h2 := hDmE E
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [h2, h1, hcoe]
    split_ifs <;> ring
  obtain ⟨χ, hχ⟩ := exists_units_componentToFunctionField_eq (mul_ne_zero hw'0 (inv_ne_zero hv0))
  obtain ⟨r, hr⟩ := exists_unit_stalk_of_forall_ord_eq_zero hxZ₀ χ (fun E hxE => by
    rw [MMP.Positivity.ord_eq_ord_componentToFunctionField, hχ]; exact hword E hxE)
  have hrK : algebraMap _ M.functionField (r : M.presheaf.stalk x) = w' * v⁻¹ := by
    rw [← MMP.CyclicChartDifferent.Aux.componentToFunctionField_stalkSpecializes M Z₀
      ((isGenericPoint_componentGenericPoint M Z₀).specializes hxZ₀) (r : M.presheaf.stalk x)]
    exact (congrArg (MMP.Positivity.componentToFunctionField Z₀).hom hr).trans (hχ Z₀)
  have hid : a' ^ (k * k' * m') * cf ^ (m * k' * m') * cg ^ (m * k) =
      (b : M.presheaf.stalk _) ^ (m * k * k' * m') *
        (M.presheaf.stalkSpecializes hsp).hom (r : M.presheaf.stalk x) := by
    apply IsFractionRing.injective (M.presheaf.stalk (j (genericPoint S))) M.functionField
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_mul, map_pow,
      MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes', hrK, ← hvdef, ← hw'def,
      mul_comm w' v⁻¹, ← mul_assoc, mul_inv_cancel₀ hv0, one_mul]
  -- restrict to `S` and take orders along `Q`
  have hψ := congrArg ψ hid
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_mul, map_pow,
    Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint S) Q.genericPoint
      (genericPoint_specializes Q.genericPoint)] at hψ
  have hu : IsUnit ((j.stalkMap Q.genericPoint).hom (r : M.presheaf.stalk x)) :=
    r.isUnit.map _
  have hspr : S.ord ((S.presheaf.stalkSpecializes (genericPoint_specializes Q.genericPoint)).hom
      ((j.stalkMap Q.genericPoint).hom (r : M.presheaf.stalk x))) Q.genericPoint = 0 := by
    have h1 := MMP.CyclicChartDifferent.Aux.algebraMap_stalk_genericPoint S
      ((S.presheaf.stalkSpecializes (genericPoint_specializes Q.genericPoint)).hom
        ((j.stalkMap Q.genericPoint).hom (r : M.presheaf.stalk x)))
    rw [← h1, MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes',
      Q.ord_algebraMap_of_isUnit hu]
  have hψa0 : ψ a' ≠ 0 := by
    rw [← ha'2]
    exact (((a.isUnit.map (j.stalkMap _).hom).map _).ne_zero)
  have hψf0 : ψ cf ≠ 0 := (hcfu.map ψ).ne_zero
  have hψg0 : ψ cg ≠ 0 := (hcgu.map ψ).ne_zero
  have hψb0 : ψ (b : M.presheaf.stalk _) ≠ 0 := (b.isUnit.map ψ).ne_zero
  have hspr0 : (S.presheaf.stalkSpecializes (genericPoint_specializes Q.genericPoint)).hom
      ((j.stalkMap Q.genericPoint).hom (r : M.presheaf.stalk x)) ≠ 0 :=
    ((hu.map _).ne_zero)
  have hordeq := congrArg (fun z => S.ord z Q.genericPoint) hψ
  simp only at hordeq
  rw [Scheme.ord_mul (mul_ne_zero (pow_ne_zero _ hψa0) (pow_ne_zero _ hψf0)) (pow_ne_zero _ hψg0),
    Scheme.ord_mul (pow_ne_zero _ hψa0) (pow_ne_zero _ hψf0),
    MMP.CyclicChartDifferent.Aux.ord_pow' hψa0, MMP.CyclicChartDifferent.Aux.ord_pow' hψf0,
    MMP.CyclicChartDifferent.Aux.ord_pow' hψg0, Scheme.ord_mul (pow_ne_zero _ hψb0) hspr0,
    MMP.CyclicChartDifferent.Aux.ord_pow' hψb0, hspr,
    add_zero] at hordeq
  -- `ord_Q ρ = ord_Q b̄ + ord_Q ρ₀`
  have hρ0 : ρ ≠ 0 := MMP.CyclicChartDifferent.Aux.isPoincareResidue_ne_zero sM hX hdim j hT P hP τ
    hτ0 hτ ρ hρ Q
  set ρ₀ := ψ ((b⁻¹ : (M.presheaf.stalk _)ˣ) : M.presheaf.stalk (j (genericPoint S))) • ρ
    with hρ₀def
  have hρeq : ρ = ψ (b : M.presheaf.stalk _) • ρ₀ := by
    rw [hρ₀def, smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]
  have hρ₀0 : ρ₀ ≠ 0 := fun h => hρ0 (by rw [hρeq, h, smul_zero])
  have hρord : Q.ordForm ρ = S.ord (ψ (b : M.presheaf.stalk _)) Q.genericPoint + Q.ordForm ρ₀ := by
    conv_lhs => rw [hρeq]
    exact Q.ordForm_smul (sX := j ≫ sM) hdT hψb0 hρ₀0
  have hk0 : (k : ℚ) ≠ 0 := by positivity
  have hk'0 : (k' : ℚ) ≠ 0 := by positivity
  have hm'0 : (m' : ℚ) ≠ 0 := by positivity
  have hOa : (S.ord (ψ a') Q.genericPoint : ℚ) =
      ((m * k * k' * m' : ℕ) * (S.ord (ψ (b : M.presheaf.stalk _)) Q.genericPoint : ℚ) -
        (m * k' * m' : ℕ) * (S.ord (ψ cf) Q.genericPoint : ℚ) -
        (m * k : ℕ) * (S.ord (ψ cg) Q.genericPoint : ℚ)) / ((k * k' * m' : ℕ) : ℚ) := by
    rw [eq_div_iff (by positivity)]
    have := congrArg (fun z : ℤ => (z : ℚ)) hordeq
    push_cast at this ⊢
    linear_combination this
  rw [hOa, hBSQ, hρord]
  push_cast
  field_simp
  ring

/-- **The different of FA 16.6 is the residue different.** Let `j : S ⟶ M` be a closed immersion
of a normal variety onto a prime divisor `P` with `1 ≤ coeff_P B`, `M` a normal variety of
dimension `n + 1` over a field `k` of characteristic zero, and write `B - P = Δ⁺ - Δ⁻`. Suppose
`B_S = Diff_S(Δ⁺) - Δ⁻|_S`, with `Diff_S(Δ⁺)` the different of FA 16.6
(`MMP.Flips.IsDifferentDivisor`) and `Δ⁻` `ℚ`-Cartier, and let `τ` be a nonzero rational top
form on `M` with a simple pole along `P`, Poincaré residue `ρ = Res_S τ` and `div τ + B`
`ℚ`-Cartier. Then `(S, B_S)` is an adjunction step of `(M, B)`: `B_S` is the residue different.
The restriction of `div τ + Δ⁺ + P` is `div ρ + Diff_S(Δ⁺)`, and `Δ⁻|_S` is subtracted by
additivity of the pull-back. -/
theorem isAdjunctionStep_of_isDifferentDivisor [CharZero k]
    {sM : M ⟶ Spec (.of k)} [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] [LocallyOfFiniteType sM]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] [IsClosedImmersion j]
    {B : QDivisor M} {BS BS' : QDivisor S} (hT : IsNormalVariety k (j ≫ sM))
    {n : ℕ} (hdim : topologicalKrullDim M = n + 1)
    (P : Mori.PrimeDivisor M) (hP1 : 1 ≤ B.coeff P) (hP : Set.range j.base = (P.support : Set M))
    {d : ℕ} {ω ωXS : MMP.Flips.WeilDivisorialSubsheaf M} {DS : MMP.Flips.WeilDivisor M}
    (hH : MMP.Flips.IsDifferentDivisor j sM d ω ωXS DS
      (QDivisor.toQWeilDivisor (B - Finsupp.single P 1)⁺) (QDivisor.toQWeilDivisor BS'))
    (hgenΔ : ∀ Z : irreducibleComponents S,
      j (componentGenericPoint S Z) ∉ (B - Finsupp.single P 1)⁻.supp)
    (hΔq : (B - Finsupp.single P 1)⁻.IsQCartier)
    (hΔpb : (B - Finsupp.single P 1)⁻.IsPullback j hgenΔ (BS' - BS))
    (τ : RationalPluriForms sM (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sM) n 1) (hρ : IsPoincareResidue sM j n 1 τ ρ)
    (hD : (Divisor.toQDivisor (divisorOfForm τ) + B).IsQCartier) :
    IsAdjunctionStep sM B j BS := by
  letI : LocallyOfFiniteType (j ≫ sM) := hT.1.toLocallyOfFiniteType
  refine ⟨hT, P, hP1, hP, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, n, hH.1.isNormalVariety, hdim, τ, hτ0, hτ, hD, ρ, hρ, ?_⟩
  have hjT : j (genericPoint S) = P.genericPoint := genericPoint_eq_of_range_eq hP
  obtain ⟨-, -, -, -, -, -, -, hBP, -⟩ :=
    exists_coeff_eq_of_isDifferentDivisor hT hdim P hP1 hP hH τ hτ0 hτ ρ hρ hjT
  obtain ⟨hgenP, hpbP⟩ :=
    isPullback_divisorOfForm_add_posPart_of_isPoincareResidue hT hdim P hP1 hP hH τ hτ0 hτ ρ hρ
  set G := Divisor.toQDivisor (divisorOfForm τ) + B with hGdef
  have hG : G + (B - Finsupp.single P 1)⁻ =
      Divisor.toQDivisor (divisorOfForm τ) + ((B - Finsupp.single P 1)⁺ + Finsupp.single P 1) := by
    have key : ∀ A C : QDivisor M, A⁺ - A⁻ = A → B = A + C → B + A⁻ = A⁺ + C := by
      intro A C h1 h2
      calc B + A⁻ = A⁺ - A⁻ + C + A⁻ := by rw [h1, h2]
        _ = A⁺ + C := by abel
    rw [hGdef, add_assoc, key _ _ (posPart_sub_negPart _) (sub_add_cancel _ _).symm]
  have hgenG : ∀ Z : irreducibleComponents S, j (componentGenericPoint S Z) ∉ G.supp :=
    notMem_supp_of_coeff_eq_zero hjT (by
      rw [hGdef, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτ,
        hBP]
      norm_num)
  have hpb : ∀ h, (G + (B - Finsupp.single P 1)⁻).IsPullback j h
      (Divisor.toQDivisor (divisorOfForm ρ) + BS') := by
    rw [hG]; exact fun _ => hpbP
  have hgen' : ∀ Z : irreducibleComponents S,
      j (componentGenericPoint S Z) ∉ (G + (B - Finsupp.single P 1)⁻).supp := by
    rwa [hG]
  have hR := QDivisor.isPullback_pullback hD hgenG
  have huniq := ((hD.add hΔq).existsUnique_isPullback hgen').unique (hpb hgen')
    (isPullback_add_of_isQCartier hD hΔq hR hΔpb hgen')
  refine ⟨hgenG, ?_⟩
  convert hR using 1
  calc Divisor.toQDivisor (divisorOfForm ρ) + BS
      = Divisor.toQDivisor (divisorOfForm ρ) + BS' - (BS' - BS) := by abel
    _ = G.pullback hD hgenG := by rw [huniq]; abel

/-- **The reduced boundary component of an adjunction step has coefficient one.** The support
condition of the restriction `(div τ + B)|_S`, with `ord_P τ = -1`, says `coeff_P B = 1`. -/
theorem IsAdjunctionStep.coeff_eq_one {sM : M ⟶ Spec (.of k)} {B : QDivisor M}
    {BS : QDivisor S} (hS : IsAdjunctionStep sM B j BS) {P : Mori.PrimeDivisor M}
    (hP : Set.range j.base = (P.support : Set M)) : B.coeff P = 1 := by
  obtain ⟨-, P', -, hP', _, _, _, _, _, _, _, _, _, _, _, n, -, -, τ, -, hτ, -, ρ, -, hgen,
    -⟩ := hS
  have hjT : j (genericPoint S) = P.genericPoint := genericPoint_eq_of_range_eq hP
  obtain rfl : P = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hjT.symm.trans (genericPoint_eq_of_range_eq hP'))
  have hc0 : (Divisor.toQDivisor (divisorOfForm τ) + B).coeff P = 0 := by
    by_contra hne
    obtain ⟨ZT⟩ : Nonempty (irreducibleComponents S) :=
      ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
    refine hgen ZT ?_
    rw [componentGenericPoint_eq_genericPoint, hjT, DivisorWithCoeffs.mem_supp_iff]
    exact ⟨P, hne, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
  rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτ] at hc0
  push_cast at hc0
  linarith

/-- **Changing the form by a unit along `S`.** Let `j : S ⟶ M` be a closed immersion onto a
prime divisor `P`, `M` a normal variety of dimension `n + 1` over a field of characteristic zero,
and suppose the restriction of the `ℚ`-Cartier divisor `div τ₀ + B` to `S` is `div ρ₀ + B_S`.
For a unit `b` of `𝒪_{M,P}`, the restriction of `div(b τ₀) + B` is `div(b̄ ρ₀) + B_S`, `b̄` the
restriction of `b` to `S`: `div(b τ₀) + B = (div τ₀ + B) + div b`, and the pull-back of the
principal divisor `div b` is `div b̄`. -/
private theorem isPullback_divisorOfForm_add_unit_smul [CharZero k]
    {sM : M ⟶ Spec (.of k)} [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M]
    [LocallyOfFiniteType sM] [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    [LocallyOfFiniteType (j ≫ sM)] [IsClosedImmersion j] {n : ℕ}
    (hdim : topologicalKrullDim M = n + 1) {P : Mori.PrimeDivisor M}
    (hjT : j (genericPoint S) = P.genericPoint)
    {B : QDivisor M} {BS : QDivisor S} {τ₀ : RationalPluriForms sM (n + 1) 1} (hτ₀0 : τ₀ ≠ 0)
    {ρ₀ : RationalPluriForms (j ≫ sM) n 1} (hρ₀0 : ∀ _ : Mori.PrimeDivisor S, ρ₀ ≠ 0)
    (hD₀ : (Divisor.toQDivisor (divisorOfForm τ₀) + B).IsQCartier)
    {hgen₀ : ∀ Z : irreducibleComponents S,
      j (componentGenericPoint S Z) ∉ (Divisor.toQDivisor (divisorOfForm τ₀) + B).supp}
    (hpb₀ : (Divisor.toQDivisor (divisorOfForm τ₀) + B).IsPullback j hgen₀
      (Divisor.toQDivisor (divisorOfForm ρ₀) + BS))
    (b : (M.presheaf.stalk (j (genericPoint S)))ˣ) {τ : RationalPluriForms sM (n + 1) 1}
    (hτb : τ = algebraMap _ M.functionField (b : M.presheaf.stalk (j (genericPoint S))) • τ₀)
    {ρ : RationalPluriForms (j ≫ sM) n 1}
    (hρb : ρ = (j.stalkMap (genericPoint S)).hom (b : M.presheaf.stalk (j (genericPoint S))) • ρ₀)
    (hgen : ∀ Z : irreducibleComponents S,
      j (componentGenericPoint S Z) ∉ (Divisor.toQDivisor (divisorOfForm τ) + B).supp) :
    (Divisor.toQDivisor (divisorOfForm τ) + B).IsPullback j hgen
      (Divisor.toQDivisor (divisorOfForm ρ) + BS) := by
  classical
  subst hτb hρb
  letI := functionFieldAlgebra sM
  letI := functionFieldAlgebra (j ≫ sM)
  have hd : (Algebra.trdeg k M.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sM) (by rw [hdim]; norm_cast)
  have hdT : (Algebra.trdeg k S.functionField).toNat = n := by
    have := MMP.CyclicChartDifferent.Aux.trdeg_add_one_of_eq_genericPoint (sY := sM) (j := j) P hjT
    omega
  set ψ := (j.stalkMap (genericPoint S)).hom
  set f := algebraMap _ M.functionField (b : M.presheaf.stalk (j (genericPoint S))) with hf
  have hf0 : f ≠ 0 := (b.isUnit.map _).ne_zero
  have hψ0 : ψ (b : M.presheaf.stalk (j (genericPoint S))) ≠ 0 := (b.isUnit.map ψ).ne_zero
  have hfP : M.ord f P.genericPoint = 0 := by
    have key : ∀ (x : M) (_ : x = P.genericPoint) (v : M.presheaf.stalk x), IsUnit v →
        M.ord (algebraMap _ M.functionField v) P.genericPoint = 0 := by
      rintro x rfl v hv; exact P.ord_algebraMap_of_isUnit hv
    exact key _ hjT _ b.isUnit
  obtain ⟨χ, hχ⟩ := exists_units_componentToFunctionField_eq hf0
  have hχE : ∀ E : Mori.PrimeDivisor M, E.ord χ = M.ord f E.genericPoint := fun E => by
    rw [MMP.Positivity.ord_eq_ord_componentToFunctionField, hχ]
  -- `div(b τ₀) + B = (div τ₀ + B) + div b`
  have hsum : Divisor.toQDivisor (divisorOfForm (f • τ₀)) + B =
      (Divisor.toQDivisor (divisorOfForm τ₀) + B) + Divisor.toQDivisor (principalDivisor χ) := by
    refine Finsupp.ext fun E => ?_
    change DivisorWithCoeffs.coeff _ E = DivisorWithCoeffs.coeff _ E
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm,
      coeff_principalDivisor]
    rw [E.ordForm_smul (sX := sM) hd hf0 hτ₀0, hχE]
    push_cast
    ring
  have hχgen : ∀ Z : irreducibleComponents S,
      j (componentGenericPoint S Z) ∉ (principalDivisor χ).supp := fun Z => by
    have := notMem_supp_of_coeff_eq_zero hjT (G := Divisor.toQDivisor (principalDivisor χ)) (by
      rw [Divisor.coeff_toQDivisor, coeff_principalDivisor, hχE, hfP]; rfl) Z
    rwa [Divisor.supp_toQDivisor] at this
  have hχgenQ : ∀ Z : irreducibleComponents S,
      j (componentGenericPoint S Z) ∉ (Divisor.toQDivisor (principalDivisor χ)).supp := fun Z => by
    rw [Divisor.supp_toQDivisor]; exact hχgen Z
  have hc := Divisor.isCartier_principalDivisor χ
  have hpχ := QDivisor.isPullback_toQDivisor hc hχgenQ (Divisor.isPullback_principalDivisor χ hχgen)
  have hgen' : ∀ Z : irreducibleComponents S, j (componentGenericPoint S Z) ∉
      ((Divisor.toQDivisor (divisorOfForm τ₀) + B) +
        Divisor.toQDivisor (principalDivisor χ)).supp := by
    rw [← hsum]; exact hgen
  have hadd := isPullback_add_of_isQCartier hD₀ (QDivisor.isQCartier_toQDivisor hc) hpb₀ hpχ hgen'
  -- the pull-back of `div b` is `div b̄`
  have hpull : ∀ Q : Mori.PrimeDivisor S, Q.ord (pullbackRationalFunction j χ hχgen) =
      S.ord (ψ (b : M.presheaf.stalk (j (genericPoint S)))) Q.genericPoint := by
    intro Q
    have hZU : j (componentGenericPoint S Q.component) ∈ (⊤ : M.Opens) := trivial
    have hloc := Divisor.isLocalEquation_principalDivisor χ ⊤
    have hcomp : Units.map (RationalFunctions.component S Q.component).toMonoidHom
        (pullbackRationalFunction j χ hχgen) =
          pullbackComponent j hχgen hloc Q.component hZU := by
      ext
      change ((RationalFunctions.unitsEquiv S (pullbackRationalFunction j χ hχgen))
        Q.component).val = _
      simp [pullbackRationalFunction]
    rw [PrimeDivisor.ord_eq_ordUnit, hcomp]
    obtain ⟨a, ha⟩ := hloc.exists_unit_stalk hZU (hχgen Q.component) (mem_pointComponent _)
    rw [pullbackComponent_eq hχgen hloc hZU (mem_pointComponent _) a ha,
      MMP.CyclicChartDifferent.Aux.ordUnit_eq_ord]
    obtain ⟨a', ha'1, ha'2⟩ := exists_stalkMap_eq_of_eq_genericPoint j
      (componentGenericPoint_eq_genericPoint Q.component) (a : M.presheaf.stalk _)
    have hψa : (MMP.Positivity.componentToFunctionField Q.component).hom
        ((Units.map (j.stalkMap (componentGenericPoint S Q.component)).hom.toMonoidHom a :
          (S.presheaf.stalk _)ˣ) : S.presheaf.stalk _) = ψ a' := ha'2
    rw [hψa]
    have ha'K : algebraMap _ M.functionField a' = f := by
      rw [ha'1, ← MMP.CyclicChartDifferent.Aux.componentToFunctionField_stalkSpecializes M
        (pointComponent (j (componentGenericPoint S Q.component)))
        ((isGenericPoint_componentGenericPoint M _).specializes (mem_pointComponent _))
        (a : M.presheaf.stalk (j (componentGenericPoint S Q.component)))]
      exact (congrArg (MMP.Positivity.componentToFunctionField _).hom ha).trans (hχ _)
    rw [IsFractionRing.injective (M.presheaf.stalk (j (genericPoint S))) M.functionField
      (ha'K.trans hf)]
  -- `div(b̄ ρ₀) + B_S = (div ρ₀ + B_S) + div b̄`
  have hRS : Divisor.toQDivisor (divisorOfForm (ψ (b : M.presheaf.stalk _) • ρ₀)) + BS =
      (Divisor.toQDivisor (divisorOfForm ρ₀) + BS) +
        Divisor.toQDivisor (principalDivisor (pullbackRationalFunction j χ hχgen)) := by
    refine Finsupp.ext fun Q => ?_
    change DivisorWithCoeffs.coeff _ Q = DivisorWithCoeffs.coeff _ Q
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm,
      coeff_principalDivisor]
    rw [Q.ordForm_smul (sX := j ≫ sM) hdT hψ0 (hρ₀0 Q), hpull]
    push_cast
    ring
  have key : ∀ (G : QDivisor M) (_ : G = (Divisor.toQDivisor (divisorOfForm τ₀) + B) +
      Divisor.toQDivisor (principalDivisor χ))
      (h : ∀ Z : irreducibleComponents S, j (componentGenericPoint S Z) ∉ G.supp),
      G.IsPullback j h ((Divisor.toQDivisor (divisorOfForm ρ₀) + BS) +
        Divisor.toQDivisor (principalDivisor (pullbackRationalFunction j χ hχgen))) := by
    rintro G rfl h
    exact hadd
  rw [hRS]
  exact key _ hsum hgen

/-- **The divisor of an adjunction step restricts the log canonical divisor along any residue**
(Kollár [SMMP, Def. 4.2]). Let `(S, B_S)` arise from `(M, B)` by one adjunction step
`j : S ⟶ M` onto the prime divisor `P` (`MMP.Fourfold.IsAdjunctionStep`), `M` a normal variety
of dimension `n + 1` over a field `k` of characteristic zero. Let `τ` be a nonzero rational top
form on `M` with a simple pole along `P` and `ρ = Res_S τ` its Poincaré residue. If `div τ + B` is
`ℚ`-Cartier, then `S` is not contained in its support and its restriction to `S` is
`div ρ + B_S`. The adjunction step gives this for one form `τ₀`; any other is `τ = b τ₀` for a unit
`b` along `P` (`MMP.Fourfold.IsPoincareResidue.exists_unit_smul`), with residue `b̄ Res_S τ₀`, and
the principal divisor `div b` restricts to `div b̄`. In particular `B_S` does not depend on the
form. -/
theorem IsAdjunctionStep.isPullback_divisorOfForm_add_of_isPoincareResidue [CharZero k]
    {sM : M ⟶ Spec (.of k)} [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] [LocallyOfFiniteType sM]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {B : QDivisor M} {BS : QDivisor S} (hS : IsAdjunctionStep sM B j BS)
    {n : ℕ} (hdim : topologicalKrullDim M = n + 1)
    (P : Mori.PrimeDivisor M) (hP : Set.range j.base = (P.support : Set M))
    (τ : RationalPluriForms sM (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sM) n 1) (hρ : IsPoincareResidue sM j n 1 τ ρ)
    (hD : (Divisor.toQDivisor (divisorOfForm τ) + B).IsQCartier) :
    letI : LocallyOfFiniteType (j ≫ sM) := hS.1.1.toLocallyOfFiniteType
    ∃ hgen : ∀ Z : irreducibleComponents S,
        j (componentGenericPoint S Z) ∉ (Divisor.toQDivisor (divisorOfForm τ) + B).supp,
      (Divisor.toQDivisor (divisorOfForm τ) + B).IsPullback j hgen
        (Divisor.toQDivisor (divisorOfForm ρ) + BS) := by
  letI : LocallyOfFiniteType (j ≫ sM) := hS.1.1.toLocallyOfFiniteType
  have hBP := hS.coeff_eq_one hP
  obtain ⟨hT, P', -, hP', hci, _, _, _, _, _, _, _, _, _, _, n', hM, hdim', τ₀, hτ₀0, hτ₀,
    hD₀, ρ₀, hρ₀, hgen₀, hpb₀⟩ := id hS
  have hjT : j (genericPoint S) = P.genericPoint := genericPoint_eq_of_range_eq hP
  obtain rfl : P = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hjT.symm.trans (genericPoint_eq_of_range_eq hP'))
  obtain rfl : n' = n := by
    have h := hdim'.symm.trans hdim
    have h' : ((n' + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      push_cast; exact h
    exact Nat.succ_injective (by exact_mod_cast h')
  obtain ⟨b, hτb, hρb⟩ :=
    IsPoincareResidue.exists_unit_smul hdim P hjT hτ0 hτ₀0 (hτ.trans hτ₀.symm) hρ
  have hρ₀eq := IsPoincareResidue.unique hS hρ₀ hρb
  have hρeq : ρ = (j.stalkMap (genericPoint S)).hom
      (b : M.presheaf.stalk (j (genericPoint S))) • ρ₀ := by
    rw [hρ₀eq, smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]
  have hgenG : ∀ Z : irreducibleComponents S,
      j (componentGenericPoint S Z) ∉ (Divisor.toQDivisor (divisorOfForm τ) + B).supp :=
    notMem_supp_of_coeff_eq_zero hjT (by
      rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτ, hBP]
      norm_num)
  exact ⟨hgenG, isPullback_divisorOfForm_add_unit_smul hdim hjT hτ₀0
    (fun Q => MMP.CyclicChartDifferent.Aux.isPoincareResidue_ne_zero sM hM hdim j hT P hP τ₀
      hτ₀0 hτ₀ ρ₀ hρ₀ Q) hD₀ hpb₀ b hτb hρeq hgenG⟩

/-- **The residue different is well defined.** Two adjunction steps of `(M, B)` along the same
closed immersion `j` have the same divisor: both restrict `div τ + B` to `div ρ + B_S` for one
form `τ` and its residue `ρ`, and pull-backs of `ℚ`-Cartier divisors are unique. -/
theorem IsAdjunctionStep.unique [CharZero k] {sM : M ⟶ Spec (.of k)} {B : QDivisor M}
    {BS BS' : QDivisor S} (hS : IsAdjunctionStep sM B j BS) (hS' : IsAdjunctionStep sM B j BS') :
    BS = BS' := by
  obtain ⟨-, P, -, hP, _, _, _, _, _, _, _, _, _, _, _, n, -, hdim, τ, hτ0, hτ, hD, ρ, hρ, hgen,
    hpb⟩ := id hS'
  obtain ⟨hgen', hpb'⟩ :=
    hS.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hP τ hτ0 hτ ρ hρ hD
  exact add_left_cancel ((hD.existsUnique_isPullback hgen).unique hpb' hpb)

end ResidueDifferent

end MMP.Fourfold
