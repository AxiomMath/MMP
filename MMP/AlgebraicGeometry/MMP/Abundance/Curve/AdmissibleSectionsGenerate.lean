module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.MMP.Abundance.Curve.PluriformRepresentationFinite
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.MMP.Abundance.NormalizedSectionDegreeZero
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Admissible generators on a finite collection of nef log curves

Let `(C_i, B_i)`, `i ∈ I`, be finitely many smooth connected proper curves over an algebraically
closed field `k` of characteristic zero, each with a `ℚ`-boundary `0 ≤ B_i ≤ 1` such that
`deg(K_{C_i} + B_i) ≥ 0`. Then in every sufficiently divisible positive even degree `m` the
admissible section systems (`MMP.Fourfold.admissibleSections`) — the tuples
`s_i ∈ H⁰(C_i, m(K_{C_i} + B_i))` whose residue restrictions are compatible under every crepant
birational identification between components and between their proper strata (the points of the
floors `⌊B_i⌋`), using even residues — generate every adjoint `𝒪_{C_i}(m(K_{C_i} + B_i))`.

The proof follows the source. Fix `d > 0` with every `d B_i` integral.

* *The setting.* A smooth proper curve is projective (it is its own smooth projective
  compactification); a curve pair with `0 ≤ B ≤ 1` is a pair and is dlt, every divisor on a
  normal curve being snc and every divisorial valuation being that of a point, of log
  discrepancy `1 - b_P ≥ 0`. A flag of strata has length at most one: the strata are the curve
  and the points of `⌊B⌋`, which are smooth zero-dimensional varieties without prime divisors.
* *Sections with prescribed floor residues.* A section is *normalized* if near every point `P`
  of `⌊B⌋` it is `(dz/z)^{⊗m}` up to order `1 - m`, for one (equivalently every) uniformizer
  `z`. In degree `12d`, normalized sections generating at any finite set of points exist: in
  positive degree from the surjectivity of `H⁰` onto the fibres at a point and the floor
  (FA 12.2.11, case (12.2.11.4)) and avoidance of finitely many subspaces, in degree zero from
  the nowhere vanishing sections of FA 12.2.11, case (12.2.11.3).
* *Invariance.* The crepant birational self-maps act on `H⁰(12d(K + B))` through a finite set
  of maps (`MMP.Fourfold.finite_range_pluriformPullback_and_isRelativelySemiample_of_curve`).
  The product of the translates of a normalized section over this finite image, raised to any
  power, is an invariant normalized section, generating wherever all the translates generate.
  Products are computed in the coordinates of a basis of the line of `1`-forms.
* *Admissibility.* On a curve the residue restriction of a normalized section to a point of the
  floor is the unit form. So a system whose entries are normalized and correspond under all
  crepant birational identifications of components is admissible. Such systems are obtained by
  pulling back invariant normalized sections on representatives of the crepant birational
  equivalence classes of the components.

## Main results

* `MMP.Fourfold.exists_admissibleSections_generatesOn_of_curve`: admissible generation for nef
  log curves.

## Implementation notes

The degree of a divisor on a curve `C` over an algebraically closed field is the sum of its
coefficients, every prime divisor of `C` being a `k`-rational point. The canonical divisor is
any `K_i` with `K_i.IsCanonicalDivisor (sX i) 1`. The source works over `ℂ`; the statement is
made over any algebraically closed field of characteristic zero, which is what the pairs of
`MMP.Mori.IsPair` require. "Generate" is local: every point of `C_i` has a neighbourhood on
which the `i`-th entry of some admissible system generates (`MMP.Mori.GeneratesOn`).

The source passes from preadmissible to admissible generators through orbit polynomials of a
finite monomial group acting on the whole preadmissible space. Here the invariant generators are
built directly: on each class representative the product of the translates of one normalized
section over the finite image of its crepant birational self-maps is invariant, and the other
components of the class receive its pull-backs along fixed crepant identifications. Generation at
a point is achieved by choosing the normalized section to generate at the finitely many points
corresponding to it under the representatives of the finite image. Normalization with residue
one makes every proper floor-stratum restriction the unit form, which is why no residue
restriction datum has to be constructed.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 12.2.9–12.2.11
-/

namespace MMP.Fourfold

universe u

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Flips
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Vanishing to a given order -/

section VanishesTo

/-- A rational form `τ` *vanishes to order `≥ a` along `Q`*: it is `0` or `ord_Q τ ≥ a`. -/
private def VanishesTo {k : Type u} [Field k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] {n : ℕ} (Q : MMP.Mori.PrimeDivisor C) (a : ℤ)
    (τ : RationalPluriForms sC 1 (n : ℕ)) : Prop :=
  τ = 0 ∨ a ≤ Q.ordForm τ

variable {k : Type u} [Field k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C]
  [IsLocallyNoetherian C] {n : ℕ} {Q : MMP.Mori.PrimeDivisor C} {a : ℤ}

private theorem VanishesTo.add [IsNormal C] {τ τ' : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (h' : VanishesTo Q a τ') : VanishesTo Q a (τ + τ') := by
  rcases h with h | h
  · rw [h, zero_add]; exact h'
  rcases h' with h' | h'
  · rw [h', add_zero]; exact Or.inr h
  by_cases h0 : τ + τ' = 0
  · exact Or.inl h0
  exact Or.inr ((le_min h h').trans (Q.min_ordForm_le_ordForm_add h0))

private theorem VanishesTo.neg {τ : RationalPluriForms sC 1 (n : ℕ)} (h : VanishesTo Q a τ) :
    VanishesTo Q a (-τ) := by
  rcases h with h | h
  · rw [h, neg_zero]; exact Or.inl rfl
  · exact Or.inr (by rwa [PrimeDivisor.ordForm_neg])

private theorem VanishesTo.sub [IsNormal C] {τ τ' : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (h' : VanishesTo Q a τ') : VanishesTo Q a (τ - τ') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

private theorem VanishesTo.const_smul {τ : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (c : k) : VanishesTo Q a (c • τ) := by
  by_cases hc : c = 0
  · rw [hc, zero_smul]; exact Or.inl rfl
  rcases h with h | h
  · rw [h, smul_zero]; exact Or.inl rfl
  · exact Or.inr (by rwa [MMP.Fourfold.ordForm_const_smul Q hc])

private theorem VanishesTo.mono {b : ℤ} {τ : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (hb : b ≤ a) : VanishesTo Q b τ :=
  h.imp id hb.trans

/-- If `τ - ρ` vanishes to order `> ord_Q ρ` at `Q`, then `τ` has the order of `ρ` at `Q`. -/
private theorem ordForm_eq_of_vanishesTo_sub [IsNormal C] {τ ρ : RationalPluriForms sC 1 (n : ℕ)}
    (hρ : ρ ≠ 0)
    (h : VanishesTo Q (Q.ordForm ρ + 1) (τ - ρ)) : τ ≠ 0 ∧ Q.ordForm τ = Q.ordForm ρ := by
  by_cases hne : τ - ρ = 0
  · rw [sub_eq_zero] at hne; subst hne; exact ⟨hρ, rfl⟩
  have h1 := h.resolve_left hne
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, zero_sub, PrimeDivisor.ordForm_neg] at h1
    omega
  refine ⟨hτ0, le_antisymm ?_ ?_⟩
  · by_contra hlt
    push Not at hlt
    have hsum : τ + -(τ - ρ) = ρ := by abel
    have := Q.min_ordForm_le_ordForm_add (τ := τ) (τ' := -(τ - ρ)) (by rw [hsum]; exact hρ)
    rw [hsum, PrimeDivisor.ordForm_neg] at this
    omega
  · have hsum : (τ - ρ) + ρ = τ := by abel
    have := Q.min_ordForm_le_ordForm_add (τ := τ - ρ) (τ' := ρ) (by rw [hsum]; exact hτ0)
    rw [hsum] at this
    omega

end VanishesTo

/-- Membership in the global sections `H⁰(C, 𝒪(nK + E))` is the order condition at every prime
divisor. -/
private theorem mem_pluricanonicalSections_top_iff {k : Type u} [Field k] {C : Scheme.{u}}
    {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] {n : ℕ}
    {E : Divisor C} {τ : RationalPluriForms sC 1 (n : ℕ)} :
    τ ∈ pluricanonicalSections sC 1 (n : ℕ) E ⊤ ↔
      ∀ Q : MMP.Mori.PrimeDivisor C, VanishesTo Q (-E.coeff Q) τ := by
  have htop : (⊤ : C.Opens) ≠ ⊥ := by
    intro h
    have hx : (Nonempty.some (inferInstance : Nonempty C)) ∈ (⊤ : C.Opens) := trivial
    rw [h] at hx
    exact hx
  rw [mem_pluricanonicalSections_of_ne_bot htop]
  refine ⟨fun h Q => ?_, fun h Q _ hτ => ?_⟩
  · by_cases hτ : τ = 0
    · exact Or.inl hτ
    · refine Or.inr ?_
      have := h Q ⟨Q.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
        trivial⟩ hτ
      omega
  · rcases h Q with h | h
    · exact (hτ h).elim
    · omega

/-- On a curve, the rational `m`-canonical forms are a line over `k(C)`: every form is a multiple
of a given nonzero one. -/
private theorem exists_eq_smul_of_ne_zero {k : Type u} [Field k] [PerfectField k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    [LocallyOfFiniteType sC] (hdim : topologicalKrullDim C = 1) {m : ℤ}
    (Q : MMP.Mori.PrimeDivisor C) {u : RationalPluriForms sC 1 m} (hu : u ≠ 0)
    (w : RationalPluriForms sC 1 m) : ∃ h : C.functionField, w = h • u := by
  let := stalkAlgebra sC Q.genericPoint
  let := functionFieldAlgebra sC
  have := isScalarTower_stalk_functionField sC Q.genericPoint
  obtain ⟨σ, hσ, h0⟩ := Q.exists_topForms_generator_of_topologicalKrullDim_eq (sX := sC) (d := 1)
    (by rw [hdim]; rfl)
  let B := ZTensorPower.basis (topFormsBasis Q.localRing hσ h0) m
  have hu' := basis_unit_repr_smul B u
  have hw' := basis_unit_repr_smul B w
  have hru : B.repr u () ≠ 0 := by
    intro h
    rw [h, zero_smul] at hu'
    exact hu hu'.symm
  refine ⟨B.repr w () / B.repr u (), ?_⟩
  have key : (B.repr w () / B.repr u ()) • (B.repr u () • B ()) = B.repr w () • B () := by
    rw [smul_smul, div_mul_cancel₀ _ hru]
  rw [hu'] at key
  exact hw'.symm.trans key.symm

/-! ### Degree zero curves of genus zero -/

/-- The degree of a `ℚ`-divisor on a normal locally Noetherian integral scheme agrees with the
degree of its `ℚ`-Weil divisor. -/
private theorem sum_toQWeilDivisor {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C]
    [IsNormal C] (Δ : QDivisor C) :
    (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).sum (fun _ a => a) = Δ.sum (fun _ a => a) :=
  Finsupp.sum_subtypeDomain_index (h := fun _ a => a)
    fun Γ _ => ⟨inferInstance, Γ.isDiscreteValuationRing_localRing⟩

private theorem eq_zero_of_nonneg_of_sum_eq_zero {α : Type*} {D : α →₀ ℤ} (h0 : 0 ≤ D)
    (hs : (D.sum fun _ a => a) = 0) : D = 0 := by
  classical
  ext P
  by_cases hP : P ∈ D.support
  · simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun Q _ => h0 Q)).1 hs P hP
  · exact Finsupp.notMem_support_iff.1 hP

/-- The coheight of a point is at most the dimension of the scheme. -/
private theorem coheight_le_of_topologicalKrullDim_eq {X : Scheme.{u}} {n : ℕ∞}
    (h : topologicalKrullDim X = n) (x : X) : Order.coheight x ≤ n := by
  have h2 : ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
    rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X]
    exact le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, h] at h2
  exact_mod_cast h2

/-- The generic point of a prime divisor is not the generic point of the scheme. -/
private theorem primeDivisor_genericPoint_ne_genericPoint {C : Scheme.{u}} [IsIntegral C]
    (P : MMP.Mori.PrimeDivisor C) : P.genericPoint ≠ genericPoint C := fun h => by
  have h1 := P.coheight_genericPoint
  rw [h, Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec C).specializes trivial] at h1
  exact zero_ne_one h1

/-- The generic point of a prime divisor of a one-dimensional integral scheme is closed. -/
private theorem isClosed_singleton_genericPoint {C : Scheme.{u}} [IsIntegral C]
    (hdim : topologicalKrullDim C = 1) (P : MMP.Mori.PrimeDivisor C) :
    IsClosed ({P.genericPoint} : Set C) :=
  Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint C hdim
    (primeDivisor_genericPoint_ne_genericPoint P)

/-- `ord(w⁻¹) = -ord(w)`. -/
private theorem ord_inv' {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C]
    {w : C.functionField} (hw : w ≠ 0) (x : C) : C.ord w⁻¹ x = -C.ord w x := by
  rw [← zpow_neg_one, ord_zpow _ hw]
  ring

section LogDiscrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Every divisor over a normal curve has the valuation of a prime divisor of the curve. -/
public theorem exists_primeDivisor_valuation_eq_of_curve (hvar : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 1) (D : DivisorOver k sX) :
    ∃ P : Mori.PrimeDivisor X, D.valuation = (DivisorOver.ofPrimeDivisor k hvar P).valuation := by
  by_contra h
  push Not at h
  have h2 := (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hvar D).mpr h
  rw [MMP.Positivity.DivisorOver.codimension_center] at h2
  have h3 : (2 : ℕ∞) ≤ 1 := h2.trans (coheight_le_of_topologicalKrullDim_eq hdim _)
  norm_num at h3

/-- The log discrepancy of a prime divisor `P` of a curve, as the divisor `(X, 𝟙, P)` over it,
is `1 - coeff_P B`. -/
public theorem isLogDiscrepancy_ofPrimeDivisor [IsAlgClosed k] (hvar : IsNormalVariety k sX)
    {B : QDivisor X} (hpair : MMP.Mori.IsPair sX B) (P : Mori.PrimeDivisor X) :
    ∃ n : ℕ, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      (DivisorOver.ofPrimeDivisor k hvar P) (1 - (B.coeff P : ℝ)) := by
  obtain ⟨-, n, K, hK, -⟩ := id hpair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK
    (DivisorOver.ofPrimeDivisor k hvar P)
  have ha' := IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hvar ha
  have hp : IsProper (DivisorOver.ofPrimeDivisor k hvar P).f := inferInstanceAs (IsProper (𝟙 X))
  refine ⟨n, ?_⟩
  have := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp
  rw [ha'] at this
  convert this using 1
  push_cast
  ring

/-- **Divisorial log discrepancies of a curve pair**: a valuation `v` has log discrepancy `a`
with respect to `(X, B)` exactly when `v = ord_P` for a prime divisor `P` and `a = 1 - b_P`. -/
public theorem hasLogDiscrepancy_iff_of_curve [IsAlgClosed k] (hvar : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 1) {B : QDivisor X} (hpair : MMP.Mori.IsPair sX B)
    (v : Valuation X.functionField ℤᵐ⁰) (a : ℝ) :
    HasLogDiscrepancy sX B v a ↔ ∃ P : Mori.PrimeDivisor X,
      v = (DivisorOver.ofPrimeDivisor k hvar P).valuation ∧ a = 1 - (B.coeff P : ℝ) := by
  constructor
  · rintro ⟨n, D, rfl, hD⟩
    obtain ⟨P, hP⟩ := exists_primeDivisor_valuation_eq_of_curve hvar hdim D
    obtain ⟨n₀, h₀⟩ := isLogDiscrepancy_ofPrimeDivisor hvar hpair P
    exact ⟨P, hP, MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD h₀ hP⟩
  · rintro ⟨P, rfl, rfl⟩
    obtain ⟨n₀, h₀⟩ := isLogDiscrepancy_ofPrimeDivisor hvar hpair P
    exact ⟨n₀, _, rfl, h₀⟩

end LogDiscrepancy

section Crepant

variable {k : Type u} [Field k] {X X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- The valuation of a prime divisor `P`, as the divisor `(X, 𝟙, P)` over `X`, is
`exp (-ord_P)`. -/
public theorem valuation_ofPrimeDivisor_apply (hvar : IsNormalVariety k sX)
    (P : Mori.PrimeDivisor X) {g : X.functionField} (hg : g ≠ 0) :
    (DivisorOver.ofPrimeDivisor k hvar P).valuation g = WithZero.exp (-X.ord g P.genericPoint) := by
  change P.divisorialValuation (functionFieldMap (𝟙 X) g) = _
  rw [functionFieldMap_id_apply, PrimeDivisor.divisorialValuation_eq_exp_neg_ord P hg]

/-- **Crepant maps of curve pairs match points.** A crepant birational map `σ : (X, B) ⇢ (X', B')`
of curve pairs sends every prime divisor `P` of `X` to a prime divisor `Q` of `X'` with
`ord_P ∘ σ = ord_Q` and `b_P = b'_Q`. -/
private theorem exists_primeDivisor_of_isCrepantBirationalMap [IsAlgClosed k]
    (hvar : IsNormalVariety k sX)
    (hvar' : IsNormalVariety k sX') (hdim' : topologicalKrullDim X' = 1) {B : QDivisor X}
    {B' : QDivisor X'} (hpair : MMP.Mori.IsPair sX B) (hpair' : MMP.Mori.IsPair sX' B')
    {σ : FunctionFieldEquiv sX sX'} (hσ : IsCrepantBirationalMap sX sX' B B' σ)
    (P : Mori.PrimeDivisor X) :
    ∃ Q : Mori.PrimeDivisor X', (∀ f : X'.functionField, f ≠ 0 →
      X.ord (σ f) P.genericPoint = X'.ord f Q.genericPoint) ∧ B.coeff P = B'.coeff Q := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra sX'
  obtain ⟨n₀, h₀⟩ := isLogDiscrepancy_ofPrimeDivisor hvar hpair P
  have h := (hσ (DivisorOver.ofPrimeDivisor k hvar P).valuation (1 - (B.coeff P : ℝ))).mp
    ⟨n₀, _, rfl, h₀⟩
  obtain ⟨Q, hQ, ha⟩ := (hasLogDiscrepancy_iff_of_curve hvar' hdim' hpair' _ _).mp h
  refine ⟨Q, fun f hf => ?_, by exact_mod_cast (by linarith : (B.coeff P : ℝ) = B'.coeff Q)⟩
  have h1 := congrArg (fun v : Valuation X'.functionField ℤᵐ⁰ => v f) hQ
  have hσf : σ f ≠ 0 := (map_ne_zero_iff _ σ.injective).2 hf
  simp only [Valuation.comap_apply] at h1
  change (DivisorOver.ofPrimeDivisor k hvar P).valuation (σ f) = _ at h1
  rw [valuation_ofPrimeDivisor_apply hvar P hσf, valuation_ofPrimeDivisor_apply hvar' Q hf]
    at h1
  have := WithZero.exp_injective h1
  omega

end Crepant

section Forms

variable {k : Type u} [Field k] {X X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- Every prime divisor of a normal integral scheme has a uniformizer in the function field. -/
private theorem exists_ord_eq_one (Q : Mori.PrimeDivisor X) :
    ∃ z : X.functionField, X.ord z Q.genericPoint = 1 := by
  have := Q.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Q.localRing
  have hne : algebraMap Q.localRing X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hϖ.ne_zero
  refine ⟨algebraMap Q.localRing X.functionField ϖ, ?_⟩
  have h := Q.divisorialValuation_algebraMap_of_irreducible hϖ
  rw [Q.divisorialValuation_eq_exp_neg_ord hne] at h
  have := WithZero.exp_injective h
  omega

/-- `(dz/z)^{⊗m}` for a uniformizer `z` at `P` is nonzero of order `-m` along `P`. -/
private theorem ordForm_dlogPow [IsAlgClosed k] (hvar : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 1) (P : Mori.PrimeDivisor X) {z : X.functionField}
    (hz : X.ord z P.genericPoint = 1) (m : ℕ) :
    Flips.dlogPow sX z m ≠ 0 ∧ P.ordForm (Flips.dlogPow sX z m) = -m := by
  obtain ⟨h1, h2⟩ := ordForm_dlogPow_one_of_ord_eq_one hvar hdim P z hz
  obtain ⟨h3, h4⟩ := ordForm_dlogPow_eq_mul hvar hdim z h1 m
  exact ⟨h3, by rw [h4 P, h2]; ring⟩

omit [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian X']
  [IsNormal X'] in
/-- Pluriform pull-back is semilinear over the field homomorphism. -/
private theorem pluriformPullback_smul' (φ : FunctionFieldHom sX sX') {d : ℕ} {m : ℤ}
    (f : X'.functionField) (τ : RationalPluriForms sX' d m) :
    pluriformPullback sX sX' φ d m (f • τ) =
      (letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX; φ f) •
        pluriformPullback sX sX' φ d m τ := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  exact pullbackForms_smul (K := X'.functionField) (K' := X.functionField) f τ

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A nonzero `1`-form on a curve spans the line of `1`-forms. -/
private theorem span_singleton_eq_top_of_ne_zero [IsAlgClosed k] [LocallyOfFiniteType sX]
    (hdim : topologicalKrullDim X = 1)
    {ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^1 Ω[X.functionField⁄k]}
    (hω : ω ≠ 0) : Submodule.span X.functionField {ω} = ⊤ := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) (d := 1) (by exact_mod_cast hdim)
  have hc := basis_unit_repr_smul b ω
  have hc0 : b.repr ω () ≠ 0 := fun h => hω (by rw [← hc, h, zero_smul])
  rw [← hc, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc0)]
  have := b.span_eq
  rwa [Set.range_unique] at this

omit [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian X'] [IsNormal X'] in
/-- **Pull-back of `(dz/z)^{⊗m}`**: `φ^*(dz/z)^{⊗m} = (d φz/φz)^{⊗m}`. -/
private theorem pluriformPullback_dlogPow [IsAlgClosed k] [CharZero k] (hvar : IsNormalVariety k sX)
    (hvar' : IsNormalVariety k sX') (hdim : topologicalKrullDim X = 1)
    (hdim' : topologicalKrullDim X' = 1) (φ : FunctionFieldHom sX sX') {z : X'.functionField}
    (hz : Flips.dlogPow sX' z 1 ≠ 0) (m : ℕ) :
    pluriformPullback sX sX' φ 1 m (Flips.dlogPow sX' z m) = Flips.dlogPow sX (φ z) m := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hvar.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hvar'.1.toLocallyOfFiniteType
  set ω : ⋀[X'.functionField]^1 Ω[X'.functionField⁄k] := z⁻¹ •
    exteriorPower.ιMulti X'.functionField 1 fun _ => KaehlerDifferential.D k X'.functionField z
    with hωdef
  have hω0 : ω ≠ 0 := by
    intro h
    apply hz
    change (PiTensorProduct.tprod X'.functionField fun _ : Fin 1 => ω) = 0
    rw [h]
    exact MultilinearMap.map_coord_zero _ (0 : Fin 1) rfl
  have hgen := isPullbackGenerator_functionFieldHom (sX := sX) (sX' := sX') (d := 1)
    (by exact_mod_cast hdim) (by exact_mod_cast hdim') φ
    (span_singleton_eq_top_of_ne_zero hdim' hω0) hω0
  have h := pluriformPullback_smul_formPow φ hgen m 1
  rw [one_smul, map_one, one_smul] at h
  change pluriformPullback sX sX' φ 1 m (formPow ω m) = _
  rw [h]
  unfold formPow Flips.dlogPow
  congr 2
  funext _
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  rw [hωdef, map_smul, topFormsMap_ιMulti]
  simp only [KaehlerDifferential.map_D]
  rw [← algebraMap_smul X.functionField z⁻¹, map_inv₀]
  rfl

/-- **Pull-back preserves orders** along corresponding prime divisors of curves. -/
private theorem ordForm_pluriformPullback [IsAlgClosed k] [CharZero k] (hvar : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 1)
    (hvar' : IsNormalVariety k sX')
    (hdim' : topologicalKrullDim X' = 1) (φ : FunctionFieldHom sX sX')
    {P : Mori.PrimeDivisor X} {Q : Mori.PrimeDivisor X'}
    (hPQ : ∀ f : X'.functionField, f ≠ 0 → X.ord (φ f) P.genericPoint = X'.ord f Q.genericPoint)
    {m : ℕ} {τ : RationalPluriForms sX' 1 (m : ℕ)} (hτ : τ ≠ 0) :
    pluriformPullback sX sX' φ 1 m τ ≠ 0 ∧
      P.ordForm (pluriformPullback sX sX' φ 1 m τ) = Q.ordForm τ := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hvar.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hvar'.1.toLocallyOfFiniteType
  have hd : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  have hd' : topologicalKrullDim X' = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim'
  obtain ⟨z, hz⟩ := exists_ord_eq_one Q
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  obtain ⟨hD0, hDord⟩ := ordForm_dlogPow hvar' hdim' Q hz m
  obtain ⟨hD1, -⟩ := ordForm_dlogPow hvar' hdim' Q hz 1
  have hφz : X.ord (φ z) P.genericPoint = 1 := by rw [hPQ z hz0, hz]
  obtain ⟨hE0, hEord⟩ := ordForm_dlogPow hvar hdim P hφz m
  obtain ⟨h, rfl⟩ := exists_eq_smul_of_ne_zero hdim' Q hD0 τ
  have hh : h ≠ 0 := by rintro rfl; exact hτ (zero_smul _ _)
  have hφh : φ h ≠ 0 := fun h0 => hh (by simpa using h0)
  rw [pluriformPullback_smul', pluriformPullback_dlogPow hvar hvar' hdim hdim' φ hD1]
  refine ⟨smul_ne_zero hφh hE0, ?_⟩
  rw [P.ordForm_smul_of_topologicalKrullDim_eq hd hφh hE0, hEord, hPQ h hh,
    Q.ordForm_smul_of_topologicalKrullDim_eq hd' hh hD0, hDord]

/-- **Pull-back preserves orders** along corresponding prime divisors of curves: if
`ord_P ∘ φ = ord_Q`, then `ord_P(φ^*τ) = ord_Q(τ)`, in the form of the vanishing condition. -/
private theorem vanishesTo_pluriformPullback [IsAlgClosed k] [CharZero k]
    (hvar : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 1)
    (hvar' : IsNormalVariety k sX')
    (hdim' : topologicalKrullDim X' = 1) (φ : FunctionFieldHom sX sX')
    {P : Mori.PrimeDivisor X} {Q : Mori.PrimeDivisor X'}
    (hPQ : ∀ f : X'.functionField, f ≠ 0 → X.ord (φ f) P.genericPoint = X'.ord f Q.genericPoint)
    {m : ℕ} {a : ℤ} {τ : RationalPluriForms sX' 1 (m : ℕ)} (hτ : VanishesTo Q a τ) :
    VanishesTo P a (pluriformPullback sX sX' φ 1 m τ) := by
  rcases hτ with rfl | hτ
  · exact Or.inl (map_zero _)
  by_cases h0 : τ = 0
  · exact Or.inl (by rw [h0, map_zero])
  obtain ⟨-, h⟩ := ordForm_pluriformPullback hvar hdim hvar' hdim' φ hPQ h0
  exact Or.inr (h ▸ hτ)

end Forms

section Residue

variable {k : Type u} [Field k]

/-- The unit `0`-form `1^{⊗m}` of an integral scheme over `k`, the residue of `(dz/z)^{⊗m}`
at a point. -/
private noncomputable def unitForm {T : Scheme.{u}} (sT : T ⟶ Spec (.of k)) [IsIntegral T]
    (m : ℕ) : RationalPluriForms sT 0 m :=
  letI := functionFieldAlgebra sT
  (PiTensorProduct.tprod T.functionField fun _ : Fin m =>
      exteriorPower.ιMulti T.functionField 0 fun i => i.elim0 :
    TensorPower T.functionField m (⋀[T.functionField]^0 Ω[T.functionField⁄k]))

/-- `c • 1^{⊗m}` does not depend on the structure morphism beyond equality. -/
private theorem heq_smul_unitForm {T : Scheme.{u}} [IsIntegral T] {s s' : T ⟶ Spec (.of k)}
    (h : s = s') (c : k) (m : ℕ) : HEq (c • unitForm s m) (c • unitForm s' m) := by
  subst h; rfl

/-- **Pull-back of the unit form.** Along a homomorphism of function fields of
zero-dimensional varieties over a field of characteristic zero, `φ^* 1^{⊗m} = 1^{⊗m}`. -/
private theorem pluriformPullback_unitForm [CharZero k] {T T' : Scheme.{u}}
    {sT : T ⟶ Spec (.of k)} {sT' : T' ⟶ Spec (.of k)} [IsIntegral T] [IsIntegral T']
    [LocallyOfFiniteType sT] [LocallyOfFiniteType sT'] (hT : topologicalKrullDim T = 0)
    (hT' : topologicalKrullDim T' = 0) (φ : FunctionFieldHom sT sT') (m : ℕ) :
    pluriformPullback sT sT' φ 0 m (unitForm sT' m) = unitForm sT m := by
  let := functionFieldAlgebra sT'
  let := functionFieldAlgebra sT
  set ω : ⋀[T'.functionField]^0 Ω[T'.functionField⁄k] :=
    exteriorPower.ιMulti T'.functionField 0 fun i => i.elim0 with hωdef
  have hω0 : ω ≠ 0 := by
    intro h
    have := congrArg (exteriorPower.zeroEquiv T'.functionField _) h
    simp [ω] at this
  have hspan : Submodule.span T'.functionField {ω} = ⊤ := by
    rw [← exteriorPower.ιMulti_span T'.functionField 0 Ω[T'.functionField⁄k]]
    congr 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro rfl
      exact ⟨_, rfl⟩
    · rintro ⟨f, rfl⟩
      congr 1
      funext i
      exact i.elim0
  have hgen := isPullbackGenerator_functionFieldHom (sX := sT) (sX' := sT') (d := 0)
    (by exact_mod_cast hT) (by exact_mod_cast hT') φ hspan hω0
  have h := pluriformPullback_smul_formPow φ hgen m 1
  rw [one_smul, map_one, one_smul] at h
  change pluriformPullback sT sT' φ 0 m (formPow ω m) = _
  rw [h]
  let : Algebra T'.functionField T.functionField := φ.toRingHom.toAlgebra
  unfold formPow unitForm
  congr 2
  funext _
  rw [hωdef, topFormsMap_ιMulti]
  congr 1
  funext i
  exact i.elim0

variable {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y} {BY : QDivisor Y}
  {BT : QDivisor T}

/-- **The Poincaré residue of a normalized form.** Let `T ⊂ Y` be an adjunction step at the
prime divisor `P` of a normal curve `Y`, `z` a uniformizer at `P`, and `τ` an `m`-fold `1`-form
with `τ - c (dz/z)^{⊗m}` vanishing at `P`. Then `Res_T τ = c • 1^{⊗m}`. -/
private theorem isPoincareResidue_of_vanishesTo [IsAlgClosed k] (hvar : IsNormalVariety k sY)
    (hdim : topologicalKrullDim Y = 1) (hj : IsAdjunctionStep sY BY j BT)
    {P : Mori.PrimeDivisor Y} (hP : j (genericPoint T) = P.genericPoint) {z : Y.functionField}
    (hz : Y.ord z P.genericPoint = 1) {m : ℕ} (hD0 : Flips.dlogPow sY z m ≠ 0)
    (hDo : P.ordForm (Flips.dlogPow sY z m) = -m) (c : k)
    {τ : RationalPluriForms sY 1 m}
    (hτ : VanishesTo P (1 - m) (τ - c • Flips.dlogPow sY z m)) :
    IsPoincareResidue sY j 0 m τ (c • unitForm (j ≫ sY) m) := by
  classical
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  have : LocallyOfFiniteType sY := hvar.1.toLocallyOfFiniteType
  have hd : topologicalKrullDim Y = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  obtain ⟨-, -, -, -, hcoh, -⟩ := hj.stalk_facts
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  obtain ⟨htow, hsurj⟩ := hj.stalkMap_facts
  have hΓP : ∀ Γ : Mori.PrimeDivisor Y, j (genericPoint T) ∈ Γ.support → Γ = P := by
    intro Γ hΓ
    refine MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes ?_
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
    rw [← hP]
    exact specializes_iff_mem_closure.2 hΓ
  have hreg : ∀ f : Y.functionField, f ≠ 0 → 0 ≤ Y.ord f P.genericPoint →
      ∃ r : Y.presheaf.stalk (j (genericPoint T)), algebraMap _ Y.functionField r = f :=
    fun f hf h => MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg _ hf
      fun Γ hΓ => by rw [hΓP Γ hΓ]; exact h
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  obtain ⟨t, ht⟩ := hreg z hz0 (by omega)
  obtain ⟨h', hh'⟩ := exists_eq_smul_of_ne_zero hdim P hD0 (τ - c • Flips.dlogPow sY z m)
  have hmax : RingHom.ker (j.stalkMap (genericPoint T)).hom =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (j (genericPoint T))) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
  obtain ⟨g', hg'1, hg'2⟩ : ∃ g' : Y.presheaf.stalk (j (genericPoint T)),
      algebraMap _ Y.functionField g' = h' ∧ (j.stalkMap (genericPoint T)).hom g' = 0 := by
    by_cases h0 : h' = 0
    · exact ⟨0, by rw [map_zero, h0], map_zero _⟩
    rcases hτ with hτ | hτ
    · rw [hh'] at hτ; exact absurd hτ (smul_ne_zero h0 hD0)
    rw [hh', P.ordForm_smul_of_topologicalKrullDim_eq hd h0 hD0, hDo] at hτ
    obtain ⟨g', hg'⟩ := hreg h' h0 (by omega)
    refine ⟨g', hg', ?_⟩
    rw [← RingHom.mem_ker, hmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hne : algebraMap _ Y.functionField g' ≠ 0 := hg' ▸ h0
    have h1 : Y.ord (algebraMap _ Y.functionField g') (j (genericPoint T)) = 0 := by
      rw [Scheme.ord_eq_iff hcoh hne, ofAdd_zero]
      have : Ring.KrullDimLE 1 (Y.presheaf.stalk (j (genericPoint T))) :=
        krullDimLE_of_coheight_le hcoh.le
      exact Ring.ordFrac_of_isUnit hu
    rw [hg', hP] at h1
    omega
  refine ⟨t, algebraMap k _ c + g', fun i => i.elim0, ?_, ?_, ?_⟩
  · rw [ht, hP]; exact hz
  · have e1 : τ = (algebraMap k Y.functionField c + h') • Flips.dlogPow sY z m := by
      rw [add_smul, ← hh', ← RationalPluriForms.smul_def]; abel
    rw [e1, map_add, ← IsScalarTower.algebraMap_apply, hg'1]
    unfold Flips.dlogPow
    rw [← ht]
    congr 2
  · have e2 : (j.stalkMap (genericPoint T)).hom (algebraMap k _ c) =
        algebraMap k T.functionField c :=
      (IsScalarTower.algebraMap_apply k (Y.presheaf.stalk (j (genericPoint T))) T.functionField
        c).symm
    rw [map_add, hg'2, add_zero, e2, RationalPluriForms.smul_def]
    unfold unitForm
    congr 2

end Residue

section Admissible

variable {k : Type u} [Field k]

/-- A form `τ` of degree `m` on a curve is *normalized with residue `c`* along `B`: at every
point `P` with `b_P = 1` and for every uniformizer `z` at `P`, `τ - c (dz/z)^{⊗m}` vanishes at
`P`. -/
private def IsNormalized {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsLocallyNoetherian X] (B : QDivisor X) (m : ℕ) (c : k)
    (τ : RationalPluriForms sX 1 m) : Prop :=
  ∀ P : Mori.PrimeDivisor X, B.coeff P = 1 → ∀ z : X.functionField,
    X.ord z P.genericPoint = 1 → VanishesTo P (1 - m) (τ - c • Flips.dlogPow sX z m)

/-- An adjunction step of a pair with boundary `0 ≤ B ≤ 1` is at a prime divisor of
coefficient one. -/
private theorem exists_coeff_eq_one_of_isAdjunctionStep {Y T : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T]
    {j : T ⟶ Y} {BY : QDivisor Y} {BT : QDivisor T}
    (hB : ∀ P, 0 ≤ BY.coeff P ∧ BY.coeff P ≤ 1) (hj : IsAdjunctionStep sY BY j BT) :
    ∃ P : Mori.PrimeDivisor Y, j (genericPoint T) = P.genericPoint ∧ BY.coeff P = 1 := by
  obtain ⟨P', hP', -⟩ := hj.exists_primeDivisor
  obtain ⟨-, P, hfl, hrange, -⟩ := hj
  have hPP' : P = P' := by
    apply MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes
    have : P'.genericPoint ∈ (P.support : Set Y) := by rw [← hrange, ← hP']; exact ⟨_, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
    exact specializes_iff_mem_closure.2 this
  subst hPP'
  refine ⟨P, hP', ?_⟩
  exact le_antisymm (hB P).2 hfl

variable [CharZero k] {I : Type*} {X : I → Scheme.{u}} {sX : ∀ i, X i ⟶ Spec (.of k)}
  [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
  {B : ∀ i, QDivisor (X i)} {m : ℕ}

/-- **Residue restrictions of normalized sections.** On a curve pair with boundary `0 ≤ B ≤ 1`,
the residue restriction of a section normalized with residue `c` to a proper stratum (a point
of `⌊B⌋`) is `c • 1^{⊗m}`. -/
private theorem toFun_eq_smul_unitForm [IsAlgClosed k] (hvar : ∀ i, IsNormalVariety k (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 1)
    (hB : ∀ i P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) (R : ResidueRestriction sX B 1 m)
    (i : I) {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
    (F : StratumAdjunctionData (sX i) (B i) ι BS) (hF : 0 < F.length)
    (hS : topologicalKrullDim S = ((0 : ℕ) : WithBot ℕ∞)) {c : k}
    (s : logPluricanonicalSections (sX i) 1 m (B i))
    (hs : IsNormalized (sX i) (B i) m c (s : RationalPluriForms (sX i) 1 m)) :
    haveI := F.isIntegral_stratum
    R.toFun i F 0 s = c • unitForm (ι ≫ sX i) m := by
  have := F.isIntegral_stratum
  refine IsIteratedResidue.unique (R.isIteratedResidue i F 0 s hS) ?_
  have hlen : F.length = 1 := by have := F.dim_add_length (hdim i) hS; omega
  cases F with
  | refl hp => simp [StratumAdjunctionData.length] at hF
  | @step S₀ T ι₀ BS₀ F₀ j BT hj =>
    cases F₀ with
    | step => simp [StratumAdjunctionData.length] at hlen
    | refl hp =>
      have : IsIntegral S := hj.1.1.toIsIntegral
      refine IsIteratedResidue.of_rec _ ⟨cast (by rw [Category.id_comp])
        (s : RationalPluriForms (sX i) 1 m), ⟨rfl, cast_heq _ _⟩,
        c • unitForm (j ≫ 𝟙 (X i) ≫ sX i) m, ?_, heq_smul_unitForm (Category.assoc _ _ _) c m⟩
      have key : ∀ (s' : X i ⟶ Spec (.of k)) (h : sX i = s'), IsAdjunctionStep s' (B i) j BS →
          IsPoincareResidue s' j 0 m (cast (by rw [h]) (s : RationalPluriForms (sX i) 1 m))
            (c • unitForm (j ≫ s') m) := by
        intro s' h hj'
        subst h
        rw [cast_eq]
        obtain ⟨P, hP, hP1⟩ := exists_coeff_eq_one_of_isAdjunctionStep (hB i) hj'
        obtain ⟨z, hz⟩ := exists_ord_eq_one P
        obtain ⟨hD0, hDo⟩ := ordForm_dlogPow (hvar i) (hdim i) P hz m
        exact isPoincareResidue_of_vanishesTo (hvar i) (hdim i) hj' hP hz hD0 hDo c
          (hs P hP1 z hz)
      exact key _ (Category.id_comp _).symm hj

/-- **Admissibility on curves.** A section system on a finite collection of curve pairs with
boundaries `0 ≤ B_i ≤ 1` is admissible if its entries are normalized with a common residue `c`
and correspond under every crepant birational map between the components. -/
private theorem mem_admissibleSections_of_isNormalized [IsAlgClosed k]
    (hvar : ∀ i, IsNormalVariety k (sX i)) (hdim : ∀ i, topologicalKrullDim (X i) = 1)
    (hB : ∀ i P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) (R : ResidueRestriction sX B 1 m)
    {s : ∀ i, logPluricanonicalSections (sX i) 1 m (B i)} (c : k)
    (hnorm : ∀ i, IsNormalized (sX i) (B i) m c (s i : RationalPluriForms (sX i) 1 m))
    (hinv : ∀ (i i' : I) (σ : FunctionFieldEquiv (sX i) (sX i')),
      IsCrepantBirationalMap (sX i) (sX i') (B i) (B i') σ →
      pluriformPullback (sX i) (sX i') σ.toHom 1 m (s i') = s i) :
    s ∈ admissibleSections R := by
  intro i i' S S' ι ι' BS BS' F F' e _ _ hS hS' σ hσ
  have hF := F.dim_add_length (hdim i) hS
  have hF' := F'.dim_add_length (hdim i') hS'
  rcases Nat.eq_zero_or_pos F.length with h0 | h0 <;>
    rcases Nat.eq_zero_or_pos F'.length with h0' | h0'
  · cases F with
    | step => simp [StratumAdjunctionData.length] at h0
    | refl hp =>
      cases F' with
      | step => simp [StratumAdjunctionData.length] at h0'
      | refl hp' =>
        simp only [StratumAdjunctionData.length, add_zero] at hF
        subst hF
        have e1 := IsIteratedResidue.unique (R.isIteratedResidue i (.refl hp) 1 (s i) hS)
          (IsIteratedResidue.refl hp)
        have e2 := IsIteratedResidue.unique (R.isIteratedResidue i' (.refl hp') 1 (s i') hS')
          (IsIteratedResidue.refl hp')
        rw [e1, e2]
        have key : ∀ (s₁ : X i ⟶ Spec (.of k)) (s₂ : X i' ⟶ Spec (.of k)) (h₁ : sX i = s₁)
            (h₂ : sX i' = s₂) (σ : FunctionFieldEquiv s₁ s₂),
            IsCrepantBirationalMap s₁ s₂ (B i) (B i') σ →
            pluriformPullback s₁ s₂ σ.toHom 1 m
              (cast (congrArg (fun s => RationalPluriForms s 1 m) h₂)
                (s i' : RationalPluriForms (sX i') 1 m)) =
              cast (congrArg (fun s => RationalPluriForms s 1 m) h₁)
                (s i : RationalPluriForms (sX i) 1 m) := by
          intro s₁ s₂ h₁ h₂
          subst h₁ h₂
          exact hinv i i'
        exact key _ _ (Category.id_comp _).symm (Category.id_comp _).symm σ hσ
  · omega
  · omega
  · obtain rfl : e = 0 := by omega
    have := F.isIntegral_stratum
    have := F'.isIntegral_stratum
    have : LocallyOfFiniteType (ι ≫ sX i) := F.isNormalVariety.1.toLocallyOfFiniteType
    have : LocallyOfFiniteType (ι' ≫ sX i') := F'.isNormalVariety.1.toLocallyOfFiniteType
    rw [toFun_eq_smul_unitForm hvar hdim hB R i F h0 hS (s i) (hnorm i),
      toFun_eq_smul_unitForm hvar hdim hB R i' F' h0' hS' (s i') (hnorm i'), map_smul,
      pluriformPullback_unitForm (by exact_mod_cast hS) (by exact_mod_cast hS')]

end Admissible

/-! ### Valuations of elements close to one -/

section CloseToOne

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)

private theorem valuation_le_one_of_sub_one_lt_one {r : K} (hr : v (r - 1) < 1) : v r ≤ 1 := by
  have : r = (r - 1) + 1 := by ring
  rw [this]
  exact (v.map_add _ _).trans (max_le hr.le v.map_one.le)

private theorem valuation_mul_sub_one_lt_one {r r' : K} (hr : v (r - 1) < 1)
    (hr' : v (r' - 1) < 1) : v (r * r' - 1) < 1 := by
  have e : r * r' - 1 = r * (r' - 1) + (r - 1) := by ring
  rw [e]
  refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ hr)
  rw [v.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_le_one_of_sub_one_lt_one v hr)) hr'

private theorem valuation_prod_sub_one_lt_one {α : Type*} (s : Finset α) {r : α → K}
    (hr : ∀ A ∈ s, v (r A - 1) < 1) : v ((∏ A ∈ s, r A) - 1) < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert A s hA ih =>
    rw [Finset.prod_insert hA]
    exact valuation_mul_sub_one_lt_one v (hr A (Finset.mem_insert_self A s))
      (ih fun B hB => hr B (Finset.mem_insert_of_mem hB))

private theorem valuation_pow_sub_one_lt_one {h : K} (hh : v (h - 1) < 1) (n : ℕ) :
    v (h ^ n - 1) < 1 := by
  have := valuation_prod_sub_one_lt_one v (Finset.range n) (r := fun _ => h)
    (fun _ _ => hh)
  simpa using this

end CloseToOne

section OrdValuation

variable {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]

/-- `ord_P(g) ≥ 1` (or `g = 0`) exactly when the divisorial valuation of `g` is `< 1`. -/
private theorem valuation_lt_one_iff (P : Mori.PrimeDivisor C) (g : C.functionField) :
    P.divisorialValuation g < 1 ↔ g = 0 ∨ 1 ≤ C.ord g P.genericPoint := by
  by_cases hg : g = 0
  · subst hg; simp
  rw [P.divisorialValuation_eq_exp_neg_ord hg, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  simp only [hg, false_or]
  omega

/-- The order of a finite product of nonzero rational functions is the sum of the orders. -/
private theorem ord_prod {α : Type*} (s : Finset α) {f : α → C.functionField}
    (hf : ∀ A, f A ≠ 0) (x : C) : C.ord (∏ A ∈ s, f A) x = ∑ A ∈ s, C.ord (f A) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert A s hA ih =>
    rw [Finset.prod_insert hA, Finset.sum_insert hA,
      Scheme.ord_mul (hf A) (Finset.prod_ne_zero_iff.2 fun B _ => hf B), ih]

end OrdValuation

/-! ### Uniformizers and the forms `(dz/z)^{⊗n}` -/

section Uniformizer

variable {k : Type u} [Field k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
  [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]

/-- `ιMulti` in degree one is linear in its single argument. -/
private theorem ιMulti_one_add_smul {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (c d : K) (x y : M) :
    exteriorPower.ιMulti K 1 (fun _ : Fin 1 => c • x + d • y) =
      c • exteriorPower.ιMulti K 1 (fun _ : Fin 1 => x) +
        d • exteriorPower.ιMulti K 1 (fun _ : Fin 1 => y) := by
  have e : ∀ z : M, (fun _ : Fin 1 => z) = Function.update (fun _ : Fin 1 => x) 0 z := by
    intro z; funext i; rw [Subsingleton.elim i 0]; simp
  rw [e (c • x + d • y), AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
    AlternatingMap.map_update_smul, ← e, ← e]

/-- **Change of uniformizer.** For two uniformizers `z, w` at `P` there is `h` with
`ord_P(h - 1) ≥ 1` and `(dw/w)^{⊗n} = hⁿ (dz/z)^{⊗n}` for every `n`. -/
private theorem exists_dlogPow_eq_pow_smul [IsAlgClosed k] (hvar : IsNormalVariety k sC)
    (hdim : topologicalKrullDim C = 1) (P : Mori.PrimeDivisor C)
    {z w : C.functionField} (hz : C.ord z P.genericPoint = 1)
    (hw : C.ord w P.genericPoint = 1) :
    ∃ h : C.functionField, P.divisorialValuation (h - 1) < 1 ∧
      ∀ n : ℕ, dlogPow sC w n = h ^ n • dlogPow sC z n := by
  let := functionFieldAlgebra sC
  have : LocallyOfFiniteType sC := hvar.1.toLocallyOfFiniteType
  have hd : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  set u := w * z⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero hw0 (inv_ne_zero hz0)
  have huo : C.ord u P.genericPoint = 0 := by
    rw [hu, Scheme.ord_mul hw0 (inv_ne_zero hz0), ord_inv' hz0, hw, hz]; ring
  have hwu : w = u * z := by rw [hu, mul_assoc, inv_mul_cancel₀ hz0, mul_one]
  set ηz : ⋀[C.functionField]^1 Ω[C.functionField⁄k] := z⁻¹ • exteriorPower.ιMulti
    C.functionField 1 fun _ => KaehlerDifferential.D k C.functionField z with hηz
  set ηu : ⋀[C.functionField]^1 Ω[C.functionField⁄k] := exteriorPower.ιMulti
    C.functionField 1 fun _ => KaehlerDifferential.D k C.functionField u with hηu
  obtain ⟨hD1, hDo1⟩ := ordForm_dlogPow hvar hdim P hz 1
  have hηz0 : ηz ≠ 0 := by
    intro h; apply hD1
    change (PiTensorProduct.tprod C.functionField fun _ : Fin 1 => ηz) = 0
    rw [h]; exact MultilinearMap.map_coord_zero _ (0 : Fin 1) rfl
  obtain ⟨g, hg⟩ : ∃ g : C.functionField, g • ηz = ηu := by
    have hspan := span_singleton_eq_top_of_ne_zero hdim hηz0
    have hmem : ηu ∈ Submodule.span C.functionField {ηz} := by rw [hspan]; trivial
    exact Submodule.mem_span_singleton.1 hmem
  have hιz : exteriorPower.ιMulti C.functionField 1
      (fun _ => KaehlerDifferential.D k C.functionField z) = z • ηz := by
    rw [hηz, smul_smul, mul_inv_cancel₀ hz0, one_smul]
  clear_value ηz ηu
  have hηw : w⁻¹ • exteriorPower.ιMulti C.functionField 1
      (fun _ => KaehlerDifferential.D k C.functionField w) = (1 + u⁻¹ * g) • ηz := by
    have hDw : KaehlerDifferential.D k C.functionField w =
        u • KaehlerDifferential.D k C.functionField z +
          z • KaehlerDifferential.D k C.functionField u := by
      rw [hwu, Derivation.leibniz]
    have e : w⁻¹ • (u • (z • ηz) + z • (g • ηz)) = (1 + u⁻¹ * g) • ηz := by
      rw [smul_smul, smul_smul, ← add_smul, smul_smul]
      congr 1
      rw [hwu]
      field_simp
    rw [hDw, ιMulti_one_add_smul, hιz, ← hηu, ← hg]
    exact e
  refine ⟨1 + u⁻¹ * g, ?_, fun n => ?_⟩
  · rw [show 1 + u⁻¹ * g - 1 = u⁻¹ * g by ring, valuation_lt_one_iff]
    by_cases hg0 : g = 0
    · left; rw [hg0, mul_zero]
    right
    rw [Scheme.ord_mul (inv_ne_zero hu0) hg0, ord_inv' hu0, huo, neg_zero, zero_add]
    have h' : g • dlogPow sC z 1 = (PiTensorProduct.tprod C.functionField fun _ : Fin 1 =>
        exteriorPower.ιMulti C.functionField 1 fun _ =>
          KaehlerDifferential.D k C.functionField u : RationalPluriForms sC 1 (1 : ℕ)) := by
      rw [← hηu, ← hg, show (fun _ : Fin 1 => g • ηz) = fun i => (fun _ : Fin 1 => g) i •
        (fun _ : Fin 1 => ηz) i from rfl, MultilinearMap.map_smul_univ, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, pow_one]
      unfold dlogPow
      rw [hηz]
      rfl
    have h0 := zero_le_ordForm_d hvar hdim P u huo.ge _ h' (smul_ne_zero hg0 hD1)
    rw [P.ordForm_smul_of_topologicalKrullDim_eq hd hg0 hD1, hDo1] at h0
    push_cast at h0
    omega
  · unfold dlogPow
    simp only
    rw [hηw, show (fun _ : Fin n => (1 + u⁻¹ * g) • ηz) = fun i => (fun _ : Fin n =>
      (1 + u⁻¹ * g)) i • (fun _ : Fin n => ηz) i from rfl, MultilinearMap.map_smul_univ,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, hηz]
    rfl

/-- **Independence of the uniformizer.** For two uniformizers `z, w` at `P`,
`(dw/w)^{⊗n} - (dz/z)^{⊗n}` vanishes to order `1 - n` at `P`. -/
private theorem vanishesTo_dlogPow_sub [IsAlgClosed k] (hvar : IsNormalVariety k sC)
    (hdim : topologicalKrullDim C = 1) (P : Mori.PrimeDivisor C)
    {z w : C.functionField} (hz : C.ord z P.genericPoint = 1)
    (hw : C.ord w P.genericPoint = 1) (n : ℕ) :
    VanishesTo P (1 - n) (dlogPow sC w n - dlogPow sC z n) := by
  have : LocallyOfFiniteType sC := hvar.1.toLocallyOfFiniteType
  have hd : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  obtain ⟨h, hh, hpow⟩ := exists_dlogPow_eq_pow_smul hvar hdim P hz hw
  obtain ⟨hDn, hDon⟩ := ordForm_dlogPow hvar hdim P hz n
  rw [hpow n, show h ^ n • dlogPow sC z n - dlogPow sC z n = (h ^ n - 1) • dlogPow sC z n by
    rw [sub_smul, one_smul]]
  rcases (valuation_lt_one_iff P _).1 (valuation_pow_sub_one_lt_one _ hh n) with h0 | h1
  · left; rw [h0, zero_smul]
  · by_cases h0 : h ^ n - 1 = 0
    · left; rw [h0, zero_smul]
    right
    rw [P.ordForm_smul_of_topologicalKrullDim_eq hd h0 hDn, hDon]
    omega

/-- A section normalized along one uniformizer is normalized along every uniformizer. -/
private theorem vanishesTo_sub_dlogPow_of_vanishesTo [IsAlgClosed k] (hvar : IsNormalVariety k sC)
    (hdim : topologicalKrullDim C = 1) (P : Mori.PrimeDivisor C)
    {z w : C.functionField} (hz : C.ord z P.genericPoint = 1)
    (hw : C.ord w P.genericPoint = 1) {n : ℕ} {τ : RationalPluriForms sC 1 (n : ℕ)}
    (hτ : VanishesTo P (1 - n) (τ - dlogPow sC z n)) :
    VanishesTo P (1 - n) (τ - dlogPow sC w n) := by
  have := hτ.sub (vanishesTo_dlogPow_sub hvar hdim P hz hw n)
  rwa [show τ - dlogPow sC z n - (dlogPow sC w n - dlogPow sC z n) = τ - dlogPow sC w n by
    abel] at this

/-- **Normalized sections generate along the floor.** If `τ - (dz/z)^{⊗n}` vanishes to order
`1 - n` at `P`, then `τ ≠ 0` and `ord_P τ = -n`. -/
private theorem ordForm_eq_of_vanishesTo_sub_dlogPow [IsAlgClosed k] (hvar : IsNormalVariety k sC)
    (hdim : topologicalKrullDim C = 1) (P : Mori.PrimeDivisor C)
    {z : C.functionField} (hz : C.ord z P.genericPoint = 1) {n : ℕ}
    {τ : RationalPluriForms sC 1 (n : ℕ)} (hτ : VanishesTo P (1 - n) (τ - dlogPow sC z n)) :
    τ ≠ 0 ∧ P.ordForm τ = -n := by
  obtain ⟨hD0, hDo⟩ := ordForm_dlogPow hvar hdim P hz n
  rw [← hDo]
  exact ordForm_eq_of_vanishesTo_sub hD0 (hτ.mono (by omega))

end Uniformizer

/-! ### Crepant pull-back of sections between curve pairs -/

section CrepantPullback

variable {k : Type u} [Field k] [CharZero k] {X X' : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']

variable (hvar : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 1)
  (hvar' : IsNormalVariety k sX') (hdim' : topologicalKrullDim X' = 1)
  {B : QDivisor X} {B' : QDivisor X'} (hpair : MMP.Mori.IsPair sX B)
  (hpair' : MMP.Mori.IsPair sX' B') {σ : FunctionFieldEquiv sX sX'}
  (hσ : IsCrepantBirationalMap sX sX' B B' σ)

include hvar hdim hvar' hdim' hpair hpair' hσ

/-- Pull-back along a crepant birational map of curve pairs preserves `H⁰(m(K + B))`. -/
private theorem pluriformPullback_mem_logPluricanonicalSections [IsAlgClosed k] {m : ℕ}
    {τ : RationalPluriForms sX' 1 m} (hτ : τ ∈ logPluricanonicalSections sX' 1 m B') :
    pluriformPullback sX sX' σ.toHom 1 m τ ∈ logPluricanonicalSections sX 1 m B := by
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_top_iff] at hτ ⊢
  intro P
  obtain ⟨Q, hPQ, hB⟩ :=
    exists_primeDivisor_of_isCrepantBirationalMap hvar hvar' hdim' hpair hpair' hσ P
  have := vanishesTo_pluriformPullback hvar hdim hvar' hdim' σ.toHom hPQ (hτ Q)
  simpa [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, hB] using this

/-- Pull-back along a crepant birational map of curve pairs preserves normalized sections. -/
private theorem isNormalized_pluriformPullback [IsAlgClosed k] {m : ℕ} {c : k}
    {τ : RationalPluriForms sX' 1 m} (hτ : IsNormalized sX' B' m c τ) :
    IsNormalized sX B m c (pluriformPullback sX sX' σ.toHom 1 m τ) := by
  intro P hP z hz
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  obtain ⟨Q, hPQ, hB⟩ :=
    exists_primeDivisor_of_isCrepantBirationalMap hvar hvar' hdim' hpair hpair' hσ P
  set w := σ.symm z
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hw0 : w ≠ 0 := (map_ne_zero_iff _ σ.symm.injective).2 hz0
  have hσw : σ w = z := σ.apply_symm_apply z
  have hwQ : X'.ord w Q.genericPoint = 1 := by rw [← hPQ w hw0, hσw, hz]
  have h := hτ Q (by rw [← hB, hP]) w hwQ
  obtain ⟨hD1, -⟩ := ordForm_dlogPow hvar' hdim' Q hwQ 1
  have := vanishesTo_pluriformPullback hvar hdim hvar' hdim' σ.toHom hPQ h
  have hσw' : (FunctionFieldEquiv.toHom sX sX' σ) w = z := hσw
  rwa [map_sub, map_smul, pluriformPullback_dlogPow hvar hvar' hdim hdim' σ.toHom hD1,
    hσw'] at this

end CrepantPullback

/-! ### Products of forms on a curve in coordinates -/

section Product

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The product of a finite family `(τ_A)` of rational `a`-canonical forms on a curve, as a
form of degree `M` (meant for `M = |A| a`), computed in the coordinates of the basis `b` of the
line of `1`-forms: `(∏_A τ_A/b^{⊗a}) b^{⊗M}`. -/
private noncomputable def prodForm
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^1 Ω[X.functionField⁄k]))
    {α : Type*} [Fintype α] {a : ℕ} (τ : α → RationalPluriForms sX 1 a) (M : ℕ) :
    RationalPluriForms sX 1 M :=
  letI := functionFieldAlgebra sX
  (∏ A, (ZTensorPower.basis b a).repr (τ A) ()) • (formPow (b ()) M : RationalPluriForms sX 1 M)

variable (b : letI := functionFieldAlgebra sX
  Module.Basis Unit X.functionField (⋀[X.functionField]^1 Ω[X.functionField⁄k]))

omit [CharZero k] [IsLocallyNoetherian X] [IsNormal X] in
private theorem formPow_ne_zero' (M : ℕ) :
    letI := functionFieldAlgebra sX
    (formPow (b ()) M : RationalPluriForms sX 1 M) ≠ 0 := by
  let := functionFieldAlgebra sX
  intro h
  have := repr_smul_formPow b M 1
  rw [one_smul] at this
  change (ZTensorPower.basis b M).repr (formPow (b ()) M : RationalPluriForms sX 1 M) () = 1
    at this
  rw [h] at this
  simp at this

variable (hvar : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 1)

include hvar hdim

/-- The order of a product of nonzero forms is the sum of the orders. -/
private theorem ordForm_prodForm {α : Type*} [Fintype α] {a : ℕ}
    {τ : α → RationalPluriForms sX 1 a} (hτ : ∀ A, τ A ≠ 0) {M : ℕ}
    (hM : M = Fintype.card α * a) (Γ : Mori.PrimeDivisor X) :
    prodForm b τ M ≠ 0 ∧ Γ.ordForm (prodForm b τ M) = ∑ A, Γ.ordForm (τ A) := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hvar.1.toLocallyOfFiniteType
  have hd : (Algebra.trdeg k X.functionField).toNat = 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by exact_mod_cast hdim)
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have hc : ∀ A, (ZTensorPower.basis b a).repr (τ A) () ≠ 0 := fun A =>
    repr_ne_zero_of_ne_zero b (hτ A)
  have hprod : (∏ A, (ZTensorPower.basis b a).repr (τ A) ()) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun A _ => hc A
  have hne : prodForm b τ M ≠ 0 := smul_ne_zero hprod (formPow_ne_zero' b M)
  refine ⟨hne, ?_⟩
  rw [hN _ _ hne]
  have hrep : (ZTensorPower.basis b M).repr (prodForm b τ M) () =
      ∏ A, (ZTensorPower.basis b a).repr (τ A) () := repr_smul_formPow b M _
  rw [hrep, ord_prod _ hc]
  have hA : ∀ A, Γ.ordForm (τ A) =
      X.ord ((ZTensorPower.basis b a).repr (τ A) ()) Γ.genericPoint + a * N := fun A =>
    hN _ _ (hτ A)
  rw [Finset.sum_congr rfl fun A _ => hA A, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, hM]
  push_cast
  ring

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Pull-back along a birational self-map in coordinates: there is `J` with
`σ^*(c b^{⊗a}) = σ(c) Jᵃ b^{⊗a}` for all `a` and `c`. -/
private theorem exists_pluriformPullback_smul_formPow (σ : FunctionFieldEquiv sX sX) :
    letI := functionFieldAlgebra sX
    ∃ J : X.functionField, ∀ (a : ℕ) (c : X.functionField),
      pluriformPullback sX sX σ.toHom 1 a (c • formPow (b ()) a : RationalPluriForms sX 1 a) =
        (σ c * J ^ a) • (formPow (b ()) a : RationalPluriForms sX 1 a) := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hvar.1.toLocallyOfFiniteType
  have hd : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  have hspan : Submodule.span X.functionField {b ()} = ⊤ := by
    have := b.span_eq
    rwa [Set.range_unique] at this
  have hgen := isPullbackGenerator_functionFieldHom (sX := sX) (sX' := sX) (d := 1) hd hd
    σ.toHom hspan (b.ne_zero ())
  obtain ⟨ω', hω'⟩ : ∃ ω' : ⋀[X.functionField]^1 Ω[X.functionField⁄k], ∀ (a : ℕ)
      (c : X.functionField),
      pluriformPullback sX sX σ.toHom 1 a (c • formPow (b ()) a : RationalPluriForms sX 1 a) =
        (σ c • formPow ω' a : RationalPluriForms sX 1 a) :=
    ⟨_, fun a c => pluriformPullback_smul_formPow σ.toHom hgen a c⟩
  refine ⟨b.repr ω' (), fun a c => ?_⟩
  rw [hω' a c]
  conv_lhs => rw [← basis_unit_repr_smul b ω']
  rw [formPow_smul, smul_smul]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Pull-back of a product along a birational self-map is the product of the pull-backs. -/
private theorem pluriformPullback_prodForm (σ : FunctionFieldEquiv sX sX) {α : Type*}
    [Fintype α] {a : ℕ} (τ : α → RationalPluriForms sX 1 a) {M : ℕ}
    (hM : M = Fintype.card α * a) :
    pluriformPullback sX sX σ.toHom 1 M (prodForm b τ M) =
      prodForm b (fun A => pluriformPullback sX sX σ.toHom 1 a (τ A)) M := by
  let := functionFieldAlgebra sX
  obtain ⟨J, hJ⟩ := exists_pluriformPullback_smul_formPow b hvar hdim σ
  have hrep : ∀ A, (ZTensorPower.basis b a).repr (pluriformPullback sX sX σ.toHom 1 a (τ A)) () =
      σ ((ZTensorPower.basis b a).repr (τ A) ()) * J ^ a := by
    intro A
    conv_lhs => rw [eq_repr_smul_formPow b (τ A)]
    erw [hJ a]
    exact repr_smul_formPow b a _
  unfold prodForm
  erw [hJ M]
  simp only [hrep]
  congr 1
  rw [Finset.prod_mul_distrib, map_prod, Finset.prod_const, Finset.card_univ, ← pow_mul, hM,
    mul_comm a]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- **Invariance of a product.** If a birational self-map permutes a family of forms, it fixes
their product. -/
private theorem pluriformPullback_prodForm_of_equiv (σ : FunctionFieldEquiv sX sX)
    {α : Type*} [Fintype α] {a : ℕ} (τ : α → RationalPluriForms sX 1 a) {M : ℕ}
    (hM : M = Fintype.card α * a) (e : α ≃ α)
    (he : ∀ A, pluriformPullback sX sX σ.toHom 1 a (τ A) = τ (e A)) :
    pluriformPullback sX sX σ.toHom 1 M (prodForm b τ M) = prodForm b τ M := by
  rw [pluriformPullback_prodForm b hvar hdim σ τ hM, show (fun A =>
    pluriformPullback sX sX σ.toHom 1 a (τ A)) = fun A => τ (e A) from funext he]
  unfold prodForm
  congr 1
  exact Equiv.prod_comp e (fun A => (ZTensorPower.basis b a).repr (τ A) ())

/-- A product of sections of `a(K + B)` is a section of `M(K + B)`, `M = |A| a`, when `aB` is
integral. -/
private theorem prodForm_mem {B : QDivisor X} {α : Type*} [Fintype α] {a : ℕ}
    (hBint : ∀ P, ∃ z : ℤ, (a : ℚ) * B.coeff P = z) {τ : α → RationalPluriForms sX 1 a}
    (hτ0 : ∀ A, τ A ≠ 0) (hτ : ∀ A, τ A ∈ logPluricanonicalSections sX 1 a B) {M : ℕ}
    (hM : M = Fintype.card α * a) :
    prodForm b τ M ∈ logPluricanonicalSections sX 1 M B := by
  have hfl : ∀ (n : ℕ) (Q : Mori.PrimeDivisor X),
      (DivisorWithCoeffs.roundDown ((n : ℤ) • B)).coeff Q = ⌊(n : ℚ) * B.coeff Q⌋ := by
    intro n Q
    simp [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul]
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_top_iff]
  intro Q
  obtain ⟨z, hz⟩ := hBint Q
  have hfa : ⌊(a : ℚ) * B.coeff Q⌋ = z := by rw [hz, Int.floor_intCast]
  have hfM : ⌊(M : ℚ) * B.coeff Q⌋ = Fintype.card α * z := by
    rw [hM]
    push_cast
    rw [mul_assoc, hz]
    exact_mod_cast Int.floor_intCast _
  have hA : ∀ A, -z ≤ Q.ordForm (τ A) := by
    intro A
    have := hτ A
    rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_top_iff] at this
    rcases this Q with h | h
    · exact absurd h (hτ0 A)
    · rwa [hfl, hfa] at h
  right
  rw [hfl, hfM, (ordForm_prodForm b hvar hdim hτ0 hM Q).2]
  calc -(Fintype.card α * z : ℤ) = ∑ _A : α, -z := by simp
    _ ≤ ∑ A, Q.ordForm (τ A) := Finset.sum_le_sum fun A _ => hA A

/-- A product of local generators of `a(K + B)` at `Q` generates `M(K + B)` at `Q`. -/
private theorem prodForm_generates {B : QDivisor X} {α : Type*} [Fintype α] {a : ℕ}
    {τ : α → RationalPluriForms sX 1 a} (hτ0 : ∀ A, τ A ≠ 0) {M : ℕ}
    (hM : M = Fintype.card α * a) (Q : Mori.PrimeDivisor X)
    (hτ : ∀ A, (Q.ordForm (τ A) : ℚ) + a * B.coeff Q = 0) :
    (Q.ordForm (prodForm b τ M) : ℚ) + M * B.coeff Q = 0 := by
  rw [(ordForm_prodForm b hvar hdim hτ0 hM Q).2]
  push_cast
  rw [Finset.sum_congr rfl fun A _ => (eq_neg_of_add_eq_zero_left (hτ A)), Finset.sum_const,
    Finset.card_univ, hM]
  push_cast
  ring

/-- Normalization in coordinates: `c b^{⊗a} - (dz/z)^{⊗a}` vanishes to order `1 - a` at a point
`P` of a uniformizer `z` exactly when `c / wᵃ` is close to `1`, where `w` is the coordinate of
`dz/z`. -/
private theorem vanishesTo_smul_formPow_sub_iff [IsAlgClosed k] (P : Mori.PrimeDivisor X)
    {z : X.functionField} (hz : X.ord z P.genericPoint = 1) :
    letI := functionFieldAlgebra sX
    ∃ w : X.functionField, w ≠ 0 ∧
      ∀ (a : ℕ) (c : X.functionField) (τ : RationalPluriForms sX 1 a),
        τ = (c • formPow (b ()) a : RationalPluriForms sX 1 a) →
        (VanishesTo P (1 - a) (τ - dlogPow sX z a) ↔
          P.divisorialValuation (c * (w ^ a)⁻¹ - 1) < 1) := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hvar.1.toLocallyOfFiniteType
  have hd1 : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  have hd : (Algebra.trdeg k X.functionField).toNat = 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd1
  obtain ⟨N, hN⟩ := P.exists_ordForm_eq_ord_add_mul hd b
  set η : ⋀[X.functionField]^1 Ω[X.functionField⁄k] := z⁻¹ • exteriorPower.ιMulti
    X.functionField 1 fun _ => KaehlerDifferential.D k X.functionField z with hη
  set w := b.repr η () with hw
  have hdl : ∀ a : ℕ, dlogPow sX z a = (w ^ a • formPow (b ()) a : RationalPluriForms sX 1 a) := by
    intro a
    change (formPow η a : RationalPluriForms sX 1 a) = _
    conv_lhs => rw [← basis_unit_repr_smul b η]
    rw [formPow_smul]
  obtain ⟨hD1, hDo1⟩ := ordForm_dlogPow hvar hdim P hz 1
  have hw0 : w ≠ 0 := by
    intro h; apply hD1; rw [hdl 1, h, zero_pow one_ne_zero, zero_smul]; rfl
  have hwN : X.ord w P.genericPoint + N = -1 := by
    have := hN ((1 : ℕ) : ℤ) (dlogPow sX z 1) hD1
    have hrep : (ZTensorPower.basis b ((1 : ℕ) : ℤ)).repr (dlogPow sX z 1) () = w ^ 1 := by
      rw [hdl 1]; exact repr_smul_formPow b 1 _
    rw [hrep, hDo1, pow_one] at this
    push_cast at this
    linarith
  refine ⟨w, hw0, fun a c τ hτ => ?_⟩
  have hwa : w ^ a ≠ 0 := pow_ne_zero a hw0
  set F : RationalPluriForms sX 1 a := formPow (b ()) a with hF
  have hF0 : F ≠ 0 := formPow_ne_zero' b a
  have hτw : τ - dlogPow sX z a = (c - w ^ a) • F := by
    rw [hτ, hdl a, sub_smul]
    rfl
  rw [hτw, valuation_lt_one_iff]
  by_cases h0 : c - w ^ a = 0
  · have : c * (w ^ a)⁻¹ - 1 = 0 := by
      rw [sub_eq_zero.1 h0, mul_inv_cancel₀ hwa, sub_self]
    simp only [this, true_or, iff_true]
    left; rw [h0, zero_smul]
  have h1 : c * (w ^ a)⁻¹ - 1 = (c - w ^ a) * (w ^ a)⁻¹ := by field_simp
  have h1' : c * (w ^ a)⁻¹ - 1 ≠ 0 := by
    rw [h1]; exact mul_ne_zero h0 (inv_ne_zero hwa)
  have hne : (c - w ^ a) • F ≠ 0 := smul_ne_zero h0 hF0
  have hord := hN a ((c - w ^ a) • F) hne
  have hrep : (ZTensorPower.basis b (a : ℤ)).repr ((c - w ^ a) • F) () = c - w ^ a :=
    repr_smul_formPow b a _
  rw [hrep] at hord
  have hpow : X.ord (w ^ a) P.genericPoint = a * X.ord w P.genericPoint := by
    rw [← zpow_natCast, ord_zpow _ hw0]
  have haN : (a : ℤ) * N = -a - a * X.ord w P.genericPoint := by
    rw [show N = -1 - X.ord w P.genericPoint by linarith]; ring
  simp only [h1', false_or]
  unfold VanishesTo
  rw [or_iff_right hne, hord, h1, Scheme.ord_mul h0 (inv_ne_zero hwa), ← zpow_neg_one,
    ord_zpow _ hwa, hpow]
  constructor <;> intro h <;> linarith

/-- A product of normalized sections is normalized. -/
private theorem prodForm_isNormalized [IsAlgClosed k] {B : QDivisor X}
    {α : Type*} [Fintype α] {a : ℕ} {τ : α → RationalPluriForms sX 1 a}
    (hτ : ∀ A, IsNormalized sX B a 1 (τ A)) {M : ℕ} (hM : M = Fintype.card α * a) :
    IsNormalized sX B M 1 (prodForm b τ M) := by
  let := functionFieldAlgebra sX
  intro P hP z hz
  obtain ⟨w, hw0, hiff⟩ := vanishesTo_smul_formPow_sub_iff b hvar hdim P hz
  rw [one_smul]
  have hA : ∀ A, P.divisorialValuation
      ((ZTensorPower.basis b a).repr (τ A) () * (w ^ a)⁻¹ - 1) < 1 := by
    intro A
    have := hτ A P hP z hz
    rw [one_smul] at this
    exact (hiff a _ (τ A) (eq_repr_smul_formPow b (τ A))).1 this
  refine (hiff M _ (prodForm b τ M) rfl).2 ?_
  have := valuation_prod_sub_one_lt_one P.divisorialValuation Finset.univ fun A _ => hA A
  rwa [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, inv_pow, ← pow_mul,
    mul_comm a, ← hM] at this

end Product

/-! ### Avoiding finitely many subspaces -/

/-- **Avoidance.** In a vector space over an infinite field, let `A` be closed under affine
combinations `x + t (y - x)`, and `W_i` finitely many subspaces none of which contains `A`.
Then some point of `A` lies outside all `W_i`. -/
private theorem exists_mem_forall_notMem {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
    [Module K V] (A : Set V) (hA : ∀ x ∈ A, ∀ y ∈ A, ∀ t : K, x + t • (y - x) ∈ A)
    {ι : Type*} (s : Finset ι) (W : ι → Submodule K V) (hW : ∀ i ∈ s, ∃ x ∈ A, x ∉ W i)
    {x₀ : V} (hx₀ : x₀ ∈ A) : ∃ x ∈ A, ∀ i ∈ s, x ∉ W i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨x₀, hx₀, by simp⟩
  | insert i s hi ih =>
    obtain ⟨a, ha, has⟩ := ih fun j hj => hW j (Finset.mem_insert_of_mem hj)
    obtain ⟨b, hb, hbi⟩ := hW i (Finset.mem_insert_self i s)
    -- for each `j`, at most one `t` puts `a + t (b - a)` into `W j`
    have hab : ∀ j ∈ insert i s, a ∉ W j ∨ b ∉ W j := by
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact Or.inr hbi
      · exact Or.inl (has j hj)
    have hsub : ∀ j ∈ insert i s, {t : K | a + t • (b - a) ∈ W j}.Subsingleton := by
      intro j hj t₁ ht₁ t₂ ht₂
      by_contra hne
      have h1 : (t₁ - t₂) • (b - a) ∈ W j := by
        have := (W j).sub_mem ht₁ ht₂
        rwa [show a + t₁ • (b - a) - (a + t₂ • (b - a)) = (t₁ - t₂) • (b - a) by
          rw [sub_smul]; abel] at this
      have h2 : b - a ∈ W j := by
        have := (W j).smul_mem (t₁ - t₂)⁻¹ h1
        rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul] at this
      have h3 : a ∈ W j := by
        have := (W j).sub_mem ht₁ ((W j).smul_mem t₁ h2)
        rwa [add_sub_cancel_right] at this
      have h4 : b ∈ W j := by
        have := (W j).add_mem h2 h3
        rwa [sub_add_cancel] at this
      rcases hab j hj with h | h
      · exact h h3
      · exact h h4
    have hfin : (⋃ j ∈ insert i s, {t : K | a + t • (b - a) ∈ W j}).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) fun j hj => (hsub j hj).finite
    obtain ⟨t, -, ht⟩ := Set.infinite_univ.exists_notMem_finite hfin
    refine ⟨a + t • (b - a), hA a ha b hb t, fun j hj hmem => ht ?_⟩
    exact Set.mem_biUnion hj hmem

/-! ### Points, boundaries and local generation on a curve -/

section CurveFacts

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

omit [IsIntegral X] in
/-- A boundary `0 ≤ B ≤ 1` on a normal variety is a boundary in the sense of FA 12.2. -/
private theorem isBoundary_toQWeilDivisor (hvar : IsNormalVariety k sX) {B : QDivisor X}
    (hB : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1) :
    (MMP.Fourfold.QDivisor.toQWeilDivisor B).IsBoundary sX := by
  have := hvar.1
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, ?_, fun Γ => hB Γ.1⟩
  exact MMP.Flips.satisfiesS2_iff_forall_min_le_depth.mpr
    ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one X).mp inferInstance).1

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A point of a curve is its generic point or the generic point of a prime divisor. -/
private theorem eq_genericPoint_or_exists_primeDivisor (hdim : topologicalKrullDim X = 1)
    (x : X) : x = genericPoint X ∨ ∃ P : Mori.PrimeDivisor X, x = P.genericPoint := by
  have hle := coheight_le_of_topologicalKrullDim_eq hdim x
  by_cases h0 : Order.coheight x = 0
  · left
    have hmax := Order.coheight_eq_zero.1 h0
    have h1 : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    have h2 : x ⤳ genericPoint X := hmax h1
    exact (h2.antisymm h1).eq
  · right
    have h1 : Order.coheight x = 1 := le_antisymm hle (Order.one_le_iff_ne_zero.2 h0)
    exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1,
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h1).symm⟩

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- **A curve has infinitely many closed points.** -/
private theorem infinite_closedPoints (hvar : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 1) : (closedPoints X).Infinite := by
  intro hfin
  have : LocallyOfFiniteType sX := hvar.1.toLocallyOfFiniteType
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hclosed : IsClosed (closedPoints X) := by
    rw [← Set.biUnion_of_singleton (closedPoints X)]
    exact hfin.isClosed_biUnion fun x hx => hx
  have huniv : closedPoints X = Set.univ := by
    have := closure_closedPoints (X := X)
    rwa [hclosed.closure_eq] at this
  have hη : IsClosed ({genericPoint X} : Set X) :=
    (huniv ▸ Set.mem_univ _ : genericPoint X ∈ closedPoints X)
  have : Subsingleton X := by
    refine ⟨fun x y => ?_⟩
    have hx : x ∈ closure ({genericPoint X} : Set X) := by
      rw [(genericPoint_spec X).def]; exact Set.mem_univ x
    have hy : y ∈ closure ({genericPoint X} : Set X) := by
      rw [(genericPoint_spec X).def]; exact Set.mem_univ y
    rw [hη.closure_eq] at hx hy
    exact hx.trans hy.symm
  have := Subsingleton.discreteTopology (α := X)
  exact zero_ne_one (topologicalKrullDim_eq_zero_of_discreteTopology_nonempty.symm.trans hdim)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Some prime divisor of a curve lies outside the support of any given divisor. -/
private theorem exists_primeDivisor_coeff_eq_zero (hvar : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 1) (B : QDivisor X) :
    ∃ P : Mori.PrimeDivisor X, B.coeff P = 0 := by
  classical
  by_contra h
  push Not at h
  apply infinite_closedPoints hvar hdim
  refine ((B.support.image fun P : Mori.PrimeDivisor X => P.genericPoint).finite_toSet).subset ?_
  intro x hx
  rcases eq_genericPoint_or_exists_primeDivisor hdim x with rfl | ⟨P, rfl⟩
  · exfalso
    obtain ⟨P⟩ : Nonempty (Mori.PrimeDivisor X) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      apply infinite_closedPoints hvar hdim
      refine (Set.finite_singleton (genericPoint X)).subset fun y _ => ?_
      rcases eq_genericPoint_or_exists_primeDivisor hdim y with rfl | ⟨Q, rfl⟩
      · rfl
      · exact (IsEmpty.false Q).elim
    have hcl : IsClosed ({genericPoint X} : Set X) := hx
    have hmem : P.genericPoint ∈ closure ({genericPoint X} : Set X) := by
      rw [(genericPoint_spec X).def]; exact Set.mem_univ _
    rw [hcl.closure_eq] at hmem
    exact primeDivisor_genericPoint_ne_genericPoint P hmem
  · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨P, Finsupp.mem_support_iff.2 (h P), rfl⟩)

omit [IsNormal X] in
/-- **Local generation from generation at a point.** A nonzero form on a curve which generates
`𝒪(m(K + B))` at `x` (when `x` is a closed point) generates it on a neighbourhood of `x`. -/
private theorem exists_generatesOn (hvar : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 1) {B : QDivisor X} {m : ℕ}
    {τ : RationalPluriForms sX 1 m} (hτ : τ ≠ 0) (x : X)
    (hx : ∀ P : Mori.PrimeDivisor X, x = P.genericPoint →
      (P.ordForm τ : ℚ) + m * B.coeff P = 0) :
    ∃ U : X.Opens, x ∈ U ∧ Mori.GeneratesOn B m U τ := by
  classical
  have := hvar.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  set S : Set (Mori.PrimeDivisor X) := {Γ | (Γ.ordForm τ : ℚ) + m * B.coeff Γ ≠ 0} with hSdef
  have hS : S.Finite := by
    refine ((finite_ordForm_ne_zero τ).union B.support.finite_toSet).subset ?_
    intro Γ hΓ
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe, Finsupp.mem_support_iff,
      not_or, not_not] at h
    apply hΓ
    rw [h.1, show B.coeff Γ = B Γ from rfl, h.2]
    simp
  set Z : Set X := ⋃ Γ ∈ hS.toFinset, (Γ.support : Set X) with hZ
  have hZc : IsClosed Z := by
    refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun Γ _ => ?_
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isClosed_closure
  refine ⟨⟨Zᶜ, hZc.isOpen_compl⟩, ?_, hτ, ?_⟩
  · change x ∉ Z
    rw [hZ, Set.mem_iUnion₂]
    rintro ⟨Γ, hΓ, hxΓ⟩
    have hcl := isClosed_singleton_genericPoint hdim Γ
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hcl.closure_eq] at hxΓ
    exact (hS.mem_toFinset.1 hΓ) (hx Γ hxΓ)
  · rintro Γ ⟨y, hyΓ, hyU⟩
    by_contra h
    exact hyU (Set.mem_biUnion (hS.mem_toFinset.2 h) hyΓ)

end CurveFacts

/-! ### Normalized sections with prescribed generation on one curve -/

section Supply

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- `⌊d B⌋` for `d B` integral: its coefficients are those of `d B`. -/
private theorem coeff_roundDown_smul_of_int {B : QDivisor X} {d : ℕ}
    (hBd : ∀ P, ∃ z : ℤ, (d : ℚ) * B.coeff P = z) (n : ℕ) (Q : Mori.PrimeDivisor X) :
    ((DivisorWithCoeffs.roundDown (((n * d : ℕ) : ℤ) • B)).coeff Q : ℚ) =
      ((n * d : ℕ) : ℚ) * B.coeff Q := by
  obtain ⟨z, hz⟩ := hBd Q
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul]
  push_cast
  rw [mul_assoc, hz, show ((n : ℚ) * z) = ((n * z : ℤ) : ℚ) by push_cast; ring,
    Int.floor_intCast]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- `⌊n d B⌋ = n ⌊d B⌋` for `d B` integral. -/
private theorem roundDown_smul_eq_nsmul {B : QDivisor X} {d : ℕ}
    (hBd : ∀ P, ∃ z : ℤ, (d : ℚ) * B.coeff P = z) (n : ℕ) :
    DivisorWithCoeffs.roundDown (((n * d : ℕ) : ℤ) • B) =
      n • DivisorWithCoeffs.roundDown ((d : ℤ) • B) := by
  refine Finsupp.ext fun Q => ?_
  have h1 := coeff_roundDown_smul_of_int hBd n Q
  have h2 := coeff_roundDown_smul_of_int hBd 1 Q
  rw [one_mul] at h2
  change (DivisorWithCoeffs.roundDown (((n * d : ℕ) : ℤ) • B)).coeff Q =
    n * (DivisorWithCoeffs.roundDown ((d : ℤ) • B)).coeff Q
  have : (((DivisorWithCoeffs.roundDown (((n * d : ℕ) : ℤ) • B)).coeff Q : ℤ) : ℚ) =
      ((n * (DivisorWithCoeffs.roundDown ((d : ℤ) • B)).coeff Q : ℤ) : ℚ) := by
    rw [h1]; push_cast; rw [h2]; ring
  exact_mod_cast this

variable [CharZero k] (hvar : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
  (hprop : IsProper sX) (hdim : topologicalKrullDim X = 1) {B : QDivisor X}
  (hB : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1)
  {K : Divisor X} (hK : K.IsCanonicalDivisor sX 1) {d : ℕ} (hd : 0 < d)
  (hBd : ∀ P, ∃ z : ℤ, (d : ℚ) * B.coeff P = z)

include hvar hsm hprop hdim hB hK hd hBd

/-- **Positive degree** (FA 12.2.11, case (12.2.11.4)): for a point `P` outside `⌊B⌋` there is a
normalized section of `12d(K + B)` generating at `P`. -/
private theorem exists_isNormalized_generates_of_pos [IsAlgClosed k]
    (hdeg : 0 < (K.sum fun _ a => (a : ℚ)) + B.sum fun _ a => a)
    (P : Mori.PrimeDivisor X) (hP : B.coeff P < 1) :
    ∃ τ ∈ logPluricanonicalSections sX 1 (12 * d) B, τ ≠ 0 ∧ IsNormalized sX B (12 * d) 1 τ ∧
      (P.ordForm τ : ℚ) + (12 * d : ℕ) * B.coeff P = 0 := by
  classical
  have : LocallyOfFiniteType sX := hvar.1.toLocallyOfFiniteType
  have hd1 : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  set G : Divisor X := DivisorWithCoeffs.roundDown ((d : ℤ) • B) with hGdef
  have hGc : ∀ Q, (G.coeff Q : ℚ) = d * B.coeff Q := fun Q => by
    have := coeff_roundDown_smul_of_int hBd 1 Q
    rwa [one_mul] at this
  have hround : DivisorWithCoeffs.roundDown (((12 * d : ℕ) : ℤ) • B) = 12 • G :=
    roundDown_smul_eq_nsmul hBd 12
  choose zQ hzQ using fun Q : Mori.PrimeDivisor X => exists_ord_eq_one Q
  have hzQ0 : ∀ Q, zQ Q ≠ 0 := fun Q h => by have := hzQ Q; rw [h] at this; simp at this
  have hfloor : ∀ Q, 1 ≤ B.coeff Q → B.coeff Q = 1 ∧ G.coeff Q = d := by
    intro Q hQ
    have h1 : B.coeff Q = 1 := le_antisymm (hB Q).2 hQ
    refine ⟨h1, ?_⟩
    have := hGc Q
    rw [h1, mul_one] at this
    exact_mod_cast this
  set e : ℤ := 12 * d - 12 * G.coeff P
  set τP : RationalPluriForms sX 1 (12 * d : ℕ) := (zQ P ^ e) • dlogPow sX (zQ P) (12 * d)
    with hτPdef
  obtain ⟨hDP0, hDPo⟩ := ordForm_dlogPow hvar hdim P (hzQ P) (12 * d)
  have hτP0 : τP ≠ 0 := smul_ne_zero (zpow_ne_zero _ (hzQ0 P)) hDP0
  have hτPo : P.ordForm τP = -(12 * G.coeff P) := by
    rw [hτPdef, P.ordForm_smul_of_topologicalKrullDim_eq hd1 (zpow_ne_zero _ (hzQ0 P)) hDP0,
      ord_zpow _ (hzQ0 P), hzQ P, hDPo]
    push_cast; ring
  set τ : Mori.PrimeDivisor X → RationalPluriForms sX 1 (12 * d : ℕ) := fun Q =>
    if Q = P then τP else dlogPow sX (zQ Q) (12 * d) with hτdef
  have hτP : τ P = τP := by simp [hτdef]
  have hτQ : ∀ Q, Q ≠ P → τ Q = dlogPow sX (zQ Q) (12 * d) := fun Q h => by
    simp [hτdef, h]
  have hP' : ¬ ∃ Γ : MMP.Flips.WeilDivisorPrime X, Γ.1 = P ∧
      1 ≤ MMP.Fourfold.QDivisor.toQWeilDivisor B Γ := by
    rintro ⟨Γ, rfl, h⟩
    rw [MMP.Fourfold.QDivisor.toQWeilDivisor_apply] at h
    exact absurd hP (not_lt.2 h)
  obtain ⟨s, hs, hsQ⟩ :=
    MMP.Flips.QWeilDivisor.IsBoundary.exists_mem_pluricanonicalSections_sub_vanishes hvar hsm
      hprop hK (isBoundary_toQWeilDivisor hvar hB) hd (G := G)
      (fun Γ => by rw [MMP.Fourfold.QDivisor.toQWeilDivisor_apply]; exact hGc Γ.1)
      (by rwa [sum_toQWeilDivisor]) P hP' τ (by
        rintro Q (rfl | ⟨Γ, rfl, hΓ⟩)
        · right
          rw [hτP, hτPo]
          omega
        · right
          rw [MMP.Fourfold.QDivisor.toQWeilDivisor_apply] at hΓ
          have hne : Γ.1 ≠ P := fun h => by rw [h] at hΓ; exact absurd hP (not_lt.2 hΓ)
          obtain ⟨-, hG⟩ := hfloor Γ.1 hΓ
          obtain ⟨-, hDo⟩ := ordForm_dlogPow hvar hdim Γ.1 (hzQ Γ.1) (12 * d)
          rw [hτQ Γ.1 hne, hDo, hG]
          push_cast; omega)
  have hsV : s ∈ logPluricanonicalSections sX 1 (12 * d) B := by
    rw [mem_logPluricanonicalSections, hround]; exact hs
  have hgen := hsQ P (Or.inl rfl)
  rw [hτP] at hgen
  obtain ⟨hs0, hso⟩ := ordForm_eq_of_vanishesTo_sub (Q := P) hτP0 (by
    rcases hgen with h | h
    · exact Or.inl h
    · right; rw [hτPo]; omega)
  refine ⟨s, hsV, hs0, fun Q hQ z hz => ?_, ?_⟩
  · have hne : Q ≠ P := fun h => by rw [h] at hQ; rw [hQ] at hP; exact lt_irrefl _ hP
    have hv := hsQ Q (Or.inr ⟨(⟨Q, inferInstance, Q.isDiscreteValuationRing_localRing⟩ :
      MMP.Flips.WeilDivisorPrime X), rfl, hQ.ge⟩)
    rw [hτQ Q hne, (hfloor Q hQ.ge).2] at hv
    have hv' : VanishesTo Q (1 - ((12 * d : ℕ) : ℤ)) (s - dlogPow sX (zQ Q) (12 * d)) := by
      rcases hv with h | h
      · exact Or.inl h
      · right; push_cast; omega
    rw [one_smul]
    exact vanishesTo_sub_dlogPow_of_vanishesTo hvar hdim Q (hzQ Q) hz hv'
  · rw [hso, hτPo]
    push_cast
    rw [hGc P]
    ring

omit hd in
/-- **Degree zero** (FA 12.2.11, case (12.2.11.3)): there is a nowhere vanishing normalized
section of `12d(K + B)`. -/
private theorem exists_isNormalized_generates_of_eq_zero [IsAlgClosed k]
    (hdeg : (K.sum fun _ a => (a : ℚ)) + (B.sum fun _ a => a) = 0) :
    ∃ τ ∈ logPluricanonicalSections sX 1 (12 * d) B, τ ≠ 0 ∧ IsNormalized sX B (12 * d) 1 τ ∧
      ∀ P : Mori.PrimeDivisor X, (P.ordForm τ : ℚ) + (12 * d : ℕ) * B.coeff P = 0 := by
  classical
  have : LocallyOfFiniteType sX := hvar.1.toLocallyOfFiniteType
  have := hvar.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hd1 : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  set G : Divisor X := DivisorWithCoeffs.roundDown ((d : ℤ) • B) with hGdef
  have hGc : ∀ Q, (G.coeff Q : ℚ) = d * B.coeff Q := fun Q => by
    have := coeff_roundDown_smul_of_int hBd 1 Q
    rwa [one_mul] at this
  have hround : DivisorWithCoeffs.roundDown (((12 * d : ℕ) : ℤ) • B) = 12 • G :=
    roundDown_smul_eq_nsmul hBd 12
  have h12 : ∀ Q, ((12 • G : Divisor X).coeff Q) = 12 * G.coeff Q := fun Q => by
    simp [DivisorWithCoeffs.coeff_apply]
  have hmem : ∀ τ : RationalPluriForms sX 1 (12 * d : ℕ),
      (∀ P : Mori.PrimeDivisor X, P.ordForm τ + (12 • G : Divisor X).coeff P = 0) →
      τ ∈ logPluricanonicalSections sX 1 (12 * d) B := by
    intro τ hτ
    rw [mem_logPluricanonicalSections, hround, mem_pluricanonicalSections_top_iff]
    intro P
    right
    have := hτ P
    omega
  have hgen : ∀ τ : RationalPluriForms sX 1 (12 * d : ℕ),
      (∀ P : Mori.PrimeDivisor X, P.ordForm τ + (12 • G : Divisor X).coeff P = 0) →
      ∀ P : Mori.PrimeDivisor X, (P.ordForm τ : ℚ) + (12 * d : ℕ) * B.coeff P = 0 := by
    intro τ hτ P
    have h := hτ P
    rw [h12] at h
    have h' : ((P.ordForm τ : ℤ) : ℚ) + 12 * (G.coeff P : ℚ) = 0 := by exact_mod_cast h
    rw [hGc P] at h'
    push_cast
    linarith
  rcases (isBoundary_toQWeilDivisor hvar hB).degree_zero_curve_types hvar hsm hprop hK
      (by rwa [sum_toQWeilDivisor]) with ⟨hg, hΔ0⟩ | ⟨hg, hΔ2, hfl⟩
  · -- genus one, `B = 0`: `K` is principal
    obtain rfl : B = 0 := MMP.Fourfold.QDivisor.toQWeilDivisor_injective (by rw [hΔ0]; rfl)
    have hKsum : (K.sum fun _ a => a) = 0 := by
      have h4 : (K.sum fun _ a => (a : ℚ)) = (((K.sum fun _ a => a : ℤ)) : ℚ) := by
        simp [Finsupp.sum]
      rw [Finsupp.sum_zero_index, add_zero, h4] at hdeg
      exact_mod_cast hdeg
    have hnt : Nontrivial (K.divisorialSubmodule ⊤) := by
      let : Module k (K.divisorialSubmodule ⊤) :=
        Module.compHom _ (scalarsToGlobalSections k sX)
      have h1 : Module.finrank k (K.divisorialSubmodule ⊤) = 1 := hg
      exact Module.nontrivial_of_finrank_pos (R := k) (by omega)
    obtain ⟨σ, hσ⟩ := exists_ne (0 : K.divisorialSubmodule ⊤)
    set φ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
    have hZ0 : MMP.Mori.principalDivisor φ + K = 0 := by
      have hnn := K.zeroDivisor_nonneg σ hσ
      rw [Divisor.zeroDivisor_eq] at hnn
      apply eq_zero_of_nonneg_of_sum_eq_zero hnn
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        sum_principalDivisor_eq_zero hvar hsm hprop hdim φ, hKsum, add_zero]
    obtain ⟨f, hf0, hf⟩ := MMP.Positivity.exists_ord_eq_of_units φ
    have hfK : ∀ R : Mori.PrimeDivisor X, X.ord f R.genericPoint + K.coeff R = 0 := by
      intro R
      rw [← hf R]
      have := congrArg (fun D' : Divisor X => D' R) hZ0
      simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at this
      exact this
    obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hvar hK
    set θ : RationalPluriForms sX 1 ((1 : ℕ) : ℤ) := f • ω with hθ
    have hθ0 : θ ≠ 0 := smul_ne_zero hf0 hω0
    have hθo : ∀ R : Mori.PrimeDivisor X, R.ordForm θ = 0 := by
      intro R
      rw [hθ, R.ordForm_smul_of_topologicalKrullDim_eq hd1 hf0 hω0, hω R, hfK R]
    obtain ⟨b⟩ := exists_basis_topForms (sX := sX) (d := 1) hd1
    have hM : 12 * d = Fintype.card (Fin (12 * d)) * 1 := by simp
    set τ := prodForm b (fun _ : Fin (12 * d) => θ) (12 * d) with hτdef
    have hτo : ∀ R : Mori.PrimeDivisor X, R.ordForm τ = 0 := by
      intro R
      rw [(ordForm_prodForm b hvar hdim (fun _ => hθ0) hM R).2]
      simp [hθo R]
    obtain ⟨P₀, -⟩ := exists_primeDivisor_coeff_eq_zero hvar hdim (0 : QDivisor X)
    have hτ0 : τ ≠ 0 := (ordForm_prodForm b hvar hdim (fun _ => hθ0) hM P₀).1
    have hG0 : ∀ P, G.coeff P = 0 := fun P => by
      have := hGc P
      simp only [DivisorWithCoeffs.coeff_zero, mul_zero] at this
      exact_mod_cast this
    have hτG : ∀ P : Mori.PrimeDivisor X, P.ordForm τ + (12 • G : Divisor X).coeff P = 0 := by
      intro P
      rw [hτo P, h12, hG0 P]
      ring
    refine ⟨τ, hmem τ hτG, hτ0, fun P hP => ?_, hgen τ hτG⟩
    simp at hP
  · -- genus zero
    have hGQ : Divisor.toQDivisor G = (d : ℤ) • B := by
      refine Finsupp.ext fun Q => ?_
      have := hGc Q
      simp only [Divisor.toQDivisor, Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast]
      exact this
    obtain ⟨s, hs0, hso, hsn⟩ := exists_ordForm_add_eq_zero_of_genus_zero sX hvar hsm hprop hdim hK
      (isBoundary_toQWeilDivisor hvar hB) hGQ hg hΔ2
    refine ⟨s, hmem s hso, hs0, fun Q hQ z hz => ?_, hgen s hso⟩
    obtain ⟨w, hw, hv⟩ := hsn Q hQ.ge
    have hGQ1 : G.coeff Q = d := by
      have := hGc Q
      rw [hQ, mul_one] at this
      exact_mod_cast this
    rw [h12, hGQ1] at hv
    have hv' : VanishesTo Q (1 - ((12 * d : ℕ) : ℤ)) (s - dlogPow sX w (12 * d)) := by
      rcases hv with h | h
      · exact Or.inl h
      · right; push_cast; omega
    rw [one_smul]
    exact vanishesTo_sub_dlogPow_of_vanishesTo hvar hdim Q hw hz hv'

/-- **Normalized sections generating at finitely many points.** For `d B` integral and
`deg(K + B) ≥ 0`, any finite set of points of the curve has a normalized nonzero section of
`12d(K + B)` generating at each of them. -/
private theorem exists_isNormalized_generates_finset [IsAlgClosed k]
    (hdeg : 0 ≤ (K.sum fun _ a => (a : ℚ)) + B.sum fun _ a => a)
    (F : Finset (Mori.PrimeDivisor X)) :
    ∃ τ ∈ logPluricanonicalSections sX 1 (12 * d) B, τ ≠ 0 ∧ IsNormalized sX B (12 * d) 1 τ ∧
      ∀ Q ∈ F, (Q.ordForm τ : ℚ) + (12 * d : ℕ) * B.coeff Q = 0 := by
  classical
  rcases hdeg.lt_or_eq with hpos | hzero
  swap
  · obtain ⟨τ, h1, h2, h3, h4⟩ :=
      exists_isNormalized_generates_of_eq_zero hvar hsm hprop hdim hB hK hBd hzero.symm
    exact ⟨τ, h1, h2, h3, fun Q _ => h4 Q⟩
  have hfl : ∀ Q : Mori.PrimeDivisor X,
      ((⌊((12 * d : ℕ) : ℚ) * B.coeff Q⌋ : ℤ) : ℚ) = ((12 * d : ℕ) : ℚ) * B.coeff Q := by
    intro Q
    have := coeff_roundDown_smul_of_int hBd 12 Q
    rwa [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at this
  have hcoeffV : ∀ Q : Mori.PrimeDivisor X,
      (DivisorWithCoeffs.roundDown (((12 * d : ℕ) : ℤ) • B)).coeff Q =
        ⌊((12 * d : ℕ) : ℚ) * B.coeff Q⌋ := by
    intro Q
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast]
  obtain ⟨P₀, hP₀⟩ := exists_primeDivisor_coeff_eq_zero hvar hdim B
  obtain ⟨x₀, hx₀V, -, hx₀n, -⟩ :=
    exists_isNormalized_generates_of_pos hvar hsm hprop hdim hB hK hd hBd hpos P₀
      (by rw [hP₀]; norm_num)
  set A : Set (RationalPluriForms sX 1 (12 * d : ℕ)) :=
    {τ | τ ∈ logPluricanonicalSections sX 1 (12 * d) B ∧ IsNormalized sX B (12 * d) 1 τ}
    with hAdef
  have hA : ∀ x ∈ A, ∀ y ∈ A, ∀ t : k, x + t • (y - x) ∈ A := by
    rintro x ⟨hxV, hxn⟩ y ⟨hyV, hyn⟩ t
    refine ⟨(logPluricanonicalSections sX 1 (12 * d) B).add_mem hxV
      ((logPluricanonicalSections sX 1 (12 * d) B).smul_mem t
        ((logPluricanonicalSections sX 1 (12 * d) B).sub_mem hyV hxV)), fun P hP z hz => ?_⟩
    have h1 := hxn P hP z hz
    have h2 := hyn P hP z hz
    have e : x + t • (y - x) - (1 : k) • dlogPow sX z (12 * d) =
        (x - (1 : k) • dlogPow sX z (12 * d)) + t • ((y - (1 : k) • dlogPow sX z (12 * d)) -
          (x - (1 : k) • dlogPow sX z (12 * d))) := by
      rw [sub_sub_sub_cancel_right]; abel
    rw [e]
    exact h1.add ((h2.sub h1).const_smul t)
  let W : Mori.PrimeDivisor X → Submodule k (RationalPluriForms sX 1 (12 * d : ℕ)) := fun Q =>
    { carrier := {τ | VanishesTo Q (1 - ⌊((12 * d : ℕ) : ℚ) * B.coeff Q⌋) τ}
      add_mem' := fun ha hb => VanishesTo.add ha hb
      zero_mem' := Or.inl rfl
      smul_mem' := fun c _ h => VanishesTo.const_smul h c }
  have hnotW : ∀ (Q : Mori.PrimeDivisor X) (τ : RationalPluriForms sX 1 (12 * d : ℕ)),
      τ ≠ 0 → (Q.ordForm τ : ℚ) + (12 * d : ℕ) * B.coeff Q = 0 → τ ∉ W Q := by
    intro Q τ hτ0 hτQ hW
    rcases hW with h | h
    · exact hτ0 h
    · have he : ((Q.ordForm τ : ℤ) : ℚ) = ((-⌊((12 * d : ℕ) : ℚ) * B.coeff Q⌋ : ℤ) : ℚ) := by
        rw [Int.cast_neg, hfl Q]; linarith
      have he' : Q.ordForm τ = -⌊((12 * d : ℕ) : ℚ) * B.coeff Q⌋ := by exact_mod_cast he
      omega
  have hW : ∀ Q ∈ insert P₀ F, ∃ x ∈ A, x ∉ W Q := by
    intro Q _
    by_cases hQ1 : B.coeff Q = 1
    · refine ⟨x₀, ⟨hx₀V, hx₀n⟩, ?_⟩
      obtain ⟨z, hz⟩ := exists_ord_eq_one Q
      have hv := hx₀n Q hQ1 z hz
      rw [one_smul] at hv
      obtain ⟨h0, ho⟩ := ordForm_eq_of_vanishesTo_sub_dlogPow hvar hdim Q hz hv
      refine hnotW Q x₀ h0 ?_
      rw [ho, hQ1]
      push_cast; ring
    · obtain ⟨x, hxV, hx0, hxn, hxQ⟩ :=
        exists_isNormalized_generates_of_pos hvar hsm hprop hdim hB hK hd hBd hpos Q
          (lt_of_le_of_ne (hB Q).2 hQ1)
      exact ⟨x, ⟨hxV, hxn⟩, hnotW Q x hx0 hxQ⟩
  obtain ⟨τ, ⟨hτV, hτn⟩, hτW⟩ := exists_mem_forall_notMem A hA (insert P₀ F) W hW ⟨hx₀V, hx₀n⟩
  have hτ0 : τ ≠ 0 := fun h => hτW P₀ (Finset.mem_insert_self _ _) (by rw [h]; exact Or.inl rfl)
  refine ⟨τ, hτV, hτ0, hτn, fun Q hQ => ?_⟩
  have hnW := hτW Q (Finset.mem_insert_of_mem hQ)
  have hlt : Q.ordForm τ < 1 - ⌊((12 * d : ℕ) : ℚ) * B.coeff Q⌋ := by
    by_contra h
    push Not at h
    exact hnW (Or.inr h)
  have hge : -⌊((12 * d : ℕ) : ℚ) * B.coeff Q⌋ ≤ Q.ordForm τ := by
    have := hτV
    rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_top_iff] at this
    rcases this Q with h | h
    · exact absurd h hτ0
    · rwa [hcoeffV] at h
  have heq : Q.ordForm τ = -⌊((12 * d : ℕ) : ℚ) * B.coeff Q⌋ := by omega
  rw [heq, Int.cast_neg, hfl Q]
  ring

end Supply

/-! ### Invariant normalized sections on one curve -/

section Invariant

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Pull-back along a product of birational self-maps is the composite of the pull-backs. -/
private theorem pluriformPullback_pluriformPullback_mul (hvar : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 1) (σ τ : FunctionFieldEquiv sX sX) {m : ℕ}
    (ρ : RationalPluriForms sX 1 m) :
    pluriformPullback sX sX σ.toHom 1 m (pluriformPullback sX sX τ.toHom 1 m ρ) =
      pluriformPullback sX sX (σ * τ).toHom 1 m ρ := by
  have : LocallyOfFiniteType sX := hvar.1.toLocallyOfFiniteType
  have hd1 : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  rw [pluriformPullback_comp hd1 hd1 hd1]
  congr 1

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Pull-back along a birational self-map is injective. -/
private theorem pluriformPullback_injective (hvar : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 1) (σ : FunctionFieldEquiv sX sX) (m : ℕ) :
    Function.Injective (pluriformPullback sX sX σ.toHom 1 m) := by
  have : LocallyOfFiniteType sX := hvar.1.toLocallyOfFiniteType
  have hd1 : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  intro x y hxy
  have h := congrArg (pluriformPullback sX sX σ⁻¹.toHom 1 m) hxy
  rwa [pluriformPullback_pluriformPullback_mul hvar hdim, pluriformPullback_pluriformPullback_mul
    hvar hdim, inv_mul_cancel, pluriformPullback_one hd1, pluriformPullback_one hd1] at h

variable (hvar : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) (hprop : IsProper sX)
  (hdim : topologicalKrullDim X = 1) {B : QDivisor X} (hB : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1)
  {K : Divisor X} (hK : K.IsCanonicalDivisor sX 1) {d : ℕ} (hd : 0 < d)
  (hBd : ∀ P, ∃ z : ℤ, (d : ℚ) * B.coeff P = z)

include hvar hsm hprop hdim hB hK hd hBd

/-- **Invariant normalized generators on one curve.** There is `N > 0` such that in every
positive degree `M` divisible by `N`, every finite set of points has a nonzero normalized section
of `M(K + B)` which is invariant under all crepant birational self-maps of `(X, B)` and generates
at each of the points. It is a product of translates of a normalized section, over the finite
image of the crepant birational self-maps
(`MMP.Fourfold.finite_range_pluriformPullback_and_isRelativelySemiample_of_curve`). -/
private theorem exists_invariant_isNormalized_generates [IsAlgClosed k]
    (hdeg : 0 ≤ (K.sum fun _ a => (a : ℚ)) + B.sum fun _ a => a)
    (hpair : MMP.Mori.IsPair sX B) :
    ∃ N : ℕ, 0 < N ∧ ∀ (F : Finset (Mori.PrimeDivisor X)) (M : ℕ), N ∣ M → 0 < M →
      ∃ τ ∈ logPluricanonicalSections sX 1 M B, τ ≠ 0 ∧ IsNormalized sX B M 1 τ ∧
        (∀ σ ∈ crepantBirationalAutomorphisms sX B,
          pluriformPullback sX sX σ.toHom 1 M τ = τ) ∧
        ∀ Q ∈ F, (Q.ordForm τ : ℚ) + M * B.coeff Q = 0 := by
  classical
  have : LocallyOfFiniteType sX := hvar.1.toLocallyOfFiniteType
  have hd1 : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  set n₀ := 12 * d with hn₀
  have hn₀B : ∀ P, ∃ z : ℤ, (n₀ : ℚ) * B.coeff P = z := fun P => by
    obtain ⟨z, hz⟩ := hBd P
    exact ⟨12 * z, by rw [hn₀]; push_cast; rw [mul_assoc, hz]⟩
  have hfin := (MMP.Fourfold.finite_range_pluriformPullback_and_isRelativelySemiample_of_curve
    hvar hsm hprop hdim hB hK hdeg).1 n₀ (by positivity) hn₀B
  set T := Set.range fun (σ : crepantBirationalAutomorphisms sX B)
    (s : logPluricanonicalSections sX 1 n₀ B) =>
      pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 1 n₀
        (s : RationalPluriForms sX 1 n₀) with hTdef
  let : Fintype T := hfin.fintype
  have hTne : Nonempty T := ⟨⟨_, 1, rfl⟩⟩
  refine ⟨Fintype.card T * n₀, Nat.mul_pos Fintype.card_pos (by positivity),
    fun F M hNM hM => ?_⟩
  obtain ⟨j, rfl⟩ := hNM
  choose σT hσT using fun A : T => A.2
  choose Qc hQc using fun (y : Mori.PrimeDivisor X) (A : T) =>
    exists_primeDivisor_of_isCrepantBirationalMap hvar hvar hdim hpair hpair (σT A).2 y
  set F' : Finset (Mori.PrimeDivisor X) :=
    Finset.image (fun p : Mori.PrimeDivisor X × T => Qc p.1 p.2) (F ×ˢ Finset.univ)
  obtain ⟨s, hsV, hs0, hsn, hsF⟩ :=
    exists_isNormalized_generates_finset hvar hsm hprop hdim hB hK hd hBd hdeg F'
  set τ : T × Fin j → RationalPluriForms sX 1 n₀ := fun p => p.1.1 ⟨s, hsV⟩ with hτdef
  have hτ : ∀ p : T × Fin j, τ p =
      pluriformPullback sX sX (σT p.1 : FunctionFieldEquiv sX sX).toHom 1 n₀ s := by
    intro p
    change p.1.1 ⟨s, hsV⟩ = _
    rw [← hσT p.1]
  obtain ⟨P₀, -⟩ := exists_primeDivisor_coeff_eq_zero hvar hdim B
  have hτ0 : ∀ p, τ p ≠ 0 := fun p => by
    rw [hτ]
    exact (ordForm_pluriformPullback hvar hdim hvar hdim _ (hQc P₀ p.1).1 hs0).1
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) (d := 1) hd1
  have hMeq : Fintype.card T * n₀ * j = Fintype.card (T × Fin j) * n₀ := by
    rw [Fintype.card_prod, Fintype.card_fin]; ring
  refine ⟨prodForm b τ (Fintype.card T * n₀ * j), ?_, ?_, ?_, ?_, ?_⟩
  · exact prodForm_mem b hvar hdim hn₀B hτ0 (fun p => by
      rw [hτ]
      exact pluriformPullback_mem_logPluricanonicalSections hvar hdim hvar hdim hpair
        hpair (σT p.1).2 hsV) hMeq
  · exact (ordForm_prodForm b hvar hdim hτ0 hMeq P₀).1
  · exact prodForm_isNormalized b hvar hdim (fun p => by
      rw [hτ]
      exact isNormalized_pluriformPullback hvar hdim hvar hdim hpair hpair (σT p.1).2
        hsn) hMeq
  · intro h hh
    let e : T → T := fun A => ⟨fun s' => pluriformPullback sX sX h.toHom 1 n₀ (A.1 s'),
      ⟨⟨h * σT A, mul_mem hh (σT A).2⟩, funext fun s' => by
        rw [← hσT A]
        exact (pluriformPullback_pluriformPullback_mul hvar hdim h _ _).symm⟩⟩
    have hinj : Function.Injective e := by
      intro A A' hAA'
      apply Subtype.ext
      funext s'
      exact pluriformPullback_injective hvar hdim h n₀ (congrFun (congrArg Subtype.val hAA') s')
    let E : T × Fin j ≃ T × Fin j :=
      Equiv.prodCongr (Equiv.ofBijective e (Finite.injective_iff_bijective.1 hinj))
        (Equiv.refl _)
    exact pluriformPullback_prodForm_of_equiv b hvar hdim h τ hMeq E fun p => rfl
  · intro y hy
    refine prodForm_generates b hvar hdim hτ0 hMeq y fun p => ?_
    rw [hτ, (ordForm_pluriformPullback hvar hdim hvar hdim _ (hQc y p.1).1 hs0).2,
      (hQc y p.1).2]
    exact hsF (Qc y p.1) (Finset.mem_image.2 ⟨(y, p.1),
      Finset.mem_product.2 ⟨hy, Finset.mem_univ _⟩, rfl⟩)

end Invariant

/-! ### Admissible generation on a finite collection of curve pairs -/

section Collection

/-- A rational number becomes an integer after multiplication by any multiple of its
denominator. -/
private theorem exists_mul_eq_intCast_of_den_dvd {q : ℚ} {n : ℕ} (h : q.den ∣ n) :
    ∃ z : ℤ, (n : ℚ) * q = z := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨t * q.num, ?_⟩
  push_cast
  rw [mul_comm (q.den : ℚ), mul_assoc, mul_comm (q.den : ℚ), Rat.mul_den_eq_num]

/-- **A common denominator** for finitely many `ℚ`-divisors. -/
private theorem exists_common_denominator {I : Type*} [Finite I] {X : I → Scheme.{u}}
    (B : ∀ i, QDivisor (X i)) :
    ∃ d : ℕ, 0 < d ∧ ∀ i P, ∃ z : ℤ, (d : ℚ) * (B i).coeff P = z := by
  classical
  have := Fintype.ofFinite I
  refine ⟨∏ i, ∏ P ∈ (B i).support, ((B i) P).den,
    Finset.prod_pos fun i _ => Finset.prod_pos fun P _ => Rat.den_pos _, fun i P => ?_⟩
  refine exists_mul_eq_intCast_of_den_dvd ?_
  by_cases hP : P ∈ (B i).support
  · exact (Finset.dvd_prod_of_mem (fun P => ((B i) P).den) hP).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ P ∈ (B i).support, ((B i) P).den) (Finset.mem_univ i))
  · rw [Finsupp.notMem_support_iff] at hP
    rw [show (B i).coeff P = (B i) P from rfl, hP, Rat.den_zero]
    exact one_dvd _

variable {k : Type u} [Field k] [CharZero k]

/-- `m(K + B) = m K + ⌊m B⌋` when `m B` is integral. -/
private theorem toQDivisor_smul_add_roundDown {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} {K : Divisor X} {m : ℕ}
    (hBm : ∀ P, ∃ z : ℤ, (m : ℚ) * B.coeff P = z) :
    Divisor.toQDivisor ((m : ℤ) • K + DivisorWithCoeffs.roundDown ((m : ℤ) • B)) =
      (m : ℤ) • (Divisor.toQDivisor K + B) := by
  rw [map_add, map_zsmul, smul_add]
  congr 1
  refine Finsupp.ext fun Q => ?_
  have h1 := coeff_roundDown_smul_of_int hBm 1 Q
  rw [one_mul] at h1
  change (Divisor.toQDivisor (DivisorWithCoeffs.roundDown ((m : ℤ) • B))).coeff Q =
    ((m : ℤ) • B).coeff Q
  rw [Divisor.coeff_toQDivisor, h1, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, Int.cast_natCast]

omit [CharZero k] in
/-- A smooth curve with a canonical divisor `K` and a `ℚ`-divisor `B` with `dB` integral is a
pair: `K + B` is `ℚ`-Cartier. -/
private theorem isPair_of_curve {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hvar : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    {B : QDivisor X} {K : Divisor X} (hK : K.IsCanonicalDivisor sX 1) {d : ℕ} (hd : 0 < d)
    (hBd : ∀ P, ∃ z : ℤ, (d : ℚ) * B.coeff P = z) : MMP.Mori.IsPair sX B :=
  ⟨hvar, 1, K, hK, d, by exact_mod_cast hd.ne', (d : ℤ) • K +
    DivisorWithCoeffs.roundDown ((d : ℤ) • B), toQDivisor_smul_add_roundDown hBd,
    MMP.Fourfold.isCartier_of_isSmoothScheme hsm _⟩

variable {I : Type*} {X : I → Scheme.{u}} {sX : ∀ i, X i ⟶ Spec (.of k)}
  [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]

/-- Crepant birational equivalence of the components of a collection of pairs. -/
private def crepantSetoid (B : ∀ i, QDivisor (X i)) : Setoid I where
  r i j := ∃ σ : FunctionFieldEquiv (sX i) (sX j),
    IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ
  iseqv := ⟨fun i => ⟨1, (crepantBirationalAutomorphisms (sX i) (B i)).one_mem⟩,
    fun {i j} ⟨σ, hσ⟩ => by
      let := functionFieldAlgebra (sX i)
      let := functionFieldAlgebra (sX j)
      exact ⟨σ.symm, hσ.symm⟩,
    fun {i j l} ⟨σ, hσ⟩ ⟨τ, hτ⟩ => by
      let := functionFieldAlgebra (sX i)
      let := functionFieldAlgebra (sX j)
      let := functionFieldAlgebra (sX l)
      exact ⟨τ.trans σ, hσ.trans hτ⟩⟩

/-- **Transport of invariant sections along crepant identifications.** If `τ` on `X_l` is
invariant under the crepant birational self-maps of `(X_l, B_l)` and `ψ : X_j ⇢ X_l`,
`ψ' : X_{j'} ⇢ X_l` are crepant, then `σ^* ψ'^* τ = ψ^* τ` for every crepant
`σ : X_j ⇢ X_{j'}`. -/
private theorem pluriformPullback_pluriformPullback_of_invariant
    (hvar : ∀ i, IsNormalVariety k (sX i)) (hdim : ∀ i, topologicalKrullDim (X i) = 1)
    {B : ∀ i, QDivisor (X i)} {j j' l : I} {m : ℕ} {τ : RationalPluriForms (sX l) 1 m}
    (hτ : ∀ g ∈ crepantBirationalAutomorphisms (sX l) (B l),
      pluriformPullback (sX l) (sX l) g.toHom 1 m τ = τ)
    {ψ : FunctionFieldEquiv (sX j) (sX l)} (hψ : IsCrepantBirationalMap _ _ (B j) (B l) ψ)
    {ψ' : FunctionFieldEquiv (sX j') (sX l)} (hψ' : IsCrepantBirationalMap _ _ (B j') (B l) ψ')
    {σ : FunctionFieldEquiv (sX j) (sX j')} (hσ : IsCrepantBirationalMap _ _ (B j) (B j') σ) :
    pluriformPullback (sX j) (sX j') σ.toHom 1 m (pluriformPullback (sX j') (sX l) ψ'.toHom 1 m τ)
      = pluriformPullback (sX j) (sX l) ψ.toHom 1 m τ := by
  have : ∀ i, LocallyOfFiniteType (sX i) := fun i => (hvar i).1.toLocallyOfFiniteType
  have hd1 : ∀ i, topologicalKrullDim (X i) = ((1 : ℕ) : WithBot ℕ∞) := fun i => by
    exact_mod_cast hdim i
  let := functionFieldAlgebra (sX j)
  let := functionFieldAlgebra (sX j')
  let := functionFieldAlgebra (sX l)
  set g : FunctionFieldEquiv (sX l) (sX l) := ψ'.trans (σ.trans ψ.symm) with hg
  have hgc : g ∈ crepantBirationalAutomorphisms (sX l) (B l) := by
    change IsCrepantBirationalMap (sX l) (sX l) (B l) (B l) g
    exact (hψ.symm.trans hσ).trans hψ'
  conv_rhs => rw [← hτ g hgc, pluriformPullback_comp (hd1 j) (hd1 l) (hd1 l)]
  rw [pluriformPullback_comp (hd1 j) (hd1 j') (hd1 l)]
  congr 2
  ext x
  change σ (ψ' x) = ψ (ψ.symm (σ (ψ' x)))
  rw [AlgEquiv.apply_symm_apply]

variable [Finite I] (hvar : ∀ i, IsNormalVariety k (sX i)) (hsm : ∀ i, IsSmoothScheme (sX i))
  (hprop : ∀ i, IsProper (sX i)) (hdim : ∀ i, topologicalKrullDim (X i) = 1)
  {B : ∀ i, QDivisor (X i)} (hB : ∀ i P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1)
  {K : ∀ i, Divisor (X i)} (hK : ∀ i, (K i).IsCanonicalDivisor (sX i) 1)
  (hdeg : ∀ i, 0 ≤ ((K i).sum fun _ a => (a : ℚ)) + (B i).sum fun _ a => a)

include hvar hsm hprop hdim hB hK hdeg

/-- **Admissible generation.** In every positive degree divisible by a fixed `m₂ > 0`, the
admissible systems generate every adjoint, for every residue restriction datum. -/
private theorem exists_admissibleSections_generatesOn [IsAlgClosed k] :
    ∃ m₂ : ℕ, 0 < m₂ ∧ ∀ m : ℕ, 0 < m → m₂ ∣ m →
      ∀ (R : ResidueRestriction sX B 1 m) (i : I) (x : X i),
        ∃ s ∈ admissibleSections R, ∃ U : (X i).Opens, x ∈ U ∧
          Mori.GeneratesOn (B i) m U (s i).1 := by
  classical
  have := Fintype.ofFinite I
  obtain ⟨d, hd, hBd⟩ := exists_common_denominator B
  have hpair : ∀ i, MMP.Mori.IsPair (sX i) (B i) := fun i =>
    isPair_of_curve (hvar i) (hsm i) (hK i) hd (hBd i)
  choose N hN hKey using fun i => exists_invariant_isNormalized_generates (hvar i) (hsm i)
    (hprop i) (hdim i) (hB i) (hK i) hd (hBd i) (hdeg i) (hpair i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun m hm hdvd R i x => ?_⟩
  let S := crepantSetoid (sX := sX) B
  let rep : I → I := fun j => (Quotient.mk S j).out
  have hrep : ∀ j, S.r j (rep j) := fun j => Setoid.symm (Quotient.mk_out (s := S) j)
  choose φ hφ using hrep
  have hrep_eq : ∀ j j', S.r j j' → rep j = rep j' := fun j j' h => by
    change (Quotient.mk S j).out = (Quotient.mk S j').out
    rw [Quotient.sound h]
  -- the target points on the representatives
  obtain ⟨F, hF⟩ : ∃ F : ∀ l, Finset (Mori.PrimeDivisor (X l)), ∀ P : Mori.PrimeDivisor (X i),
      x = P.genericPoint → ∃ Q : Mori.PrimeDivisor (X (rep i)),
        (∀ f : (X (rep i)).functionField, f ≠ 0 →
          (X i).ord (φ i f) P.genericPoint = (X (rep i)).ord f Q.genericPoint) ∧
        (B i).coeff P = (B (rep i)).coeff Q ∧ Q ∈ F (rep i) := by
    by_cases hx : ∃ P : Mori.PrimeDivisor (X i), x = P.genericPoint
    · obtain ⟨P₁, hP₁⟩ := hx
      obtain ⟨Q, hQ, hBQ⟩ := exists_primeDivisor_of_isCrepantBirationalMap (hvar i)
        (hvar (rep i)) (hdim (rep i)) (hpair i) (hpair (rep i)) (hφ i) P₁
      refine ⟨fun l => if h : rep i = l then {h ▸ Q} else ∅, fun P hP => ?_⟩
      have hPP : P = P₁ := MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes
        (by rw [← hP, hP₁])
      subst hPP
      exact ⟨Q, hQ, hBQ, by simp⟩
    · exact ⟨fun _ => ∅, fun P hP => absurd ⟨P, hP⟩ hx⟩
  have hNm : ∀ l, N l ∣ m := fun l => (Finset.dvd_prod_of_mem N (Finset.mem_univ l)).trans hdvd
  choose τ hτV hτ0 hτn hτinv hτF using fun l => hKey l (F l) m (hNm l) hm
  -- the section system
  let s : ∀ j, logPluricanonicalSections (sX j) 1 m (B j) := fun j =>
    ⟨pluriformPullback (sX j) (sX (rep j)) (φ j).toHom 1 m (τ (rep j)),
      pluriformPullback_mem_logPluricanonicalSections (hvar j) (hdim j) (hvar (rep j))
        (hdim (rep j)) (hpair j) (hpair (rep j)) (hφ j) (hτV (rep j))⟩
  have hsadm : s ∈ admissibleSections R := by
    refine mem_admissibleSections_of_isNormalized hvar hdim hB R 1 (fun j =>
      isNormalized_pluriformPullback (hvar j) (hdim j) (hvar (rep j))
        (hdim (rep j)) (hpair j) (hpair (rep j)) (hφ j) (hτn (rep j))) ?_
    intro j j' σ hσ
    have h1 := hrep_eq j j' ⟨σ, hσ⟩
    change pluriformPullback (sX j) (sX j') σ.toHom 1 m
        (pluriformPullback (sX j') (sX (rep j')) (φ j').toHom 1 m (τ (rep j'))) =
      pluriformPullback (sX j) (sX (rep j)) (φ j).toHom 1 m (τ (rep j))
    revert h1
    generalize hφj : φ j = ψ
    generalize hφj' : φ j' = ψ'
    have hψ : IsCrepantBirationalMap _ _ (B j) (B (rep j)) ψ := hφj ▸ hφ j
    have hψ' : IsCrepantBirationalMap _ _ (B j') (B (rep j')) ψ' := hφj' ▸ hφ j'
    clear hφj hφj'
    generalize rep j = l at ψ hψ ⊢
    intro h1
    subst h1
    exact pluriformPullback_pluriformPullback_of_invariant hvar hdim (hτinv _) hψ hψ' hσ
  refine ⟨s, hsadm, ?_⟩
  obtain ⟨P₀, -⟩ := exists_primeDivisor_coeff_eq_zero (hvar i) (hdim i) (B i)
  obtain ⟨Q₀, hQ₀, -⟩ := exists_primeDivisor_of_isCrepantBirationalMap (hvar i) (hvar (rep i))
    (hdim (rep i)) (hpair i) (hpair (rep i)) (hφ i) P₀
  have hs0 : (s i).1 ≠ 0 := (ordForm_pluriformPullback (hvar i) (hdim i) (hvar (rep i))
      (hdim (rep i)) (φ i).toHom hQ₀ (hτ0 (rep i))).1
  refine exists_generatesOn (hvar i) (hdim i) hs0 x fun P hP => ?_
  obtain ⟨Q, hPQ, hBQ, hQF⟩ := hF P hP
  have h := (ordForm_pluriformPullback (hvar i) (hdim i) (hvar (rep i)) (hdim (rep i))
    (φ i).toHom hPQ (hτ0 (rep i))).2
  change (P.ordForm (pluriformPullback (sX i) (sX (rep i)) (φ i).toHom 1 m (τ (rep i))) : ℚ) +
    m * (B i).coeff P = 0
  rw [h, hBQ]
  exact hτF (rep i) Q hQF

end Collection

/-! ### The stratified setting for curve pairs -/

section Setting

variable {k : Type u} [Field k]

/-- **Zero-dimensional varieties over an algebraically closed field are smooth.** -/
private theorem isSmoothScheme_of_topologicalKrullDim_eq_zero [IsAlgClosed k] {T : Scheme.{u}}
    {sT : T ⟶ Spec (.of k)} [IsIntegral T] [LocallyOfFiniteType sT]
    (hT : topologicalKrullDim T = 0) : IsSmoothScheme sT := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have hreg : IsRegular T := by
    refine ((isRegular_tfae T).out 1 2 rfl rfl).mpr ⟨inferInstance, fun x => ?_⟩
    have : Ring.KrullDimLE 0 (T.presheaf.stalk x) :=
      krullDimLE_of_coheight_le (coheight_le_of_topologicalKrullDim_eq hT x)
    have hfield := Ring.KrullDimLE.isField_of_isDomain (R := T.presheaf.stalk x)
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield, Submodule.spanFinrank_bot]
    exact_mod_cast ringKrullDim_nonneg_of_nontrivial
  have := smooth_of_isRegular_of_perfectField k sT hreg
  exact (MMP.Mori.isSmoothScheme_iff sT).2 this

variable {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C]
  [IsNormal C]

/-- **Divisors on a normal curve are snc.** -/
private theorem isSNC_of_curve [IsAlgClosed k] [LocallyOfFiniteType sC]
    (hdim : topologicalKrullDim C = 1)
    {R : Type*} [Zero R] (D : DivisorWithCoeffs R C) : D.IsSNC sC := by
  have hsupp : ∀ E : Mori.PrimeDivisor C, (E.support : Set C) = {E.genericPoint} := fun E => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      (isClosed_singleton_genericPoint hdim E).closure_eq]
  refine ⟨fun E _ => ?_, fun x => ?_⟩
  · have := E.integral
    apply isSmoothScheme_of_topologicalKrullDim_eq_zero
    have hrange := Scheme.IdealSheafData.range_subschemeι E.idealSheaf
    have : Subsingleton E.idealSheaf.subscheme := ⟨fun a b => by
      apply E.idealSheaf.subschemeι.isClosedEmbedding.injective
      have ha : E.idealSheaf.subschemeι a ∈ Set.range E.idealSheaf.subschemeι := ⟨a, rfl⟩
      have hb : E.idealSheaf.subschemeι b ∈ Set.range E.idealSheaf.subschemeι := ⟨b, rfl⟩
      rw [hrange] at ha hb
      change _ ∈ (E.support : Set C) at ha hb
      rw [hsupp] at ha hb
      exact ha.trans hb.symm⟩
    have := Subsingleton.discreteTopology (α := E.idealSheaf.subscheme)
    exact topologicalKrullDim_eq_zero_of_discreteTopology_nonempty
  · rcases eq_genericPoint_or_exists_primeDivisor hdim x with rfl | ⟨P, rfl⟩
    · have hnot : ∀ E : Mori.PrimeDivisor C, genericPoint C ∉ (E.support : Set C) := by
        intro E h
        rw [hsupp] at h
        exact primeDivisor_genericPoint_ne_genericPoint E (Set.mem_singleton_iff.1 h).symm
      refine ⟨0, Fin.elim0, fun E => absurd E.2.2 (hnot E.1), ⟨?_, ?_⟩,
        fun E => absurd E.2.2 (hnot E.1), fun E => absurd E.2.2 (hnot E.1)⟩
      · rw [Set.range_eq_empty, Ideal.span_empty]
        exact (IsLocalRing.isField_iff_maximalIdeal_eq.mp
          (Field.toIsField C.functionField)).symm
      · rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight,
          Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec C).specializes trivial]
        rfl
    · have := P.isDiscreteValuationRing_localRing
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
      have hspan : Ideal.span {ϖ} = IsLocalRing.maximalIdeal P.localRing :=
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ).symm
      have hE : ∀ E : {E : Mori.PrimeDivisor C // E ∈ D.support ∧ P.genericPoint ∈ E.support},
          E.1 = P := fun E => by
        have h := E.2.2
        rw [hsupp] at h
        exact MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes
          (Inseparable.of_eq (Set.mem_singleton_iff.1 h).symm).specializes
      refine ⟨1, ![ϖ], fun _ => 0, ⟨?_, ?_⟩, fun E E' _ => Subtype.ext ((hE E).trans (hE E').symm),
        fun E => ?_⟩
      · rw [Set.range_unique]
        simpa using hspan
      · have : ringKrullDim P.localRing = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one _
        rw [this]; rfl
      · have := P.integral
        rw [hE E]
        change IdealSheafData.stalk P.idealSheaf
          (P.idealSheaf.subschemeι (_root_.genericPoint P.idealSheaf.subscheme)) = _
        rw [AlgebraicGeometry.IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal]
        change _ = Ideal.span {ϖ}
        exact hspan.symm

variable (hvar : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hprop : IsProper sC)
  (hdim : topologicalKrullDim C = 1)

include hvar hsm hprop hdim in
omit [IsNormal C] in
/-- **A smooth proper curve is projective.** It is its own smooth projective compactification. -/
private theorem isProjectiveVariety_of_curve [IsAlgClosed k] : Mori.IsProjectiveVariety k sC := by
  have := hvar.1
  have : AlgebraicGeometry.IsCurve k sC := (AlgebraicGeometry.isCurve_iff k sC).2 ⟨hvar.1, hdim⟩
  have : LocallyOfFiniteType sC := hvar.1.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sC :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : Smooth sC := (MMP.Mori.isSmoothScheme_iff sC).1 hsm
  have hreg : IsRegular C := ((isRegular_tfae C).out 1 2 rfl rfl).mpr
    ⟨inferInstance, fun x => isRegularLocalRing_stalk_of_smooth_over_field sC x⟩
  obtain ⟨-, Y, q, j, hj, hjq, hcq, hproj, -, -, -, -⟩ :=
    exists_smooth_isProjectiveMorphism_compactification_of_perfectField k sC hreg
  have : IsOpenImmersion j := hj
  have : AlgebraicGeometry.IsCurve k q := hcq
  have : IsIntegral Y := ((AlgebraicGeometry.isCurve_iff k q).1 hcq).1.toIsIntegral
  have : IsProper (j ≫ q) := hjq ▸ hprop
  have : IsProper j := IsProper.of_comp j q
  have hsurj : Function.Surjective j.base := by
    have hcl : IsClosed (Set.range j.base) := j.isClosedMap.isClosed_range
    have hop : IsOpen (Set.range j.base) := j.isOpenEmbedding.isOpen_range
    have hne : (Set.range j.base).Nonempty := Set.range_nonempty _
    exact Set.range_eq_univ.1 (IsClopen.eq_univ ⟨hcl, hop⟩ hne)
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).2 ⟨hj, ⟨hsurj⟩⟩
  obtain ⟨n, i, hi, hiq⟩ := hproj
  have : IsClosedImmersion i := hi
  refine { toIsVariety := hvar.1, isProjective := ⟨n, j ≫ i, inferInstance, ?_⟩ }
  rw [Category.assoc, hiq, hjq]

include hvar hsm hdim in
/-- **Curve pairs with boundary `0 ≤ B ≤ 1` are dlt.** -/
private theorem isDltPair_of_curve [IsAlgClosed k] {B : QDivisor C}
    (hB : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1)
    (hpair : MMP.Mori.IsPair sC B) : MMP.Intersection.IsDltPair sC B := by
  have := hvar.1
  have : LocallyOfFiniteType sC := hvar.1.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sC :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : Smooth sC := (MMP.Mori.isSmoothScheme_iff sC).1 hsm
  refine ⟨⟨hpair, fun P => (hB P).1, fun n D a hD => ?_⟩, fun P => (hB P).2, ⊥, ?_, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := exists_primeDivisor_valuation_eq_of_curve hvar hdim D
    obtain ⟨n₀, h₀⟩ := isLogDiscrepancy_ofPrimeDivisor hvar hpair P
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD h₀ hP]
    have : (B.coeff P : ℝ) ≤ 1 := by exact_mod_cast (hB P).2
    linarith
  · exact (MMP.Mori.isSmoothScheme_iff _).2 inferInstance
  · have hU : (⊥ : TopologicalSpace.Closeds C).compl = ⊤ := by
      ext x; simp
    rw [hU]
    have : IsIso (⊤ : C.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    have hdim' : topologicalKrullDim (⊤ : C.Opens).toScheme = 1 := by
      rw [IsHomeomorph.topologicalKrullDim_eq _
        (Scheme.homeoOfIso (asIso (⊤ : C.Opens).ι)).isHomeomorph, hdim]
    exact isSNC_of_curve hdim' _
  · intro n D hD
    obtain ⟨x, hx⟩ := D.center.isIrreducible.nonempty
    exact absurd (hD hx) (by simp)

end Setting

/-! ### The stratified setting for a finite collection of curve pairs -/

section SettingCollection

variable {k : Type u} [Field k] [CharZero k]

/-- On a scheme of dimension zero every point has coheight zero, so there are no prime
divisors. -/
private theorem isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero {S : Scheme.{u}}
    (hS : topologicalKrullDim S = 0) : IsEmpty (Mori.PrimeDivisor S) := by
  refine ⟨fun P => ?_⟩
  have h := coheight_le_of_topologicalKrullDim_eq hS P.genericPoint
  rw [P.coheight_genericPoint] at h
  exact absurd h (by decide)

variable {I : Type*} [Finite I] {X : I → Scheme.{u}} {sX : ∀ i, X i ⟶ Spec (.of k)}
  [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
  (hvar : ∀ i, IsNormalVariety k (sX i)) (hsm : ∀ i, IsSmoothScheme (sX i))
  (hprop : ∀ i, IsProper (sX i)) (hdim : ∀ i, topologicalKrullDim (X i) = 1)
  {B : ∀ i, QDivisor (X i)} (hB : ∀ i P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1)
  {K : ∀ i, Divisor (X i)} (hK : ∀ i, (K i).IsCanonicalDivisor (sX i) 1)

include hvar hsm hprop hdim hB hK

/-- **The stratified setting.** The curve pairs form a stratified section setting in every
positive even degree divisible by a common denominator of the boundaries. -/
private theorem exists_isStratifiedSectionSetting [IsAlgClosed k] :
    ∃ m₁ : ℕ, 0 < m₁ ∧ ∀ m : ℕ, 0 < m → m₁ ∣ m → Even m →
      IsStratifiedSectionSetting sX B 1 m := by
  obtain ⟨d, hd, hBd⟩ := exists_common_denominator B
  have hpair : ∀ i, MMP.Mori.IsPair (sX i) (B i) := fun i =>
    isPair_of_curve (hvar i) (hsm i) (hK i) hd (hBd i)
  refine ⟨d, hd, fun m hm hdm hev => ⟨inferInstance, fun i =>
    isProjectiveVariety_of_curve (hvar i) (hsm i) (hprop i) (hdim i),
    fun i => ⟨inferInstance, inferInstance, hpair i, fun P => (hB i P).1⟩,
    fun i => isDltPair_of_curve (hvar i) (hsm i) (hdim i) (hB i) (hpair i),
    fun i => by rw [hdim i]; rfl, hev, hm, ?_⟩⟩
  intro i S ι BS F
  have := F.isIntegral_stratum
  have := F.isNormal_stratum
  have := F.isLocallyNoetherian_stratum
  have : LocallyOfFiniteType (ι ≫ sX i) := F.isNormalVariety.1.toLocallyOfFiniteType
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim S = e :=
    ⟨_, topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX i)⟩
  have hlen := F.dim_add_length (hdim i) he
  rcases Nat.eq_zero_or_pos F.length with h0 | h0
  · cases F with
    | step => simp [StratumAdjunctionData.length] at h0
    | refl hp =>
      have hBm : ∀ P, ∃ z : ℤ, (m : ℚ) * (B i).coeff P = z := fun P => by
        obtain ⟨t, rfl⟩ := hdm
        obtain ⟨z, hz⟩ := hBd i P
        exact ⟨z * t, by push_cast; rw [← hz]; ring⟩
      refine ⟨1, K i, by rw [Category.id_comp]; exact hK i,
        (m : ℤ) • K i + DivisorWithCoeffs.roundDown ((m : ℤ) • B i),
        toQDivisor_smul_add_roundDown hBm, MMP.Fourfold.isCartier_of_isSmoothScheme (hsm i) _⟩
  · have he0 : e = 0 := by omega
    subst he0
    have hS0 : topologicalKrullDim S = 0 := by rw [he]; rfl
    have hsmS : IsSmoothScheme (ι ≫ sX i) := isSmoothScheme_of_topologicalKrullDim_eq_zero hS0
    have : MMP.Mori.IsVariety k (ι ≫ sX i) := F.isNormalVariety.1
    have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (ι ≫ sX i)
    obtain ⟨KS, hKS⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (ι ≫ sX i) hsmS
      (n := 0) (by rw [hS0]; rfl)
    have := isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero hS0
    exact ⟨0, KS, hKS, 0, Subsingleton.elim _ _, Divisor.isCartier_zero⟩

end SettingCollection

/-- **Admissible generators on a finite collection of nef log curves.** Let `(C_i, B_i)` be
finitely many smooth connected proper curves over an algebraically closed field `k` of
characteristic zero with `ℚ`-boundaries `0 ≤ B_i ≤ 1` and `deg(K_{C_i} + B_i) ≥ 0`. Then there
is `m₀ > 0` such that for every positive even multiple `m` of `m₀` the collection is a
stratified section setting in degree `m` (`MMP.Fourfold.IsStratifiedSectionSetting`), and for
every residue restriction `R` in degree `m` the admissible systems
`MMP.Fourfold.admissibleSections R` generate `𝒪_{C_i}(m(K_{C_i} + B_i))` near every point of
every `C_i`. -/
@[mmp "thm_mmp_curve_admissible_sections_generate"]
public theorem exists_admissibleSections_generatesOn_of_curve
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {I : Type*} [Finite I]
    {X : I → Scheme.{u}} {sX : ∀ i, X i ⟶ Spec (.of k)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (hvar : ∀ i, Mori.IsNormalVariety k (sX i)) (hsm : ∀ i, IsSmoothScheme (sX i))
    (hprop : ∀ i, IsProper (sX i)) (hdim : ∀ i, topologicalKrullDim (X i) = 1)
    {B : ∀ i, QDivisor (X i)} (hB : ∀ i P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1)
    {K : ∀ i, Divisor (X i)} (hK : ∀ i, (K i).IsCanonicalDivisor (sX i) 1)
    (hdeg : ∀ i, 0 ≤ ((K i).sum fun _ a => (a : ℚ)) + (B i).sum fun _ a => a) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → Even m →
      IsStratifiedSectionSetting sX B 1 m ∧
      ∀ (R : ResidueRestriction sX B 1 m) (i : I) (x : X i),
        ∃ s ∈ admissibleSections R, ∃ U : (X i).Opens, x ∈ U ∧
          Mori.GeneratesOn (B i) m U (s i).1 := by
  obtain ⟨m₁, hm₁, h₁⟩ := exists_isStratifiedSectionSetting hvar hsm hprop hdim hB hK
  obtain ⟨m₂, hm₂, h₂⟩ := exists_admissibleSections_generatesOn hvar hsm hprop hdim hB hK hdeg
  refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun m hm hdvd hev => ⟨?_, ?_⟩⟩
  · exact h₁ m hm (dvd_trans (dvd_mul_right _ _) hdvd) hev
  · exact h₂ m hm (dvd_trans (dvd_mul_left _ _) hdvd)

end MMP.Fourfold
