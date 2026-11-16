module

public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Centers and valuations of divisors over a variety (KM 2.24–2.28)

Let `X` be a variety over `k` and `(Y, f, E)` a divisor over `X`, with valuation `v(E, Y)` of
`k(X)` and center `center_X E = closure f(E)`.

* The center depends only on the valuation: `v(E, Y) = v(E', Y')` gives `f(η_E) = f'(η_{E'})`.
* For `X` normal, `codim_X center_X E ≥ 2` if and only if `v(E, Y)` is not the valuation `v(P, X)`
  of any prime divisor `P` of `X`.
* For `X` normal, if `center_X E` is a prime divisor `P` of `X`, then `v(E, Y) = v(P, X)`.

Here `v(P, X)` is the valuation of the divisor `(X, 𝟙_X, P)` over `X`
(`MMP.Mori.DivisorOver.ofPrimeDivisor`).

## Main results

* `MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq`,
  `MMP.Positivity.DivisorOver.center_eq_of_valuation_eq`
* `MMP.Positivity.DivisorOver.two_le_codimension_center_iff`
* `MMP.Positivity.DivisorOver.valuation_eq_of_center_eq`
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity.DivisorOver

open MMP.Mori

open scoped WithZero

/-! ### Valuations dominating a discrete valuation ring -/

section DVR

variable {R K : Type*} [CommRing R]

section Generic

variable [CommRing K] [Algebra R K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- A valuation which is at most `1` on `R` takes the value `1` on the units of `R`. -/
theorem valuation_algebraMap_unit_eq_one (w : Valuation K Γ₀)
    (h1 : ∀ r, w (algebraMap R K r) ≤ 1) (u : Rˣ) : w (algebraMap R K u) = 1 :=
  Valuation.Integers.one_of_isUnit' u.isUnit h1

/-- A valuation which is at most `1` on `R` takes the value `w(ϖ) ^ n` on `u * ϖ ^ n`, for
`u` a unit of `R`. -/
theorem valuation_algebraMap_eq_pow (w : Valuation K Γ₀) (h1 : ∀ r, w (algebraMap R K r) ≤ 1)
    {r ϖ : R} {n : ℕ} {u : Rˣ} (hr : r = u * ϖ ^ n) :
    w (algebraMap R K r) = w (algebraMap R K ϖ) ^ n := by
  rw [hr, map_mul, map_mul, valuation_algebraMap_unit_eq_one w h1, one_mul, map_pow, map_pow]

end Generic

variable [Field K] [Algebra R K] [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

/-- A valuation of `K` with values in `ℤᵐ⁰`, dominating the discrete valuation ring `R` and
taking the value `exp (-1)`, takes the value `exp (-1)` on every uniformizer of `R`. -/
theorem valuation_algebraMap_of_irreducible (w : Valuation K ℤᵐ⁰)
    (h1 : ∀ r, w (algebraMap R K r) ≤ 1)
    (h2 : ∀ r ∈ IsLocalRing.maximalIdeal R, w (algebraMap R K r) < 1)
    (h3 : ∃ g, w g = WithZero.exp (-1)) {ϖ : R} (hϖ : Irreducible ϖ) :
    w (algebraMap R K ϖ) = WithZero.exp (-1) := by
  obtain ⟨g, hg⟩ := h3
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [map_zero] at hg
    exact WithZero.exp_ne_zero hg.symm
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hg0
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  rw [map_div₀, valuation_algebraMap_eq_pow w h1 hu, valuation_algebraMap_eq_pow w h1 hu'] at hg
  set c := w (algebraMap R K ϖ)
  have hc0 : c ≠ 0 := by
    simp only [c, ne_eq, map_eq_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hϖ.ne_zero
  have hc1 : c < 1 := h2 _ ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
  rw [← WithZero.exp_log hc0] at hc1 hg ⊢
  rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_sub] at hg
  have hg' := WithZero.exp_injective hg
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hc1
  have : WithZero.log c * ((n : ℤ) - m) = -1 := by
    rw [← hg']
    simp [nsmul_eq_mul]
    ring
  rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one this with h | h
  · omega
  · rw [h]

/-- Two valuations of `K` with values in `ℤᵐ⁰`, both dominating the discrete valuation ring `R`
with fraction field `K` and both taking the value `exp (-1)`, are equal. -/
theorem valuation_eq_of_isDiscreteValuationRing {w w' : Valuation K ℤᵐ⁰}
    (h1 : ∀ r, w (algebraMap R K r) ≤ 1)
    (h2 : ∀ r ∈ IsLocalRing.maximalIdeal R, w (algebraMap R K r) < 1)
    (h3 : ∃ g, w g = WithZero.exp (-1)) (h1' : ∀ r, w' (algebraMap R K r) ≤ 1)
    (h2' : ∀ r ∈ IsLocalRing.maximalIdeal R, w' (algebraMap R K r) < 1)
    (h3' : ∃ g, w' g = WithZero.exp (-1)) : w = w' := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  ext g
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  by_cases ha0 : a = 0
  · simp [ha0]
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  rw [map_div₀, map_div₀, valuation_algebraMap_eq_pow w h1 hu,
    valuation_algebraMap_eq_pow w h1 hu', valuation_algebraMap_eq_pow w' h1' hu,
    valuation_algebraMap_eq_pow w' h1' hu', valuation_algebraMap_of_irreducible w h1 h2 h3 hϖ,
    valuation_algebraMap_of_irreducible w' h1' h2' h3' hϖ]

end DVR

/-! ### Centers of valuations on a separated scheme -/

section Center

variable {X : Scheme.{u}} [IsIntegral X]

/-- A point `z` whose local ring is dominated by the valuation ring of `w` gives a morphism
`Spec 𝒪_w ⟶ X` extending the generic point and sending the closed point to `z`. -/
theorem exists_spec_valuationSubring_hom (w : Valuation X.functionField ℤᵐ⁰) (z : X)
    (h1 : ∀ a : X.presheaf.stalk z, w (algebraMap _ X.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z),
      w (algebraMap _ X.functionField a) < 1) :
    ∃ l : Spec (.of w.valuationSubring) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap w.valuationSubring X.functionField)) ≫ l =
        X.fromSpecStalk (genericPoint X) ∧
      l (IsLocalRing.closedPoint w.valuationSubring) = z := by
  let φ : X.presheaf.stalk z →+* w.valuationSubring :=
    (algebraMap (X.presheaf.stalk z) X.functionField).codRestrict w.valuationSubring
      fun a => (w.mem_valuationSubring_iff _).2 (h1 a)
  haveI hφ : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hlt := h2 a ((IsLocalRing.mem_maximalIdeal _).2 hna)
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    have hb' : algebraMap _ X.functionField a * (b : X.functionField) = 1 :=
      congrArg Subtype.val hb
    exact (mul_lt_one_of_lt_of_le hlt ((w.mem_valuationSubring_iff _).1 b.2)).ne
      (by rw [← map_mul, hb', map_one])
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z, ?_, ?_⟩
  · have hc : CommRingCat.ofHom φ ≫
        CommRingCat.ofHom (algebraMap w.valuationSubring X.functionField) =
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
      ext a
      rfl
    rw [← Spec.map_comp_assoc, hc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  · change X.fromSpecStalk z (Spec.map (CommRingCat.ofHom φ)
      (IsLocalRing.closedPoint w.valuationSubring)) = z
    haveI : IsLocalHom (CommRingCat.ofHom φ).hom := hφ
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- **The center of a valuation on a separated scheme is unique** (valuative criterion of
separatedness). Two points of an integral scheme separated over `Spec k` whose local rings are
both dominated by the valuation ring of `w` are equal. -/
theorem eq_of_dominates {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) [IsSeparated sX]
    (w : Valuation X.functionField ℤᵐ⁰) {x x' : X}
    (h1 : ∀ a : X.presheaf.stalk x, w (algebraMap _ X.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      w (algebraMap _ X.functionField a) < 1)
    (h1' : ∀ a : X.presheaf.stalk x', w (algebraMap _ X.functionField a) ≤ 1)
    (h2' : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x'),
      w (algebraMap _ X.functionField a) < 1) : x = x' := by
  obtain ⟨l, hl, hlx⟩ := exists_spec_valuationSubring_hom w x h1 h2
  obtain ⟨l', hl', hlx'⟩ := exists_spec_valuationSubring_hom w x' h1' h2'
  let α := CommRingCat.ofHom (algebraMap w.valuationSubring X.functionField)
  have key : ∀ g g' : Spec (.of w.valuationSubring) ⟶ Spec (.of k),
      Spec.map α ≫ g = Spec.map α ≫ g' → g = g' := by
    intro g g' h
    obtain ⟨p, rfl⟩ : ∃ p, Spec.map p = g := ⟨_, Spec.map_preimage g⟩
    obtain ⟨p', rfl⟩ : ∃ p, Spec.map p = g' := ⟨_, Spec.map_preimage g'⟩
    rw [← Spec.map_comp, ← Spec.map_comp] at h
    congr 1
    ext c
    exact congrArg (fun q => q.hom c) (Spec.map_injective h)
  have hll : l' ≫ sX = l ≫ sX := key _ _ (by rw [← Category.assoc, ← Category.assoc, hl, hl'])
  let S : ValuativeCommSq sX :=
    { R := w.valuationSubring
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := l ≫ sX
      commSq := ⟨by rw [← hl, Category.assoc]⟩ }
  have hS := IsSeparated.valuativeCriterion sX S
  let L : S.commSq.LiftStruct := ⟨l, hl, rfl⟩
  let L' : S.commSq.LiftStruct := ⟨l', hl', hll⟩
  have hLL := congrArg CommSq.LiftStruct.l (Subsingleton.elim L L')
  rw [← hlx, ← hlx']
  exact congrArg (fun m : Spec (.of w.valuationSubring) ⟶ X =>
    m (IsLocalRing.closedPoint w.valuationSubring)) hLL

end Center

/-! ### The local ring at the image of the generic point -/

section Dominates

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]

/-- The valuation of a divisor `D` over `X` is at most `1` on the local ring of `X` at the image
of the generic point of `D.E`. -/
theorem valuation_algebraMap_le_one (D : MMP.Mori.DivisorOver k sX) (z : X)
    (hz : z = D.f D.E.genericPoint) (a : X.presheaf.stalk z) :
    D.valuation (algebraMap _ X.functionField a) ≤ 1 := by
  subst hz
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  change D.E.divisorialValuation (functionFieldMap D.f _) ≤ 1
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk,
    MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
  exact ⟨_, rfl⟩

/-- The valuation of a divisor `D` over `X` is less than `1` on the maximal ideal of the local
ring of `X` at the image of the generic point of `D.E`. -/
theorem valuation_algebraMap_lt_one (D : MMP.Mori.DivisorOver k sX) (z : X)
    (hz : z = D.f D.E.genericPoint) (a : X.presheaf.stalk z)
    (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z)) :
    D.valuation (algebraMap _ X.functionField a) < 1 := by
  subst hz
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  change D.E.divisorialValuation (functionFieldMap D.f _) < 1
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk,
    MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
    (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)

/-- The valuation of a divisor over `X` takes the value `exp (-1)` at some element of `k(X)`. -/
theorem exists_valuation_eq_exp_neg_one (D : MMP.Mori.DivisorOver k sX) :
    ∃ g, D.valuation g = WithZero.exp (-1) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := D.E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.E.localRing
  obtain ⟨g, hg⟩ := (MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective
    D.isBirationalMorphism).2 (algebraMap D.E.localRing D.Y.functionField ϖ)
  refine ⟨g, ?_⟩
  change D.E.divisorialValuation (functionFieldMap D.f g) = _
  rw [hg, MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_of_irreducible _ hϖ]

/-- The center of a divisor over `X` is the closure of the point `f(η_E)`. -/
theorem center_eq_closureSingleton (D : MMP.Mori.DivisorOver k sX) :
    D.center = IrreducibleCloseds.closureSingleton (D.f D.E.genericPoint) :=
  IrreducibleCloseds.ext D.center_eq_closure_genericPoint

/-- The codimension of the center of a divisor over `X` is the coheight of `f(η_E)`. -/
theorem codimension_center (D : MMP.Mori.DivisorOver k sX) :
    codimension D.center = Order.coheight (D.f D.E.genericPoint) := by
  have hEq : (irreducibleSetEquivPoints (α := X)).symm (D.f D.E.genericPoint) = D.center :=
    (center_eq_closureSingleton D).symm
  rw [codimension_eq_coheight, ← hEq, Order.coheight_orderIso]

/-- If `f(η_E)` is the generic point of a prime divisor `P` of a normal variety `X`, then
`v(E, Y) = v(P, X)`. -/
theorem valuation_eq_of_map_genericPoint_eq (hX : IsNormalVariety k sX)
    (D : MMP.Mori.DivisorOver k sX) (P : MMP.Mori.PrimeDivisor X)
    (hx : D.f D.E.genericPoint = P.genericPoint) :
    D.valuation = (DivisorOver.ofPrimeDivisor k hX P).valuation := by
  haveI : IsNormal X := hX.2
  haveI : IsLocallyNoetherian X := (DivisorOver.ofPrimeDivisor k hX P).isLocallyNoetherian
  haveI := P.isDiscreteValuationRing_localRing
  have hP' : (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation := by
    ext g
    change P.divisorialValuation (functionFieldMap (𝟙 X) g) = _
    rw [MMP.Mori.functionFieldMap_id_apply]
  rw [hP']
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  refine valuation_eq_of_isDiscreteValuationRing (R := P.localRing)
    (valuation_algebraMap_le_one D _ hx.symm) (valuation_algebraMap_lt_one D _ hx.symm)
    (exists_valuation_eq_exp_neg_one D) (fun r => ?_)
    (fun r hr => (P.divisorialValuation_algebraMap_lt_one_iff r).2 hr)
    ⟨_, P.divisorialValuation_algebraMap_of_irreducible hϖ⟩
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
  exact ⟨r, rfl⟩

/-- The map from the stalk at the generic point of an integral scheme to its function field is
surjective. -/
theorem algebraMap_stalk_surjective_of_eq_genericPoint (z : X) (hz : z = genericPoint X) :
    Function.Surjective (algebraMap (X.presheaf.stalk z) X.functionField) := by
  refine IsFractionRing.surjective_iff_isField.2 ?_
  subst hz
  exact Field.toIsField X.functionField

/-- The image `f(η_E)` of the generic point of `D.E` has nonzero coheight, i.e. it is not the
generic point of `X`. -/
theorem coheight_map_genericPoint_ne_zero (D : MMP.Mori.DivisorOver k sX) :
    Order.coheight (D.f D.E.genericPoint) ≠ 0 := by
  intro h0
  have hsp : genericPoint X ⤳ D.f D.E.genericPoint := (genericPoint_spec X).specializes trivial
  have hx : D.f D.E.genericPoint = genericPoint X :=
    (show D.f D.E.genericPoint ⤳ genericPoint X from (Order.coheight_eq_zero.1 h0) hsp).antisymm
      hsp |>.eq
  obtain ⟨g, hg⟩ := exists_valuation_eq_exp_neg_one D
  obtain ⟨a, ha⟩ := algebraMap_stalk_surjective_of_eq_genericPoint _ hx g⁻¹
  have hle := valuation_algebraMap_le_one D _ rfl a
  rw [ha, map_inv₀, hg, ← WithZero.exp_neg, neg_neg] at hle
  exact absurd hle (by decide)

end Dominates

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]

/-- **KM Def. 2.24, the center depends only on the valuation.** Let `(Y, f, E)` and `(Y', f', E')`
be divisors over a variety `X` with `v(E, Y) = v(E', Y')`. Then `f(η_E) = f'(η_{E'})`. -/
@[mmp "lem_km2b_center_depends_only_on_valuation"]
theorem map_genericPoint_eq_of_valuation_eq (hX : MMP.Mori.IsVariety k sX)
    {D D' : MMP.Mori.DivisorOver k sX} (h : D.valuation = D'.valuation) :
    D.f D.E.genericPoint = D'.f D'.E.genericPoint := by
  haveI := hX.toIsSeparated
  exact eq_of_dominates sX D.valuation (valuation_algebraMap_le_one D _ rfl)
    (valuation_algebraMap_lt_one D _ rfl)
    (fun a => by rw [h]; exact valuation_algebraMap_le_one D' _ rfl a)
    (fun a ha => by rw [h]; exact valuation_algebraMap_lt_one D' _ rfl a ha)

/-- **KM Def. 2.24.** Divisors over a variety `X` with the same valuation have the same center. -/
@[mmp "lem_km2b_center_depends_only_on_valuation"]
theorem center_eq_of_valuation_eq (hX : MMP.Mori.IsVariety k sX)
    {D D' : MMP.Mori.DivisorOver k sX} (h : D.valuation = D'.valuation) :
    D.center = D'.center := by
  rw [center_eq_closureSingleton, center_eq_closureSingleton,
    map_genericPoint_eq_of_valuation_eq hX h]

/-- **KM Def. 2.28, "equivalently".** Let `X` be a normal variety and `(Y, f, E)` a divisor over
`X`. Then `codim_X center_X E ≥ 2` if and only if `v(E, Y) ≠ v(P, X)` for every prime divisor `P`
of `X`. -/
@[mmp "lem_km2b_exceptional_iff_center_codim_two"]
theorem two_le_codimension_center_iff (hX : IsNormalVariety k sX)
    (D : MMP.Mori.DivisorOver k sX) :
    2 ≤ codimension D.center ↔
      ∀ P : MMP.Mori.PrimeDivisor X,
        D.valuation ≠ (DivisorOver.ofPrimeDivisor k hX P).valuation := by
  rw [codimension_center]
  constructor
  · intro h2 P hv
    have hx : D.f D.E.genericPoint = P.genericPoint := map_genericPoint_eq_of_valuation_eq hX.1 hv
    rw [hx, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  · intro hP
    by_contra hlt
    rcases (show Order.coheight (D.f D.E.genericPoint) = 0 ∨
        Order.coheight (D.f D.E.genericPoint) = 1 by
      have hlt' := not_le.mp hlt
      generalize Order.coheight (D.f D.E.genericPoint) = c at hlt' ⊢
      induction c using ENat.recTopCoe with
      | top => exact absurd hlt' (by simp)
      | coe n =>
        norm_cast at hlt' ⊢
        omega) with h0 | h1
    · exact coheight_map_genericPoint_ne_zero D h0
    · let P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
      exact hP P (valuation_eq_of_map_genericPoint_eq hX D P
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm)

/-- **KM 2.25, 2.28.** Let `X` be a normal variety and `(Y, f, E)` a divisor over `X` whose center
is a prime divisor `P` of `X`. Then `v(E, Y) = v(P, X)`. -/
@[mmp "lem_km2b_center_divisor_same_valuation"]
theorem valuation_eq_of_center_eq (hX : IsNormalVariety k sX) (D : MMP.Mori.DivisorOver k sX)
    (P : MMP.Mori.PrimeDivisor X) (hP : (D.center : Set X) = P.support) :
    D.valuation = (DivisorOver.ofPrimeDivisor k hX P).valuation := by
  refine valuation_eq_of_map_genericPoint_eq hX D P ?_
  have : closure {D.f D.E.genericPoint} = closure {P.genericPoint} := by
    rw [← D.center_eq_closure_genericPoint, hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact (inseparable_iff_closure_eq.2 this).eq

end MMP.Positivity.DivisorOver
