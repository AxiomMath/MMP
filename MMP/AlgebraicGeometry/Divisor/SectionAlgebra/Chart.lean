module

public import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Birational
public import MMP.AlgebraicGeometry.Divisor.PrimeDivisorValuationSubring
public import MMP.RingTheory.DiscreteValuationRing.IntersectionHeightOne

/-!
# The affine charts of the relative `Proj` of a divisorial algebra

Let `Y` be an integral, locally Noetherian, normal scheme, `D` a Weil divisor on `Y`, `W` an open
of `Y` and `f ∈ 𝒪_Y(D)(W)` a nonzero section of degree one of `S = ⨁_n 𝒪_Y(nD)(W)`. The ring of
the chart `D₊(f)` of `Proj S` is the degree-zero part of `S_f`, the fractions `s / fⁿ` with
`s ∈ 𝒪_Y(nD)(W)`. Viewing everything inside the function field `K(Y)`, it is the intersection of
the valuation rings `𝒪_{Y,E}` over the prime divisors `E` meeting `W` along which
`v_E(f) + D_E = 0`.

## Main definitions

* `MMP.Fourfold.DivisorialSectionAlgebra.sectionRingToFunctionField`: the section ring
  `⨁_n 𝒪_Y(nD)(W)` to `K(Y)`, `∑ sₙ ↦ ∑ sₙ`.
* `MMP.Fourfold.DivisorialSectionAlgebra.awayToFunctionField`: the chart ring
  `S_{(f)}` to `K(Y)`, `s / fⁿ ↦ s / fⁿ`.

## Main results

* `MMP.Fourfold.DivisorialSectionAlgebra.awayToFunctionField_injective`: the chart ring embeds
  in `K(Y)`.
* `MMP.Fourfold.DivisorialSectionAlgebra.awayToFunctionField_mem_valuationSubring`,
  `MMP.Fourfold.DivisorialSectionAlgebra.mem_range_awayToFunctionField`: its image is the
  intersection of the `𝒪_{Y,E}` over the prime divisors `E` meeting `W` with `v_E(f) = -D_E`.
* `MMP.Fourfold.DivisorialSectionAlgebra.exists_primeDivisor_of_height_one`: every height-one
  prime of the chart ring is the centre of one of these `𝒪_{Y,E}`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], Lemma 6.2.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite HomogeneousLocalization Polynomial

universe u

namespace MMP.Mori

variable {X : Scheme.{u}} [IsIntegral X]

/-- On an integral scheme, the components of a section of `𝒦_X` over an open have the same image
in the function field. -/
theorem algebraMap_rationalFunctionsPresheaf_apply_eq {W : X.Opens}
    (φ : ToType ((rationalFunctionsPresheaf X).obj (op W)))
    (i j : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W}) :
    algebraMap _ X.functionField (φ i) = algebraMap _ X.functionField (φ j) := by
  obtain rfl : i = j := by
    refine Subtype.ext (Subtype.ext ?_)
    have hi : (i.1 : Set X) ∈ ({Set.univ} : Set (Set X)) :=
      irreducibleComponents_eq_singleton (X := X) ▸ i.1.2
    have hj : (j.1 : Set X) ∈ ({Set.univ} : Set (Set X)) :=
      irreducibleComponents_eq_singleton (X := X) ▸ j.1.2
    exact (Set.mem_singleton_iff.mp hi).trans (Set.mem_singleton_iff.mp hj).symm
  rfl

/-- On an integral scheme, a section of `𝒦_X` over an open is determined by any one component. -/
theorem rationalFunctionsPresheaf_eq_zero_of_apply_eq_zero {W : X.Opens}
    {φ : ToType ((rationalFunctionsPresheaf X).obj (op W))}
    (i : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W}) (h : φ i = 0) :
    φ = 0 := by
  funext j
  apply IsFractionRing.injective _ X.functionField
  rw [algebraMap_rationalFunctionsPresheaf_apply_eq φ j i, h, map_zero]
  exact (map_zero _).symm

end MMP.Mori

namespace MMP.Fourfold.DivisorialSectionAlgebra

open MMP.Mori MMP.Mori.Divisor Stacks.RelativeProj

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y}
  (A : DivisorialSectionAlgebra (𝟙 Y) D) {W : Y.Opens}
  (i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W})

/-- The section ring `⨁_n 𝒪_Y(nD)(W)` to the function field, `∑ sₙ ↦ ∑ sₙ`, read through the
component `i` of `𝒦_Y(W)`. -/
def sectionRingToFunctionField : A.situation.sectionRing W →+* Y.functionField :=
  ((algebraMap _ Y.functionField).comp (Pi.evalRingHom _ i)).comp
    ((Polynomial.evalRingHom 1).comp (A.toPolynomial W))

/-- On a homogeneous section `a` of degree `n`, `sectionRingToFunctionField` is the image of the
`i`-component of `a` in the function field. -/
theorem sectionRingToFunctionField_of (n : ℕ) (a : A.situation.sectionPieces W n) :
    A.sectionRingToFunctionField i (DirectSum.of _ n a) =
      algebraMap _ Y.functionField (A.pieceToRationalFunctions W n a i) := by
  simp only [sectionRingToFunctionField, RingHom.comp_apply, toPolynomial_of, coe_evalRingHom,
    eval_monomial, one_pow, mul_one]
  rfl

/-- A homogeneous section has image zero in the function field if and only if it is zero. -/
theorem sectionRingToFunctionField_of_eq_zero_iff (n : ℕ) (a : A.situation.sectionPieces W n) :
    A.sectionRingToFunctionField i (DirectSum.of _ n a) = 0 ↔ a = 0 := by
  rw [sectionRingToFunctionField_of]
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := rationalFunctionsPresheaf_eq_zero_of_apply_eq_zero i
      (IsFractionRing.injective _ Y.functionField (h.trans (map_zero _).symm))
    rw [pieceToRationalFunctions_apply] at h1
    exact (A.sectionEquiv n (Int.natCast_nonneg n) W).injective
      (Subtype.ext (h1.trans (by rw [map_zero]; rfl)))
  · rintro rfl
    rw [map_zero]
    exact map_zero _

variable {f : A.situation.sectionRing W} (hf : f ∈ A.situation.sectionRingGrading W 1)
  (hf0 : A.sectionRingToFunctionField i f ≠ 0)

/-- The ring `S_{(f)}` of the chart `D₊(f)` to the function field, `s / fⁿ ↦ s / fⁿ`. -/
def awayToFunctionField : Away (A.situation.sectionRingGrading W) f →+* Y.functionField :=
  (IsLocalization.Away.lift f (g := A.sectionRingToFunctionField i)
    (isUnit_iff_ne_zero.mpr hf0)).comp
    (algebraMap (Away (A.situation.sectionRingGrading W) f) (Localization.Away f))

/-- The image of the fraction `s / fⁿ` in the function field, multiplied by the image of `fⁿ`, is
the image of `s`. -/
theorem awayToFunctionField_mk_mul (n : ℕ) (s : A.situation.sectionRing W)
    (hs : s ∈ A.situation.sectionRingGrading W (n • 1)) :
    A.awayToFunctionField i hf0 (Away.mk _ hf n s hs) * A.sectionRingToFunctionField i f ^ n =
      A.sectionRingToFunctionField i s := by
  have h : (Localization.mk s ⟨f ^ n, n, rfl⟩ : Localization.Away f) *
      algebraMap _ (Localization.Away f) (f ^ n) = algebraMap _ (Localization.Away f) s := by
    rw [Localization.mk_eq_mk', IsLocalization.mk'_spec]
  have h' := congrArg (IsLocalization.Away.lift f (g := A.sectionRingToFunctionField i)
    (isUnit_iff_ne_zero.mpr hf0)) h
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, map_pow] at h'
  rw [awayToFunctionField, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  exact h'

set_option backward.isDefEq.respectTransparency false in
include hf in
/-- The chart ring `S_{(f)}` embeds in the function field. -/
theorem awayToFunctionField_injective : Function.Injective (A.awayToFunctionField i hf0) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨n, s, hs, rfl⟩ := Away.mk_surjective _ hf x
  have h := A.awayToFunctionField_mk_mul i hf hf0 n s hs
  rw [hx, zero_mul] at h
  obtain ⟨a, rfl⟩ := hs
  rw [eq_comm, sectionRingToFunctionField_of_eq_zero_iff] at h
  subst h
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, HomogeneousLocalization.val_zero, map_zero, Localization.mk_zero]

omit [IsIntegral Y] in
/-- The order of vanishing of a section of degree `n` along a prime divisor `E` meeting `W` is at
least `-n D_E`. -/
theorem ordGE_pieceToRationalFunctions (n : ℕ) (b : A.situation.sectionPieces W n)
    (E : MMP.Mori.PrimeDivisor Y) (hE : (E.support ∩ W).Nonempty) :
    E.OrdGE (-((n : ℤ) * D.coeff E))
      (A.pieceToRationalFunctions W n b
        ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) := by
  have h := (A.sectionEquiv n (Int.natCast_nonneg n) W b).2 E hE
  rwa [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h

set_option backward.isDefEq.respectTransparency false in
/-- **The chart ring lies in `𝒪_{Y,E}`** for every prime divisor `E` meeting `W` along which the
degree-one section `a` has order exactly `-D_E`. -/
theorem awayToFunctionField_mem_valuationSubring (a : A.situation.sectionPieces W 1)
    (hf0 : A.sectionRingToFunctionField i (DirectSum.of _ 1 a) ≠ 0)
    (x : Away (A.situation.sectionRingGrading W) (DirectSum.of _ 1 a))
    (E : MMP.Mori.PrimeDivisor Y) (hE : (E.support ∩ W).Nonempty)
    (hgood : E.valuation (A.pieceToRationalFunctions W 1 a
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) = WithZero.exp (-D.coeff E)) :
    A.awayToFunctionField i hf0 x ∈ E.valuationSubring := by
  set j : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W} :=
    ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩
  have ha : DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 := ⟨a, rfl⟩
  obtain ⟨n, s, ⟨b, rfl⟩, rfl⟩ := Away.mk_surjective _ ha x
  have h := A.awayToFunctionField_mk_mul i ha hf0 n _ ⟨b, rfl⟩
  rw [sectionRingToFunctionField_of, sectionRingToFunctionField_of,
    algebraMap_rationalFunctionsPresheaf_apply_eq (W := W) (A.pieceToRationalFunctions W 1 a) i j,
    algebraMap_rationalFunctionsPresheaf_apply_eq (W := W)
      (A.pieceToRationalFunctions W (n • 1) b) i j] at h
  obtain ⟨y, hy⟩ := PrimeDivisor.algebraMap_stalk_componentGenericPoint_surjective E.component
    (A.awayToFunctionField i hf0 (Away.mk _ ha n _ ⟨b, rfl⟩))
  rw [← hy] at h ⊢
  rw [← map_pow, ← map_mul] at h
  have h' := IsFractionRing.injective _ Y.functionField h
  rw [PrimeDivisor.algebraMap_mem_valuationSubring_iff]
  have hb := A.ordGE_pieceToRationalFunctions (n • 1) b E hE
  have hc : WithZero.exp (-D.coeff E) ^ n ≠ 0 := pow_ne_zero _ WithZero.exp_ne_zero
  have hv : E.valuation y * WithZero.exp (-D.coeff E) ^ n =
      E.valuation (A.pieceToRationalFunctions W (n • 1) b j) := by
    rw [← hgood, ← map_pow, ← map_mul]
    exact congrArg E.valuation h'
  rcases hb with hb0 | hb
  · left
    rw [hb0, map_zero] at hv
    letI := (RationalFunctions.isField_stalk Y E.component).toField
    exact (map_eq_zero E.valuation).mp ((mul_eq_zero.mp hv).resolve_right hc)
  · right
    have he : WithZero.exp (-(((n • 1 : ℕ) : ℤ) * D.coeff E)) =
        WithZero.exp (-D.coeff E) ^ n := by
      rw [← WithZero.exp_nsmul, smul_eq_mul, mul_one, nsmul_eq_mul, neg_mul_eq_mul_neg]
    rw [he] at hb
    calc WithZero.exp (0 : ℤ)
        = WithZero.exp (-D.coeff E) ^ n * (WithZero.exp (-D.coeff E) ^ n)⁻¹ := by
          rw [mul_inv_cancel₀ hc, WithZero.exp_zero]
      _ ≤ E.valuation (A.pieceToRationalFunctions W (n • 1) b j) *
          (WithZero.exp (-D.coeff E) ^ n)⁻¹ := mul_le_mul_left hb _
      _ = E.valuation y := by rw [← hv, mul_inv_cancel_right₀ hc]

set_option backward.isDefEq.respectTransparency false in
/-- **The chart ring is the intersection of the `𝒪_{Y,E}`.** An element of `K(Y)` lying in
`𝒪_{Y,E}` for every prime divisor `E` meeting `W` along which the degree-one section `a` has order
exactly `-D_E` is a fraction `s / aⁿ` with `s ∈ 𝒪_Y(nD)(W)`. -/
theorem mem_range_awayToFunctionField [CompactSpace Y] (a : A.situation.sectionPieces W 1)
    (hf0 : A.sectionRingToFunctionField i (DirectSum.of _ 1 a) ≠ 0) (x : Y.functionField)
    (hx : ∀ (E : MMP.Mori.PrimeDivisor Y) (hE : (E.support ∩ W).Nonempty),
      E.valuation (A.pieceToRationalFunctions W 1 a
        ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) = WithZero.exp (-D.coeff E) →
      x ∈ E.valuationSubring) :
    x ∈ (A.awayToFunctionField i hf0).range := by
  classical
  have ha : DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 := ⟨a, rfl⟩
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [map_zero, hx0]⟩
  set φf := A.pieceToRationalFunctions W 1 a
  have hχ : A.sectionRingToFunctionField i (DirectSum.of _ 1 a) =
      algebraMap _ Y.functionField (φf i) := A.sectionRingToFunctionField_of i 1 a
  choose y hy using fun Z : irreducibleComponents Y =>
    PrimeDivisor.algebraMap_stalk_componentGenericPoint_surjective Z x
  have hy0 : ∀ Z, y Z ≠ 0 := fun Z h0 => hx0 (by rw [← hy Z, h0, map_zero])
  have hS := PrimeDivisor.finite_notMem_valuationSubring hx0
  set n : ℕ := hS.toFinset.sup fun E => (-WithZero.log (E.valuation (y E.component))).toNat
  set σ : ToType ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W))) :=
    fun Z => y Z.1 * φf Z ^ n
  have hσ : σ ∈ ((((n • 1 : ℕ)) : ℤ) • D).divisorialSubmodule ((𝟙 Y) ⁻¹ᵁ W) := by
    intro E hE
    set j : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W} :=
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩
    rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul, smul_eq_mul, mul_one]
    have hfj : φf j ≠ 0 := fun h0 => hf0 (by
      rw [hχ, algebraMap_rationalFunctionsPresheaf_apply_eq (W := W) φf i j, h0, map_zero])
    have hfE : WithZero.exp (-D.coeff E) ≤ E.valuation (φf j) := by
      have h := A.ordGE_pieceToRationalFunctions 1 a E hE
      rw [show -(((1 : ℕ) : ℤ) * D.coeff E) = -D.coeff E by simp] at h
      exact h.resolve_left hfj
    right
    change WithZero.exp _ ≤ E.valuation (y E.component * φf j ^ n)
    rw [map_mul, map_pow]
    by_cases hxE : x ∈ E.valuationSubring
    · have hyE : WithZero.exp 0 ≤ E.valuation (y E.component) := by
        have h := (PrimeDivisor.algebraMap_mem_valuationSubring_iff E (y E.component)).mp
          (by rw [hy]; exact hxE)
        exact h.resolve_left (hy0 _)
      calc WithZero.exp (-((n : ℤ) * D.coeff E))
          = WithZero.exp 0 * WithZero.exp (-D.coeff E) ^ n := by
            rw [← WithZero.exp_nsmul, ← WithZero.exp_add, nsmul_eq_mul, zero_add,
              neg_mul_eq_mul_neg]
        _ ≤ _ := mul_le_mul' hyE (pow_le_pow_left' hfE n)
    · have hES : E ∈ hS.toFinset := hS.mem_toFinset.mpr (Or.inl hxE)
      have hbad : E.valuation (φf j) ≠ WithZero.exp (-D.coeff E) := fun h => hxE (hx E hE h)
      have hv0 : E.valuation (φf j) ≠ 0 := ne_of_gt (lt_of_lt_of_le WithZero.exp_pos hfE)
      have hfE' : WithZero.exp (-D.coeff E + 1) ≤ E.valuation (φf j) := by
        rw [← WithZero.exp_log hv0, WithZero.exp_le_exp] at hfE ⊢
        rw [← WithZero.exp_log hv0, WithZero.exp_injective.ne_iff] at hbad
        omega
      have hyv0 : E.valuation (y E.component) ≠ 0 := by
        letI := (RationalFunctions.isField_stalk Y E.component).toField
        exact (map_ne_zero E.valuation).mpr (hy0 _)
      have hle : (-WithZero.log (E.valuation (y E.component))).toNat ≤ n :=
        Finset.le_sup (f := fun E => (-WithZero.log (E.valuation (y E.component))).toNat) hES
      have hyE : WithZero.exp (-(n : ℤ)) ≤ E.valuation (y E.component) := by
        rw [← WithZero.exp_log hyv0, WithZero.exp_le_exp]
        omega
      calc WithZero.exp (-((n : ℤ) * D.coeff E))
          = WithZero.exp (-(n : ℤ)) * WithZero.exp (-D.coeff E + 1) ^ n := by
            rw [← WithZero.exp_nsmul, ← WithZero.exp_add, nsmul_eq_mul]
            congr 1
            ring
        _ ≤ _ := mul_le_mul' hyE (pow_le_pow_left' hfE' n)
  set b : A.situation.sectionPieces W (n • 1) :=
    (A.sectionEquiv _ (Int.natCast_nonneg _) W).symm ⟨σ, hσ⟩
  refine ⟨Away.mk _ ha n (DirectSum.of _ (n • 1) b) ⟨b, rfl⟩, ?_⟩
  have h := A.awayToFunctionField_mk_mul i ha hf0 n _ ⟨b, rfl⟩
  rw [A.sectionRingToFunctionField_of i (n • 1) b, pieceToRationalFunctions_apply,
    AddEquiv.apply_symm_apply] at h
  have hσi : algebraMap _ Y.functionField (σ i) =
      x * A.sectionRingToFunctionField i (DirectSum.of _ 1 a) ^ n := by
    change algebraMap _ Y.functionField (y i.1 * φf i ^ n) = _
    rw [map_mul, map_pow, hy, hχ]
  exact mul_right_cancel₀ (pow_ne_zero n hf0) (h.trans hσi)

/-- **The height-one primes of a chart.** Every height-one prime of the chart ring `S_{(a)}` is
the centre `S_{(a)} ∩ 𝔪_E` of the valuation ring of a prime divisor `E` meeting `W` along which `a`
has order exactly `-D_E`. -/
theorem exists_primeDivisor_of_height_one [CompactSpace Y] (a : A.situation.sectionPieces W 1)
    (hf0 : A.sectionRingToFunctionField i (DirectSum.of _ 1 a) ≠ 0)
    (q : Ideal (Away (A.situation.sectionRingGrading W) (DirectSum.of _ 1 a))) [q.IsPrime]
    (hq0 : q ≠ ⊥) (hq : ∀ p : Ideal (Away (A.situation.sectionRingGrading W) (DirectSum.of _ 1 a)),
      p.IsPrime → p ≠ ⊥ → p ≤ q → p = q) :
    ∃ (E : MMP.Mori.PrimeDivisor Y) (hE : (E.support ∩ W).Nonempty),
      E.valuation (A.pieceToRationalFunctions W 1 a
        ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) = WithZero.exp (-D.coeff E) ∧
      ∀ x, x ∈ q ↔ ∃ hx : A.awayToFunctionField i hf0 x ∈ E.valuationSubring,
        (⟨_, hx⟩ : E.valuationSubring) ∈ IsLocalRing.maximalIdeal E.valuationSubring := by
  let ι := {E : MMP.Mori.PrimeDivisor Y // ∃ hE : (E.support ∩ W).Nonempty,
    E.valuation (A.pieceToRationalFunctions W 1 a
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) = WithZero.exp (-D.coeff E)}
  obtain ⟨⟨E, hE, hgood⟩, h⟩ := MMP.ValuationSubring.exists_iff_mem_maximalIdeal_of_injective
    (A.awayToFunctionField i hf0) (A.awayToFunctionField_injective i ⟨a, rfl⟩ hf0)
    (fun E : ι => E.1.valuationSubring)
    (fun E x => A.awayToFunctionField_mem_valuationSubring i a hf0 x E.1 E.2.1 E.2.2)
    (fun x hx => A.mem_range_awayToFunctionField i a hf0 x fun E hE hgood => hx ⟨E, hE, hgood⟩)
    (fun x hx0 => ((PrimeDivisor.finite_notMem_valuationSubring hx0).preimage
      Subtype.val_injective.injOn).subset fun _ hE => Or.inr hE)
    q hq0 hq
  exact ⟨E, hE, hgood, fun x => (h x).trans ⟨fun hx => ⟨_, hx⟩, fun ⟨_, hx⟩ => hx⟩⟩

end MMP.Fourfold.DivisorialSectionAlgebra
