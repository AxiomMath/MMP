module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModel
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModelGraphDivisor
import MMP.AlgebraicGeometry.MMP.MinimalModel.AmpleModelAdjointAmple
import MMP.AlgebraicGeometry.MMP.MinimalModel.AmpleModelBirational
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus

/-!
# The ample model of a birational contraction: smallness and boundary

Let `(X, B)` be a projective lc fourfold pair over `ℂ` with rational boundary, `D = K_X + B`,
and `f : X ⟶ Z` a birational contraction onto a normal projective variety with `-D` `f`-ample.
Let `(M, B_M, q, V, B_V)` be an ample-model datum of `f`, with structure morphism `p : V ⟶ Z`.
Then `p` is a small morphism — a proper birational morphism of normal varieties whose
exceptional locus has codimension at least two in `V` — and the boundary `B_V = q_* B_M` is the
strict transform `p⁻¹_* f_* B` of `f_* B` on `V`.

*Smallness.* Let `(G, u, v)` be a normalized graph of `X ⤏ V` over `Z` and
`H = u^* D - v^*(K_V + B_V)`. If a point `y ∈ Ex(p)` of codimension one is the generic point of
a prime divisor `P` of `V`, its strict transform `E` on `G` lies over `p(y)`, over which `p` is
not an isomorphism, so `E ⊆ Supp H`; but the coefficient of `E` in `H` is the coefficient of `P`
in `v_* H = 0`.

*The boundary.* Fix a prime divisor `P` of `V`. Since `p` is small, `p` is an isomorphism near
the generic point of `P`, which maps to the generic point of a prime divisor `G` of `Z`. The
proper birational morphisms `f` and `π_M` onto the normal variety `Z` are isomorphisms over every
point of codimension one, so `G` is the image of a unique prime divisor `D` of `X`, and `φ`
sends `D` to the unique prime divisor `F` of `M` over `G`. Then `q_* F = P`, `F` is not
exceptional over `X`, and the coefficients of `P` in `q_* B_M` and in `p⁻¹_* f_* B` are both the
coefficient of `D` in `B`.

## Main results

* `MMP.Fourfold.IsAmpleModelDatum.isSmallMorphism`: `p : V ⟶ Z` is small.
* `MMP.Fourfold.IsAmpleModelDatum.boundary_eq_flipTransform`: `B_V = p⁻¹_* f_* B`.

## Implementation notes

`V` is a variety over `ℂ` through `p ≫ s_Z : V ⟶ Z ⟶ Spec ℂ`, and smallness is
`MMP.Fourfold.IsSmallMorphism` for this structure morphism; its field `comp_eq` then holds by
definition, and normality and properness of `V` are part of the conclusion.

Normality of `V` is not recorded in the datum. `V` is the relative `Proj` of
`𝒜 = ⨁_n π_* 𝒪_M(nD)`, and on the chart `D₊(a)` over an affine `U ⊆ Z` its ring is `𝒜(U)_(a)`.
The ring map `𝒜(U)_(a) → 𝒪_M(M_a)` describing `q` there is bijective: a regular function `s` on
the generating locus `M_a` has poles only along the prime divisors of `π⁻¹U` missing `M_a`, and
`a` vanishes along each of them, so `s aᵐ ∈ H⁰(π⁻¹U, 𝒪_M(mnD))` for large `m`. Hence
`𝒜(U)_(a)` is the ring of functions on the normal integral scheme `M_a`, and is integrally
closed.

The normalized graph is the relative normalization of `X ×_Z V` in the graph of `X ⤏ V` over
the open of `Z` above which `f` and `p` are isomorphisms; it is finite over `X ×_Z V` since
`X ×_Z V` is of finite type over `ℂ`. The canonical divisor `K_V` is `div(p^*ω)` for the top
form `ω` on `Z` with `div(f^*ω) = K_X`, so that `p_* K_V = f_* K_X`.

The strict transform on `V` of `f_* B` is `MMP.Mori.flipTransform f p B`, the push-forward of
`B` along `f` followed by the inverse birational transform along `p`; this is the spelling of the
boundary of a permitted step (`MMP.Fourfold.IsPermittedStep`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Normality of the relative `Proj` -/

section Normality

variable {M Z : Scheme.{u}} [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] {π : M ⟶ Z}
  {D : Divisor M} (A : DivisorialSectionAlgebra π D)

omit [IsLocallyNoetherian M] [IsNormal M] in
private theorem componentGenericPoint_mem {W : M.Opens} (hW : genericPoint M ∈ W)
    (Y : irreducibleComponents M) : componentGenericPoint M Y ∈ W := by
  rwa [componentGenericPoint_eq_genericPoint]

/-- The section of `𝒦_M` over `W` determined by a rational function. -/
private noncomputable def ofRF (W : M.Opens) :
    RationalFunctions M →+* (rationalFunctionsPresheaf M).obj (op W) :=
  RingHom.pi fun Y => Pi.evalRingHom
    (fun Y : irreducibleComponents M => M.presheaf.stalk (componentGenericPoint M Y)) Y.1

omit [IsLocallyNoetherian M] [IsNormal M] in
private theorem ofRF_apply (W : M.Opens) (φ : RationalFunctions M)
    (Y : {Y : irreducibleComponents M // componentGenericPoint M Y ∈ W}) :
    ofRF W φ Y = φ Y.1 := rfl

omit [IsLocallyNoetherian M] [IsNormal M] in
private theorem map_ofRF {W W' : M.Opens} (i : W' ⟶ W) (φ : RationalFunctions M) :
    (rationalFunctionsPresheaf M).map i.op (ofRF W φ) = ofRF W' φ := rfl

omit [IsLocallyNoetherian M] [IsNormal M] in
private theorem exists_ofRF_eq {W : M.Opens} (hW : genericPoint M ∈ W)
    (φ : (rationalFunctionsPresheaf M).obj (op W)) : ∃ ψ, ofRF W ψ = φ :=
  ⟨fun Y => φ ⟨Y, componentGenericPoint_mem hW Y⟩, funext fun _ => rfl⟩

omit [IsLocallyNoetherian M] [IsNormal M] in
private theorem isUnit_of_ne_zero {φ : RationalFunctions M} (hφ : φ ≠ 0) : IsUnit φ := by
  have hall : ∀ Y Y' : irreducibleComponents M, Y = Y' := fun Y Y' =>
    Subtype.ext (((irreducibleComponents_eq_singleton (X := M)).le Y.2).trans
      ((irreducibleComponents_eq_singleton (X := M)).le Y'.2).symm)
  rw [Pi.isUnit_iff]
  intro Y
  have hfield := RationalFunctions.isField_stalk M Y
  let := hfield.toField
  refine isUnit_iff_ne_zero.mpr fun h0 => hφ (funext fun Y' => ?_)
  obtain rfl := hall Y Y'
  exact h0

private theorem ordGE_units_iff (E : MMP.Mori.PrimeDivisor M) (n : ℤ) (w : (RationalFunctions M)ˣ) :
    E.OrdGE n ((w : RationalFunctions M) E.component) ↔ n ≤ E.ord w := by
  have hne : (w : RationalFunctions M) E.component ≠ 0 := by
    intro h0
    have := (Pi.isUnit_iff.mp w.isUnit) E.component
    rw [h0] at this
    exact not_isUnit_zero this
  rw [MMP.Mori.PrimeDivisor.OrdGE, or_iff_right hne, PrimeDivisor.valuation_component,
    WithZero.exp_le_exp]

/-- The open of `π⁻¹U` off the support of `div(a) + nD` lies in the generating locus of `a`. -/
private theorem le_generatingLocus [CompactSpace M] {n : ℕ} {U : Z.Opens}
    (a : (A.algebra.piece (n : ℤ)).val.obj (op U)) (w : (RationalFunctions M)ˣ)
    (hw : ofRF (π ⁻¹ᵁ U) w = (A.sectionEquiv n (Int.natCast_nonneg n) U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))) :
    π ⁻¹ᵁ U ⊓ ⟨((principalDivisor w + (n : ℤ) • D).supp : Set M)ᶜ,
      (principalDivisor w + (n : ℤ) • D).isClosed_supp.isOpen_compl⟩ ≤
      A.generatingLocus (Int.natCast_nonneg n) a := by
  refine le_sSup ⟨inf_le_left, ofRF _ ((w⁻¹ : (RationalFunctions M)ˣ) : RationalFunctions M),
    ?_, ?_⟩
  · intro E hE
    have hE0 : (principalDivisor w + (n : ℤ) • D).coeff E = 0 := by
      by_contra hne
      obtain ⟨x, hxE, hxW⟩ := hE
      exact hxW.2 (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hxE⟩)
    have hcoeff : E.ord w + n * D.coeff E = 0 := by
      simpa [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul] using hE0
    change E.OrdGE _ (((w⁻¹ : (RationalFunctions M)ˣ) : RationalFunctions M) E.component)
    rw [ordGE_units_iff, PrimeDivisor.ord_inv]
    simp only [DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_smul, neg_neg, smul_eq_mul]
    linarith
  · rw [← hw, map_ofRF, ← map_mul, Units.mul_inv, map_one]

omit [IsLocallyNoetherian M] [IsNormal M] in
private theorem toRationalFunctionsPresheaf_injective {L : M.Opens} (hL : genericPoint M ∈ L) :
    Function.Injective ((toRationalFunctionsPresheaf M).app (op L)) := by
  intro r r' h
  let Y0 : irreducibleComponents M := ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩
  exact germ_injective_of_isIntegral M _ (componentGenericPoint_mem hL Y0)
    (congrFun h ⟨Y0, componentGenericPoint_mem hL Y0⟩)

/-- A nonzero section `a` of `𝒜_n` over `U` is a unit rational function, and `π⁻¹U` contains
the generic point of `M`. -/
private theorem exists_unit_ofRF_eq_sectionEquiv {n : ℕ} {U : Z.Opens}
    (a : (A.algebra.piece (n : ℤ)).val.obj (op U)) (ha : a ≠ 0) :
    genericPoint M ∈ π ⁻¹ᵁ U ∧ ∃ w : (RationalFunctions M)ˣ,
      ofRF (π ⁻¹ᵁ U) w = (A.sectionEquiv n (Int.natCast_nonneg n) U a :
        (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) := by
  have hφa0 : (A.sectionEquiv n (Int.natCast_nonneg n) U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ≠ 0 := fun h =>
    ha (by simpa using (Subtype.ext h : A.sectionEquiv n (Int.natCast_nonneg n) U a = 0))
  have hηW : genericPoint M ∈ π ⁻¹ᵁ U := by
    by_contra hW
    exact hφa0 (funext fun Y =>
      absurd (by simpa [componentGenericPoint_eq_genericPoint] using Y.2) hW)
  obtain ⟨fa, hfa⟩ := exists_ofRF_eq hηW (A.sectionEquiv n (Int.natCast_nonneg n) U a).1
  have hfa0 : fa ≠ 0 := by rintro rfl; exact hφa0 (by rw [← hfa, map_zero])
  exact ⟨hηW, (isUnit_of_ne_zero hfa0).unit, hfa⟩

/-- The generating locus of a nonzero section contains the generic point of `M`. -/
private theorem genericPoint_mem_generatingLocus [CompactSpace M] {n : ℕ} {U : Z.Opens}
    (a : (A.algebra.piece (n : ℤ)).val.obj (op U)) (ha : a ≠ 0) :
    genericPoint M ∈ A.generatingLocus (Int.natCast_nonneg n) a := by
  obtain ⟨hηW, w, hw⟩ := exists_unit_ofRF_eq_sectionEquiv A a ha
  exact le_generatingLocus A a w hw ⟨hηW, fun h => by
    obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    exact MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support E hE⟩

/-- A unit rational function has bounded poles: its order along every prime divisor is at
least `-m` for some `m`. -/
private theorem exists_neg_le_ord [CompactSpace M] (u : (RationalFunctions M)ˣ) :
    ∃ m : ℕ, ∀ E : MMP.Mori.PrimeDivisor M, -(m : ℤ) ≤ E.ord u := by
  classical
  refine ⟨∑ E ∈ (principalDivisor u).support, (E.ord u).natAbs, fun E => ?_⟩
  by_cases hE : E ∈ (principalDivisor u).support
  · have h2 : ((E.ord u).natAbs : ℤ) ≤
        ((∑ E ∈ (principalDivisor u).support, (E.ord u).natAbs : ℕ) : ℤ) :=
      Nat.cast_le.mpr <|
        Finset.single_le_sum (f := fun E => (E.ord u).natAbs) (fun _ _ => Nat.zero_le _) hE
    rw [Int.natCast_natAbs] at h2
    linarith [neg_abs_le (E.ord u)]
  · rw [Finsupp.notMem_support_iff] at hE
    rw [show E.ord u = 0 from hE]
    exact neg_nonpos.mpr (Int.natCast_nonneg _)

/-- A nonzero section over an open containing the generic point is a unit rational function. -/
private theorem exists_unit_ofRF_eq_app {L : M.Opens} (hηL : genericPoint M ∈ L) (s : Γ(M, L))
    (hs : s ≠ 0) :
    ∃ us : (RationalFunctions M)ˣ, ofRF L us = (toRationalFunctionsPresheaf M).app (op L) s := by
  obtain ⟨fs, hfs⟩ := exists_ofRF_eq hηL ((toRationalFunctionsPresheaf M).app (op L) s)
  have hfs0 : fs ≠ 0 := by
    rintro rfl
    apply hs
    apply toRationalFunctionsPresheaf_injective hηL
    rw [map_zero, ← hfs, map_zero]
  exact ⟨(isUnit_of_ne_zero hfs0).unit, hfs⟩

/-- A regular function on `L` has nonnegative order along every prime divisor meeting `L`. -/
private theorem ord_nonneg_of_ofRF_eq_app {L : M.Opens} (s : Γ(M, L)) (us : (RationalFunctions M)ˣ)
    (hus : ofRF L us = (toRationalFunctionsPresheaf M).app (op L) s)
    (E : MMP.Mori.PrimeDivisor M) (hE : (E.support ∩ L).Nonempty) : 0 ≤ E.ord us := by
  have h1 : (1 : (rationalFunctionsPresheaf M).obj (op L)) ∈
      (0 : Divisor M).divisorialSubmodule L := by
    intro E' _
    refine Or.inr ?_
    rw [DivisorWithCoeffs.coeff_zero, neg_zero, WithZero.exp_zero]
    exact le_of_eq (map_one _).symm
  have h2 : (toRationalFunctionsPresheaf M).app (op L) s ∈
      (0 : Divisor M).divisorialSubmodule L := by
    have : (toRationalFunctionsPresheaf M).app (op L) s =
        s • (1 : (rationalFunctionsPresheaf M).obj (op L)) := by
      funext Y
      rw [rationalFunctions_smul_apply]
      exact (mul_one _).symm
    rw [this]
    exact Submodule.smul_mem _ _ h1
  have := h2 E hE
  rwa [← hus, ofRF_apply, ordGE_units_iff, DivisorWithCoeffs.coeff_zero, neg_zero] at this

/-- A section `a` of `𝒜_n` over `U` has order at least `-n D_E` along every prime divisor `E`
meeting `π⁻¹U`. -/
private theorem neg_le_ord_of_ofRF_eq_sectionEquiv {n : ℕ} {U : Z.Opens}
    (a : (A.algebra.piece (n : ℤ)).val.obj (op U)) (ua : (RationalFunctions M)ˣ)
    (hua : ofRF (π ⁻¹ᵁ U) ua = (A.sectionEquiv n (Int.natCast_nonneg n) U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))))
    (E : MMP.Mori.PrimeDivisor M) (hE : (E.support ∩ π ⁻¹ᵁ U).Nonempty) :
    -((n : ℤ) * D.coeff E) ≤ E.ord ua := by
  have := (A.sectionEquiv n (Int.natCast_nonneg n) U a).2 E hE
  rwa [← hua, ofRF_apply, ordGE_units_iff, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at this

/-- Along a prime divisor of `π⁻¹U` missing the generating locus of `a`, the section `a`
vanishes. -/
private theorem one_le_ord_add_of_not_nonempty [CompactSpace M] {n : ℕ} {U : Z.Opens}
    (a : (A.algebra.piece (n : ℤ)).val.obj (op U)) (ua : (RationalFunctions M)ˣ)
    (hua : ofRF (π ⁻¹ᵁ U) ua = (A.sectionEquiv n (Int.natCast_nonneg n) U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))))
    (E : MMP.Mori.PrimeDivisor M) (hEW : (E.support ∩ π ⁻¹ᵁ U).Nonempty)
    (hEL : ¬ (E.support ∩ A.generatingLocus (Int.natCast_nonneg n) a).Nonempty) :
    1 ≤ E.ord ua + n * D.coeff E := by
  by_contra hlt
  have hE0 : (principalDivisor ua + (n : ℤ) • D).coeff E = 0 := by
    have := neg_le_ord_of_ofRF_eq_sectionEquiv A a ua hua E hEW
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      coeff_principalDivisor]
    omega
  apply hEL
  refine ⟨E.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
    le_generatingLocus A a ua hua ⟨E.genericPoint_mem_of_nonempty hEW, fun h => ?_⟩⟩
  obtain ⟨E', hE', hηE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hηE
  exact hE' hE0

/-- For `s` regular on the generating locus of `a` with poles of order at most `m`, the rational
function `s aᵐ` is a section of `𝒪_M(mnD)` over `π⁻¹U`. -/
private theorem ofRF_mul_pow_mem_divisorialSubmodule [CompactSpace M] {n : ℕ} {U : Z.Opens}
    (a : (A.algebra.piece (n : ℤ)).val.obj (op U)) (ua : (RationalFunctions M)ˣ)
    (hua : ofRF (π ⁻¹ᵁ U) ua = (A.sectionEquiv n (Int.natCast_nonneg n) U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))))
    (us : (RationalFunctions M)ˣ) (m : ℕ) (hm : ∀ E : MMP.Mori.PrimeDivisor M, -(m : ℤ) ≤ E.ord us)
    (hS : ∀ E : MMP.Mori.PrimeDivisor M,
      (E.support ∩ A.generatingLocus (Int.natCast_nonneg n) a).Nonempty → 0 ≤ E.ord us) :
    ofRF (π ⁻¹ᵁ U) ((us * ua ^ m : (RationalFunctions M)ˣ) : RationalFunctions M) ∈
      (((m • n : ℕ) : ℤ) • D).divisorialSubmodule (π ⁻¹ᵁ U) := by
  intro E hE
  change E.OrdGE _ (((us * ua ^ m : (RationalFunctions M)ˣ) : RationalFunctions M) E.component)
  rw [ordGE_units_iff, PrimeDivisor.ord_mul, PrimeDivisor.ord_pow,
    DivisorWithCoeffs.coeff_smul, smul_eq_mul, nsmul_eq_mul]
  push_cast
  rw [nsmul_eq_mul]
  by_cases hEL : (E.support ∩ A.generatingLocus (Int.natCast_nonneg n) a).Nonempty
  · have h1 := hS E hEL
    have h2 := neg_le_ord_of_ofRF_eq_sectionEquiv A a ua hua E hE
    have h3 : (m : ℤ) * (-((n : ℤ) * D.coeff E)) ≤ m * E.ord ua :=
      mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg m)
    linarith
  · have h1 := hm E
    have h2 := one_le_ord_add_of_not_nonempty A a ua hua E hE hEL
    have h3 : (m : ℤ) * 1 ≤ m * (E.ord ua + n * D.coeff E) :=
      mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg m)
    linarith

/-- If `x aᵐ = s aᵐ` as rational functions on `L`, then `x = s`. -/
private theorem eq_of_app_mul_pow_eq {L W : M.Opens} (hLW : L ≤ W) (hηL : genericPoint M ∈ L)
    (x s : Γ(M, L)) (ua us : (RationalFunctions M)ˣ) (m : ℕ)
    (hus : ofRF L us = (toRationalFunctionsPresheaf M).app (op L) s)
    (h : (toRationalFunctionsPresheaf M).app (op L) x *
        (rationalFunctionsPresheaf M).map (homOfLE hLW).op (ofRF W ua) ^ m =
      (rationalFunctionsPresheaf M).map (homOfLE hLW).op
        (ofRF W ((us * ua ^ m : (RationalFunctions M)ˣ) : RationalFunctions M))) :
    x = s := by
  rw [map_ofRF, map_ofRF, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hus] at h
  have hu : IsUnit (ofRF L (ua : RationalFunctions M) ^ m) := (ua.isUnit.map (ofRF L)).pow m
  exact toRationalFunctionsPresheaf_injective hηL (hu.mul_left_inj.mp h)

/-- **The ring map from the chart ring to the functions on the generating locus is surjective.**
The ring map `𝒜(U)_(a) → 𝒪_M(M_a)` describing the induced morphism on the generating locus of a
nonzero section `a` of positive degree is surjective: a regular function `s` on `M_a` has poles
only along prime divisors of `π⁻¹U` missing `M_a`, along which `a` vanishes, so `s aᵐ` is a
section of `𝒪_M(mnD)` over `π⁻¹U` for `m` large. -/
private theorem surjective_of_factors [CompactSpace M] (U : Z.affineOpens) (n : ℕ)
    (a : (A.algebra.piece (n : ℤ)).val.obj (op U.1)) (ha : a ≠ 0)
    (ψ : HomogeneousLocalization.Away (A.situation.sectionRingGrading U.1)
        (DirectSum.of (A.situation.sectionPieces U.1) n a) →+*
        Γ(M, A.generatingLocus (Int.natCast_nonneg n) a))
    (heq : ∀ (m : ℕ) (t : (A.algebra.piece ((m • n : ℕ) : ℤ)).val.obj (op U.1)),
          (toRationalFunctionsPresheaf M).app (op (A.generatingLocus (Int.natCast_nonneg n) a))
              (ψ (HomogeneousLocalization.Away.mk (A.situation.sectionRingGrading U.1) ⟨a, rfl⟩ m
                (DirectSum.of (A.situation.sectionPieces U.1) (m • n) t) ⟨t, rfl⟩)) *
              (rationalFunctionsPresheaf M).map
                (homOfLE (A.generatingLocus_le _ a)).op
                (A.sectionEquiv n (Int.natCast_nonneg n) U.1 a :
                  (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U.1))) ^ m =
            (rationalFunctionsPresheaf M).map (homOfLE (A.generatingLocus_le _ a)).op
              (A.sectionEquiv _ (Int.natCast_nonneg _) U.1 t :
                (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U.1)))) :
    Function.Surjective ψ := by
  intro s
  obtain ⟨-, ua, hua⟩ := exists_unit_ofRF_eq_sectionEquiv A a ha
  have hηL := genericPoint_mem_generatingLocus A a ha
  by_cases hs : s = 0
  · exact ⟨0, by rw [hs, map_zero]⟩
  obtain ⟨us, hus⟩ := exists_unit_ofRF_eq_app hηL s hs
  obtain ⟨m, hm⟩ := exists_neg_le_ord us
  have hσ := ofRF_mul_pow_mem_divisorialSubmodule A a ua hua us m hm
    (ord_nonneg_of_ofRF_eq_app s us hus)
  refine ⟨HomogeneousLocalization.Away.mk (A.situation.sectionRingGrading U.1) ⟨a, rfl⟩ m
    (DirectSum.of (A.situation.sectionPieces U.1) (m • n)
      ((A.sectionEquiv ((m • n : ℕ) : ℤ) (Int.natCast_nonneg _) U.1).symm ⟨_, hσ⟩))
    ⟨_, rfl⟩, ?_⟩
  have h := heq m ((A.sectionEquiv ((m • n : ℕ) : ℤ) (Int.natCast_nonneg _) U.1).symm ⟨_, hσ⟩)
  rw [AddEquiv.apply_symm_apply, ← hua] at h
  exact eq_of_app_mul_pow_eq (A.generatingLocus_le _ a) hηL _ s ua us m hus h

omit [IsLocallyNoetherian M] [IsNormal M] in
private theorem rationalFunctions_map_injective {U V : M.Opens} (h : V ≤ U)
    (hV : genericPoint M ∈ V) :
    Function.Injective ((rationalFunctionsPresheaf M).map (homOfLE h).op) := by
  intro s s' hss
  funext Y
  exact congrFun hss ⟨Y.1, componentGenericPoint_mem hV Y.1⟩

private theorem injective_of_factors [CompactSpace M] (U : Z.affineOpens) (n : ℕ)
    (a : (A.algebra.piece (n : ℤ)).val.obj (op U.1)) (ha : a ≠ 0)
    (ψ : HomogeneousLocalization.Away (A.situation.sectionRingGrading U.1)
        (DirectSum.of (A.situation.sectionPieces U.1) n a) →+*
        Γ(M, A.generatingLocus (Int.natCast_nonneg n) a))
    (heq : ∀ (m : ℕ) (t : (A.algebra.piece ((m • n : ℕ) : ℤ)).val.obj (op U.1)),
          (toRationalFunctionsPresheaf M).app (op (A.generatingLocus (Int.natCast_nonneg n) a))
              (ψ (HomogeneousLocalization.Away.mk (A.situation.sectionRingGrading U.1) ⟨a, rfl⟩ m
                (DirectSum.of (A.situation.sectionPieces U.1) (m • n) t) ⟨t, rfl⟩)) *
              (rationalFunctionsPresheaf M).map
                (homOfLE (A.generatingLocus_le _ a)).op
                (A.sectionEquiv n (Int.natCast_nonneg n) U.1 a :
                  (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U.1))) ^ m =
            (rationalFunctionsPresheaf M).map (homOfLE (A.generatingLocus_le _ a)).op
              (A.sectionEquiv _ (Int.natCast_nonneg _) U.1 t :
                (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U.1)))) :
    Function.Injective ψ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (A.situation.sectionRingGrading U.1)
    (show DirectSum.of (A.situation.sectionPieces U.1) n a ∈ A.situation.sectionRingGrading U.1 n
      from ⟨a, rfl⟩) x
  obtain ⟨t, rfl⟩ := hy
  have h := heq m t
  rw [hx, map_zero, zero_mul] at h
  have h0 := rationalFunctions_map_injective (A.generatingLocus_le _ a)
    (genericPoint_mem_generatingLocus A a ha) (h.symm.trans (map_zero _).symm)
  obtain rfl : t = 0 := by
    simpa using (Subtype.ext h0 : A.sectionEquiv _ (Int.natCast_nonneg _) U.1 t = 0)
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk, Localization.mk_zero]

private theorem mem_range_awayι {σ R : Type*} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : R} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m)
    {y : AlgebraicGeometry.Proj 𝒜} (hy : y ∈ Proj.basicOpen 𝒜 f) :
    y ∈ Set.range (Proj.awayι 𝒜 f hf hm) := by
  rwa [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]

/-- A ring isomorphic to an integrally closed domain is an integrally closed domain. -/
private theorem normal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    [IsDomain S] [IsIntegrallyClosed S] : ∃ _ : IsDomain R, IsIntegrallyClosed R :=
  ⟨e.injective.isDomain e.toRingHom, IsIntegrallyClosed.of_equiv e.symm⟩

/-- A point of `Proj 𝒜(W)` lies in a basic open `D₊(a)` of a nonzero homogeneous element `a` of
positive degree. -/
private theorem exists_mem_basicOpen {W : Z.Opens}
    (y : AlgebraicGeometry.Proj (A.situation.sectionRingGrading W)) :
    ∃ (i : ℕ) (hi0 : 0 < i) (a : A.situation.sectionPieces W i), a ≠ 0 ∧
      y ∈ Proj.basicOpen _ (DirectSum.of (A.situation.sectionPieces W) i a) := by
  classical
  obtain ⟨r, hr, hry⟩ := SetLike.not_le_iff_exists.mp y.not_irrelevant_le
  obtain ⟨i, hi⟩ : ∃ i, ((DirectSum.decompose (A.situation.sectionRingGrading W) r i :
      A.situation.sectionRing W)) ∉ y.asHomogeneousIdeal := by
    by_contra! H
    apply hry
    rw [← DirectSum.sum_support_decompose (A.situation.sectionRingGrading W) r]
    exact Ideal.sum_mem _ fun j _ => H j
  have hi0 : 0 < i := by
    refine Nat.pos_of_ne_zero fun h0 => hi ?_
    subst h0
    rw [show (DirectSum.decompose (A.situation.sectionRingGrading W) r 0 :
      A.situation.sectionRing W) = 0 from hr]
    exact zero_mem _
  obtain ⟨a, ha⟩ := (DirectSum.decompose (A.situation.sectionRingGrading W) r i).2
  have hya : y ∈ Proj.basicOpen _ (DirectSum.of (A.situation.sectionPieces W) i a) := by
    rwa [Proj.mem_basicOpen, ha]
  refine ⟨i, hi0, a, ?_, hya⟩
  rintro rfl
  rw [Proj.mem_basicOpen, map_zero] at hya
  exact hya (zero_mem _)

/-- **The relative `Proj` of the section algebra of a divisor on a normal integral scheme is
normal**, once it receives the induced morphism: on the chart `D₊(a)` its ring is
`𝒜(U)_(a) ≅ 𝒪_M(M_a)`, integrally closed since `M_a` is a normal integral scheme. -/
private theorem isNormal_model [CompactSpace M] {q : M ⟶ A.model} (hq : A.IsInducedMorphism q) :
    IsNormal A.model := by
  classical
  rw [isNormal_iff_stalk_normal]
  intro x
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
    (show A.toBase x ∈ (⊤ : Z.Opens) from trivial)
  let U : Z.affineOpens := ⟨W, hW⟩
  obtain ⟨y, rfl⟩ :=
    (Stacks.RelativeProj.Situation.mem_opensRange_relativeProjChart A.situation U x).mpr hxW
  obtain ⟨i, hi0, a, ha0, hya⟩ := exists_mem_basicOpen A y
  obtain ⟨z, rfl⟩ : y ∈ Set.range (Proj.awayι (A.situation.sectionRingGrading U.1)
      (DirectSum.of (A.situation.sectionPieces U.1) i a) ⟨a, rfl⟩ hi0) :=
    mem_range_awayι _ _ hi0 hya
  obtain ⟨ψ, -, heq⟩ := hq.factors U i hi0 a
  have hinj := injective_of_factors A U i a ha0 ψ heq
  have hsurj := surjective_of_factors A U i a ha0 ψ heq
  let L := A.generatingLocus (Int.natCast_nonneg i) a
  have : Nonempty L := ⟨⟨_, genericPoint_mem_generatingLocus A a ha0⟩⟩
  have : IsIntegrallyClosed Γ(L.toScheme, ⊤) := normal_globalSections L.toScheme
  let eL : Γ(L.toScheme, ⊤) ≃+* Γ(M, L) := L.topIso.commRingCatIsoToRingEquiv
  have : IsDomain Γ(M, L) := eL.symm.injective.isDomain eL.symm.toRingHom
  have : IsIntegrallyClosed Γ(M, L) := IsIntegrallyClosed.of_equiv eL
  let e := RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have : IsDomain (HomogeneousLocalization.Away (A.situation.sectionRingGrading U.1)
      (DirectSum.of (A.situation.sectionPieces U.1) i a)) := hinj.isDomain ψ
  have : IsIntegrallyClosed (HomogeneousLocalization.Away (A.situation.sectionRingGrading U.1)
      (DirectSum.of (A.situation.sectionPieces U.1) i a)) := IsIntegrallyClosed.of_equiv e.symm
  have hN := isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed
    (HomogeneousLocalization.Away (A.situation.sectionRingGrading U.1)
      (DirectSum.of (A.situation.sectionPieces U.1) i a)))
  let c := Proj.awayι (A.situation.sectionRingGrading U.1)
      (DirectSum.of (A.situation.sectionPieces U.1) i a) ⟨a, rfl⟩ hi0 ≫
    A.situation.relativeProjChart U
  have : IsOpenImmersion (A.situation.relativeProjChart U) :=
    Stacks.RelativeProj.Situation.isOpenImmersion_relativeProjChart _ _
  have : IsOpenImmersion (Proj.awayι (A.situation.sectionRingGrading U.1)
      (DirectSum.of (A.situation.sectionPieces U.1) i a) ⟨a, rfl⟩ hi0) :=
    Proj.instIsOpenImmersionAwayι _ _ _ _
  have : IsOpenImmersion c := IsOpenImmersion.comp _ _
  have : IsIso (c.stalkMap z) := (IsOpenImmersion.iff_isIso_stalkMap.mp this).2 z
  have hz := hN.stalk_normal z
  exact normal_of_ringEquiv (asIso (c.stalkMap z)).commRingCatIsoToRingEquiv

end Normality

/-! ### Normalized graphs -/

private theorem isIso_morphismRestrict {U V Z : Scheme.{u}} [IsReduced V] (p : V ⟶ Z)
    [IsSeparated p] (u : U ⟶ V) [IsOpenImmersion (u ≫ p)] [IsDominant u] :
    IsIso (p ∣_ (u ≫ p).opensRange) := by
  set O := (u ≫ p).opensRange
  let σ := (u ≫ p).isoOpensRange
  have hu : Set.range u ⊆ Set.range (p ⁻¹ᵁ O).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩
  let u' : U ⟶ p ⁻¹ᵁ O := IsOpenImmersion.lift (p ⁻¹ᵁ O).ι u hu
  have hu' : u' ≫ (p ⁻¹ᵁ O).ι = u := IsOpenImmersion.lift_fac _ _ _
  have h1 : u' ≫ p ∣_ O = σ.hom := by
    rw [← cancel_mono O.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hu']
    exact (Scheme.Hom.isoOpensRange_hom_ι _).symm
  have : IsDominant u' := by
    have : IsDominant (u' ≫ (p ⁻¹ᵁ O).ι) := by rw [hu']; infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion u' (p ⁻¹ᵁ O).ι
  let s' := σ.inv ≫ u'
  have h2 : s' ≫ p ∣_ O = 𝟙 _ := by simp [s', h1]
  refine ⟨s', ?_, h2⟩
  refine ext_of_isDominant_of_isSeparated (p ∣_ O)
    (by rw [Category.assoc, h2, Category.comp_id, Category.id_comp]) u' ?_
  simp [s', reassoc_of% h1]

private theorem exists_isBiregular {V Z : Scheme.{u}} [IsReduced V] [IrreducibleSpace V] {p : V ⟶ Z}
    [IsSeparated p] (hp : IsBirationalMorphism p) :
    ∃ O : Z.Opens, (O : Set Z).Nonempty ∧ IsBiregular p O := by
  have : Nonempty V := IrreducibleSpace.toNonempty
  obtain ⟨W, hW, hWp⟩ := hp.exists_isOpenImmersion
  have : IsDominant W.ι := Opens.isDominant_ι (W.isOpen.dense hW)
  refine ⟨(W.ι ≫ p).opensRange, ?_, isIso_morphismRestrict p W.ι⟩
  obtain ⟨x, hx⟩ := hW
  exact ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩

/-- Two separated birational morphisms to an irreducible scheme are both isomorphisms over a
common nonempty open. -/
private theorem exists_isIso_morphismRestrict {X V Z : Scheme.{u}} [IsReduced X]
    [IrreducibleSpace X] [IsReduced V] [IrreducibleSpace V] [IrreducibleSpace Z] {f : X ⟶ Z}
    {p : V ⟶ Z} [IsSeparated f] [IsSeparated p] (hf : IsBirationalMorphism f)
    (hp : IsBirationalMorphism p) :
    ∃ O : Z.Opens, (O : Set Z).Nonempty ∧ IsIso (f ∣_ O) ∧ IsIso (p ∣_ O) := by
  obtain ⟨Of, hOf, hf'⟩ := exists_isBiregular hf
  obtain ⟨Op, hOp, hp'⟩ := exists_isBiregular hp
  obtain ⟨z, hz1, hz2⟩ := (Of.isOpen.dense hOf).inter_open_nonempty _ Op.isOpen hOp
  exact ⟨Of ⊓ Op, ⟨z, hz2, hz1⟩,
    isBiregular_iff_le_biregularLocus.mpr
      (inf_le_left.trans (isBiregular_iff_le_biregularLocus.mp hf')),
    isBiregular_iff_le_biregularLocus.mpr
      (inf_le_right.trans (isBiregular_iff_le_biregularLocus.mp hp'))⟩

/-- The generic point of an irreducible reduced scheme lies over the biregular locus of a
separated birational morphism. -/
private theorem map_genericPoint_mem_biregularLocus {V Z : Scheme.{u}} [IsReduced V]
    [IrreducibleSpace V] [IrreducibleSpace Z] {p : V ⟶ Z} [IsSeparated p]
    (hp : IsBirationalMorphism p) : p (genericPoint V) ∈ biregularLocus p := by
  obtain ⟨O, hO, hOp⟩ := exists_isBiregular hp
  have : IsDominant p := hp.isDominant
  rw [MMP.Positivity.map_genericPoint_eq_of_isDominant]
  exact isBiregular_iff_le_biregularLocus.mp hOp
    (((genericPoint_spec Z).mem_open_set_iff O.isOpen).mpr (by simpa using hO))

/-- A point of coheight less than two outside the biregular locus of a separated birational
morphism has coheight one. -/
private theorem coheight_eq_one_of_map_notMem_biregularLocus {V Z : Scheme.{u}} [IsReduced V]
    [IrreducibleSpace V] [IrreducibleSpace Z] {p : V ⟶ Z} [IsSeparated p]
    (hp : IsBirationalMorphism p) {y : V} (hy : p y ∉ biregularLocus p)
    (hlt : Order.coheight y < 2) : Order.coheight y = 1 := by
  obtain h0 | h1 :=
    lt_or_eq_of_le (Order.le_of_lt_succ (show Order.coheight y < Order.succ 1 from hlt))
  · have hmax : IsMax y := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0)
    have hgy : y = genericPoint V :=
      (Specializes.antisymm (hmax (genericPoint_specializes y)) (genericPoint_specializes y)).eq
    exact (hy (hgy ▸ map_genericPoint_mem_biregularLocus hp)).elim
  · exact h1

private theorem isBirationalMorphism_of_isOpenImmersion {V Z : Scheme.{u}} (p : V ⟶ Z)
    (W : V.Opens) (hW : Dense (W : Set V)) [IsOpenImmersion (W.ι ≫ p)]
    (hW' : Dense (Set.range (W.ι ≫ p))) : IsBirationalMorphism p := by
  refine ⟨⟨W, hW, (W.ι ≫ p).opensRange,
    by rwa [Scheme.Hom.coe_opensRange], (W.ι ≫ p).isoOpensRange⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨W, hW, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, Scheme.Hom.isoOpensRange_hom_ι]
  rw [Scheme.topIso_hom]
  change V.homOfLE (le_refl W) ≫ W.ι ≫ p = V.homOfLE (le_top : W ≤ ⊤) ≫ (⊤ : V.Opens).ι ≫ p
  rw [Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]

private theorem isBirationalMorphism_of_isOpenImmersion_comp {U V Z : Scheme.{u}} [Nonempty U]
    [IsReduced V] [IrreducibleSpace Z] (p : V ⟶ Z) [IsSeparated p] (u : U ⟶ V)
    [IsOpenImmersion (u ≫ p)] [IsDominant u] : IsBirationalMorphism p := by
  have := isIso_morphismRestrict p u
  have hsub : Set.range u ⊆ (p ⁻¹ᵁ (u ≫ p).opensRange : Set V) := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  have : IsOpenImmersion ((p ⁻¹ᵁ (u ≫ p).opensRange).ι ≫ p) := by
    rw [← morphismRestrict_ι]; infer_instance
  refine isBirationalMorphism_of_isOpenImmersion p _ (u.denseRange.mono hsub) ?_
  obtain ⟨t⟩ := ‹Nonempty U›
  refine ((u ≫ p).isOpenEmbedding.isOpenMap.isOpen_range.dense ⟨_, t, rfl⟩).mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨⟨u t, hsub ⟨t, rfl⟩⟩, rfl⟩

private theorem exists_isNormalizedGraph {k : Type u} [Field k] {X V Z : Scheme.{u}}
    [IsIntegral X] [IsNormal X] [IsIntegral V] [IrreducibleSpace Z]
    [CompactSpace X] [CompactSpace V]
    {sZ : Z ⟶ Spec (.of k)} [LocallyOfFiniteType sZ]
    {f : X ⟶ Z} {p : V ⟶ Z} [LocallyOfFiniteType f] [LocallyOfFiniteType p] [IsSeparated f]
    [IsSeparated p] [QuasiCompact p]
    (hf : IsBirationalMorphism f) (hp : IsBirationalMorphism p) :
    ∃ (G : Scheme.{u}) (u : G ⟶ X) (v : G ⟶ V), IsNormalizedGraph f p u v ∧ CompactSpace G ∧
      IsLocallyNoetherian G := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sZ)
  have : IsNoetherian X := {}
  obtain ⟨O, hOne, hfO, hpO⟩ := exists_isIso_morphismRestrict hf hp
  set T := f ⁻¹ᵁ O
  have : Nonempty T := by
    obtain ⟨z, hz⟩ := hOne
    exact ⟨(inv (f ∣_ O)) ⟨z, hz⟩⟩
  let g : T.toScheme ⟶ V := (f ∣_ O) ≫ inv (p ∣_ O) ≫ (p ⁻¹ᵁ O).ι
  have hg : T.ι ≫ f = g ≫ p := by
    simp only [g, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    exact (morphismRestrict_ι f O).symm
  let j : T.toScheme ⟶ pullback f p := pullback.lift T.ι g hg
  have : TopologicalSpace.NoetherianSpace T := TopologicalSpace.NoetherianSpace.set _
  have : QuasiCompact j := quasiCompact_of_noetherianSpace_source j
  have : QuasiSeparated j := by
    have : QuasiSeparated (j ≫ pullback.fst f p) := by
      simp only [j, pullback.lift_fst]; infer_instance
    exact QuasiSeparated.of_comp j (pullback.fst f p)
  let G := j.normalization
  let ν : G ⟶ pullback f p := j.fromNormalization
  have tν : j.toNormalization ≫ ν = j := j.toNormalization_fromNormalization
  have : LocallyOfFiniteType (j ≫ pullback.fst f p ≫ f ≫ sZ) := by
    rw [pullback.lift_fst_assoc]; infer_instance
  have hfin : IsFinite ν := isFinite_fromNormalization_of_locallyOfFiniteType_over_field k
    (pullback.fst f p ≫ f ≫ sZ) _ j rfl
  refine ⟨G, ν ≫ pullback.fst f p, ν ≫ pullback.snd f p, ?_, ?_, ?_⟩
  · have hT : ∀ W : T.toScheme.Opens, IsCompact (W : Set T) → (irreducibleComponents W).Finite :=
      fun W _ => by
        have : TopologicalSpace.NoetherianSpace W := TopologicalSpace.NoetherianSpace.set _
        exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    have hGn : IsNormal G := isNormal_normalization j hT
    have hcomp : (ν ≫ pullback.fst f p) ≫ f = (ν ≫ pullback.snd f p) ≫ p := by
      simp [pullback.condition]
    have hlift : pullback.lift _ _ hcomp = ν :=
      pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    refine ⟨inferInstance, hGn, hcomp, by rwa [hlift], ?_, ?_⟩
    · have : IsOpenImmersion (j.toNormalization ≫ ν ≫ pullback.fst f p) := by
        rw [reassoc_of% tν]; simp only [j, pullback.lift_fst]; infer_instance
      exact isBirationalMorphism_of_isOpenImmersion_comp _ j.toNormalization
    · have : IsOpenImmersion (j.toNormalization ≫ ν ≫ pullback.snd f p) := by
        rw [reassoc_of% tν]; simp only [j, pullback.lift_snd, g]; infer_instance
      exact isBirationalMorphism_of_isOpenImmersion_comp _ j.toNormalization
  · exact QuasiCompact.compactSpace_of_compactSpace (ν ≫ pullback.fst f p)
  · exact LocallyOfFiniteType.isLocallyNoetherian (ν ≫ pullback.fst f p ≫ f ≫ sZ)

/-! ### Canonical divisors of normal varieties -/

section CanonicalDivisorExistence

open Opposite TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes_component {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem component_specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_stalkSpecializes_apply {Y : Scheme.{u}} {x y z : Y}
    (h : x ⤳ y) (h' : y ⤳ z) (h'' : x ⤳ z) (s : Y.presheaf.stalk z) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) =
      (Y.presheaf.stalkSpecializes h'').hom s :=
  TopCat.Presheaf.stalkSpecializes_comp_apply _ h h' s

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes_component Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' :=
  congrArg (evFF φ) (index_eq Z Z')

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective
      (Y.presheaf.stalkSpecializes (genericPoint_specializes_component Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (component_specializes_genericPoint Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation ((Y.presheaf.stalkSpecializes
      (genericPoint_specializes_component E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes_component E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes
            (genericPoint_specializes_component E.component)).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, -⟩ := h
  exact ((genericPoint_spec U.toScheme).specializes trivial).mem_open V.isOpen hx

/-- The unique irreducible component `Set.univ` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rwa [componentGenericPoint_eq_genericPoint]⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (component_specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (component_specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (component_specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes_component _)).hom
      ((X.presheaf.stalkSpecializes (component_specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (component_specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
    rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  refine ⟨fun h P hP => ?_, fun h E' hE' =>
    (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))⟩
  have hPU : P.genericPoint ∈ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
    rw [← hx]
    exact x.2
  obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
  exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · have h' : restrictRF U V ψ₁.1 = restrictRF U V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective U V h')
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  have : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  have : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  have : IsDominant T.ι := Opens.isDominant_ι (T.isOpen.dense ⟨_, (Classical.arbitrary T).2⟩)
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  have : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  have : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  let e₀ := (@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom T KS)).symm
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

end CanonicalDivisorExistence

/-! ### Rational top forms -/

section FormsAux

open MMP.Flips

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

open MMP.Positivity in
/-- For a proper birational morphism `f : Y → X` of normal varieties of dimension `n` and a
canonical divisor `K_Y` of `Y`, there is a nonzero rational top form `ω` on `X` with
`div_Y(f^*ω) = K_Y` and `div_X(ω) = f_* K_Y`. -/
private theorem exists_divisorOfForm_eq_transformDivisor (hX : IsNormalVariety k sX) {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX)) [IsProper f]
    (hf : IsBirationalMorphism f) [IsDominant f] {n : ℕ} (hn : topologicalKrullDim X = n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧
      divisorOfForm ω = RationalMap.transformDivisor (X := Y) f.toRationalMap KY ∧
      divisorOfForm (pullbackRationalPluriForms sX f ω) = KY := by
  have hbij := hf.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨ω₁, hω₁0, hω₁⟩ := IsCanonicalDivisor.exists_ordForm_eq hY hKY
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω₁ ())
  let τ : RationalPluriForms sX n 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sX f τ = ω₁ := by
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 τ = ω₁
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp only [τ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap f g • _ = ω₁
    rw [hg]
    exact basis_unit_repr_smul _ ω₁
  refine ⟨τ, fun h0 => hω₁0 ?_, Finsupp.ext fun P => ?_, Finsupp.ext fun Γ => ?_⟩
  · rw [← hpull, h0]
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 0 = 0
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp
  · obtain ⟨E, heq, hiso, htr⟩ := exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hf P
    rw [htr]
    change P.ordForm τ = KY.coeff E
    rw [← ordForm_pullbackRationalPluriForms_of_isIso f hbij hd E P heq τ, hpull, hω₁]
  · change Γ.ordForm _ = KY.coeff Γ
    rw [hpull, hω₁]

end FormsAux

/-! ### Dimension and top forms along birational morphisms -/

section BirationalForms

open MMP.Positivity

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [LocallyOfFiniteType sX] [IsIntegral Y]

omit [PerfectField k] in
/-- A birational morphism of varieties preserves dimension: both are the transcendence degree of
the common function field. -/
private theorem topologicalKrullDim_eq_of_isBirationalMorphism {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] [IsDominant f] (hf : IsBirationalMorphism f) :
    topologicalKrullDim Y = topologicalKrullDim X := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  rw [← toENat_trdeg_functionField (sX := f ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX f hf.functionFieldMap_bijective,
    toENat_trdeg_functionField (sX := sX)]

/-- The pull-back along a pull-back generator of a nonzero pluri-form is nonzero. -/
private theorem pullbackForms_ne_zero {k : Type*} [CommRing k] {K K' : Type*} [Field K]
    [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) {m : ℤ} {τ : PluriForms k K d m}
    (hτ : τ ≠ 0) : pullbackForms (K' := K') m τ ≠ 0 := by
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  exact smul_ne_zero ((map_ne_zero _).mpr (repr_ne_zero_of_ne_zero _ hτ))
    ((ZTensorPower.basis _ m).ne_zero ())

/-- The pull-back of a nonzero rational pluri-form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {f : Y ⟶ X} [LocallyOfFiniteType (f ≫ sX)]
    [IsDominant f] (hf : IsBirationalMorphism f) {d : ℕ} (hd : topologicalKrullDim X = d)
    {m : ℤ} {σ : RationalPluriForms sX d m} (hσ : σ ≠ 0) :
    pullbackRationalPluriForms sX f σ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd)
  exact pullbackForms_ne_zero hω hσ

end BirationalForms

/-! ### Prime divisors over the biregular locus -/

section Helpers

variable {X Y : Scheme.{u}}

/-- A morphism is injective on the points mapping into its biregular locus. -/
private theorem eq_of_map_eq_of_mem_biregularLocus (f : X ⟶ Y) {x y : X} (hxy : f x = f y)
    (hx : f x ∈ biregularLocus f) : x = y := by
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  let a : (f ⁻¹ᵁ biregularLocus f).toScheme := ⟨x, hx⟩
  let b : (f ⁻¹ᵁ biregularLocus f).toScheme := ⟨y, show f y ∈ _ from hxy ▸ hx⟩
  have := (f ∣_ biregularLocus f).isOpenEmbedding.injective (a₁ := a) (a₂ := b)
    (Subtype.ext ((morphismRestrict_base_coe f _ a).trans
      (hxy.trans (morphismRestrict_base_coe f _ b).symm)))
  exact congrArg Subtype.val this

/-- Two prime divisors whose generic points have the same image in the biregular locus are
equal. -/
private theorem primeDivisor_eq_of_map_genericPoint_eq (f : X ⟶ Y)
    {D D' : MMP.Mori.PrimeDivisor X} (h : f D'.genericPoint = f D.genericPoint)
    (hD : f D.genericPoint ∈ biregularLocus f) : D' = D :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_map_eq_of_mem_biregularLocus f h (h ▸ hD))

/-- A point mapping onto the generic point of a prime divisor inside the biregular locus is the
generic point of a prime divisor. -/
private theorem exists_primeDivisor_of_map_eq (f : X ⟶ Y) {x : X} {G : MMP.Mori.PrimeDivisor Y}
    (hx : f x = G.genericPoint) (hG : G.genericPoint ∈ biregularLocus f) :
    ∃ D : MMP.Mori.PrimeDivisor X, D.genericPoint = x := by
  have hc : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f (hx ▸ hG), hx,
      G.coheight_genericPoint]
  exact ⟨.ofCoheightOne _ hc, AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc⟩

/-- A prime divisor of the target whose generic point lies in the biregular locus is the image
of a prime divisor of the source. -/
private theorem exists_map_genericPoint_eq (f : X ⟶ Y) {G : MMP.Mori.PrimeDivisor Y}
    (hG : G.genericPoint ∈ biregularLocus f) :
    ∃ D : MMP.Mori.PrimeDivisor X, f D.genericPoint = G.genericPoint := by
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  obtain ⟨x, hx⟩ := (f ∣_ biregularLocus f).surjective ⟨_, hG⟩
  have hx : f x.1 = G.genericPoint :=
    (morphismRestrict_base_coe f _ x).symm.trans (congrArg Subtype.val hx)
  obtain ⟨D, hD⟩ := exists_primeDivisor_of_map_eq f hx hG
  exact ⟨D, hD ▸ hx⟩

/-- The image of the generic point of a prime divisor, if it lies in the biregular locus, is the
generic point of a prime divisor. -/
private theorem exists_genericPoint_eq_map (f : X ⟶ Y) (P : MMP.Mori.PrimeDivisor X)
    (hP : f P.genericPoint ∈ biregularLocus f) :
    ∃ G : MMP.Mori.PrimeDivisor Y, G.genericPoint = f P.genericPoint := by
  have hc : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hP, P.coheight_genericPoint]
  exact ⟨.ofCoheightOne _ hc, AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc⟩

/-- A proper birational morphism onto a normal variety is an isomorphism near the generic point of
every prime divisor of the target. -/
private theorem genericPoint_mem_biregularLocus {k : Type u} [Field k] {sY : Y ⟶ Spec (.of k)}
    (hY : IsNormalVariety k sY) (f : X ⟶ Y) (hX : AlgebraicGeometry.IsVariety k (f ≫ sY))
    [IsProper f] (hf : IsBirationalMorphism f) (G : MMP.Mori.PrimeDivisor Y) :
    G.genericPoint ∈ biregularLocus f := by
  have := hY.1.toIsIntegral
  have := hY.1.toLocallyOfFiniteType
  have := LocallyOfFiniteType.isLocallyNoetherian sY
  refine mem_biregularLocus_of_ringKrullDim_stalk_le_one hY f hX hf ?_
  rw [ringKrullDim_stalk_eq_coheight, G.coheight_genericPoint]
  rfl

/-- The coefficient of `P` in the push-forward along a morphism `g` is the coefficient of the
unique prime divisor whose generic point `g` sends to that of `P`. -/
private theorem transformDivisor_toRationalMap_apply [IsReduced X] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {R : Type*} [AddCommMonoid R] (g : X ⟶ Y) {E : MMP.Mori.PrimeDivisor X}
    {P : MMP.Mori.PrimeDivisor Y} (hE : g E.genericPoint = P.genericPoint)
    (h : ∀ E' : MMP.Mori.PrimeDivisor X, g E'.genericPoint = P.genericPoint → E' = E)
    (B : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (X := X) g.toRationalMap B P = B E :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff g E P).mpr hE)
    (fun E' hE' => h E' ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff g E' P).mp
      hE')) B

/-- A structure morphism to `Spec k` which is separated makes the scheme separated over the
terminal object. -/
private theorem isSeparated_terminal {k : Type u} [Field k] (s : X ⟶ Spec (.of k))
    (hs : IsSeparated s) : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- The birational transform of a prime divisor `P` under a rational map represented at its
generic point by `g'` is the closure of the image of the generic point. -/
private theorem coe_transform_eq_closure_singleton [IsReduced X] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {φ : X.RationalMap Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ,
    TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rwa [Scheme.Opens.ι_apply])
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- If `φ_* P = E` and `g'` represents `φ` at the generic point of `P`, then `g'` sends the
generic point of `P` to that of `E`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- Conversely, if `g'` represents `φ` at the generic point of `P` and sends it to the generic
point of `E`, then `φ_* P = E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    RationalMap.transformPrimeDivisor φ P = some E := by
  refine RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- **Prime divisors over a common biregular point correspond under a rational map over `Z`.** Let
`φ : X ⤏ M` be a rational map over `Z`, with `f : X ⟶ Z` and `π : M ⟶ Z`, and let `G` be a prime
divisor of `Z` at whose generic point both `f` and `π` are isomorphisms. Then the prime divisor
`D` of `X` over `G` is sent by `φ` to the prime divisor `F` of `M` over `G`, and `D` is the only
prime divisor `φ` sends to `F`. -/
private theorem exists_transformPrimeDivisor_eq_some {Z M : Scheme.{u}} [IsIntegral X]
    [IsReduced M] [IsSeparated (M ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)] {f : X ⟶ Z}
    {π : M ⟶ Z} {φ : X.RationalMap M} (hφ : MMP.Flips.RationalMap.IsOver f π φ)
    {G : MMP.Mori.PrimeDivisor Z} (hf : G.genericPoint ∈ biregularLocus f)
    (hπ : G.genericPoint ∈ biregularLocus π) {D : MMP.Mori.PrimeDivisor X}
    (hD : f D.genericPoint = G.genericPoint) :
    ∃ F : MMP.Mori.PrimeDivisor M, π F.genericPoint = G.genericPoint ∧
      RationalMap.transformPrimeDivisor φ D = some F ∧
      ∀ D' : MMP.Mori.PrimeDivisor X, RationalMap.transformPrimeDivisor φ D' = some F → D' = D := by
  have : IsIso (π ∣_ biregularLocus π) := isBiregular_biregularLocus π
  have hDW : D.genericPoint ∈ f ⁻¹ᵁ biregularLocus π := show f _ ∈ _ from hD ▸ hπ
  have hd : Dense ((f ⁻¹ᵁ biregularLocus π : X.Opens) : Set X) := (f ⁻¹ᵁ _).isOpen.dense ⟨_, hDW⟩
  let g : X.PartialMap M := .mk _ hd
    ((f ∣_ biregularLocus π ≫ inv (π ∣_ biregularLocus π)) ≫ (π ⁻¹ᵁ biregularLocus π).ι)
  have hg : g.toRationalMap = φ :=
    MMP.Flips.toRationalMap_eq_of_comp_morphismRestrict_eq hd (by simp) hφ
  have hm : π (g.hom ⟨D.genericPoint, hDW⟩) = G.genericPoint := by
    have key : g.hom ≫ π = (f ⁻¹ᵁ biregularLocus π).ι ≫ f := by
      simp only [g, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    have := congrArg (fun k : (f ⁻¹ᵁ biregularLocus π).toScheme ⟶ Z => k ⟨D.genericPoint, hDW⟩) key
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at this
    exact this.trans hD
  obtain ⟨F, hF⟩ := exists_primeDivisor_of_map_eq π hm hπ
  have hFG : π F.genericPoint = G.genericPoint := hF ▸ hm
  refine ⟨F, hFG, transformPrimeDivisor_eq_some_of_genericPoint_eq g hg hDW hF,
    fun D' hD' => ?_⟩
  obtain ⟨g', hD'g, hg'⟩ :=
    RationalMap.definedAt_iff.mp (RationalMap.transformPrimeDivisor_eq_some_iff.mp hD').1
  have h1 := genericPoint_eq_of_transformPrimeDivisor_eq_some hD' g' hg' hD'g
  have h2 : π (g'.hom ⟨_, hD'g⟩) = f D'.genericPoint :=
    MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq (g := g'.compHom π)
      (g' := f.toPartialMap) (by rw [Scheme.RationalMap.compHom_toRationalMap, hg', hφ])
      hD'g trivial
  exact primeDivisor_eq_of_map_genericPoint_eq f (by rw [← h2, ← h1, hFG, hD]) (hD ▸ hf)

/-- If the exceptional set of `f` has codimension at least two, then the generic point of every
prime divisor lies over the biregular locus of `f`. -/
private theorem map_genericPoint_mem_biregularLocus_of_two_le (f : X ⟶ Y)
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f := by
  by_contra hne
  have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 (mem_exceptionalSet.mpr hne)
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- At a prime divisor `P` of `V` over the generic point of a prime divisor `G` of `Y`, around
which `p` and `f` are isomorphisms, `p⁻¹_* f_* B` has the coefficient of `B` at the prime divisor
`D` of `X` over `G`. -/
private theorem flipTransform_apply_eq {V : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {R : Type*} [AddCommMonoid R] (f : X ⟶ Y) (p : V ⟶ Y)
    {P : MMP.Mori.PrimeDivisor V} {G : MMP.Mori.PrimeDivisor Y} {D : MMP.Mori.PrimeDivisor X}
    (hG : G.genericPoint = p P.genericPoint) (hP : p P.genericPoint ∈ biregularLocus p)
    (hD : f D.genericPoint = G.genericPoint) (hGf : G.genericPoint ∈ biregularLocus f)
    (B : DivisorWithCoeffs R X) : flipTransform f p B P = B D := by
  change DivisorWithCoeffs.mapPrimeDivisors (inverseTransformPrimeDivisor p)
    (RationalMap.transformDivisor (X := X) f.toRationalMap B) P = _
  rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      hG.symm (hG ▸ hP)) fun G' hG' =>
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
          hG').1.symm.trans hG.symm)]
  exact transformDivisor_toRationalMap_apply f hD (fun D' hD' =>
    primeDivisor_eq_of_map_genericPoint_eq f (hD'.trans hD.symm) (hD ▸ hGf)) B

end Helpers

section AmpleModel

variable {X Z M V : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]

/-! ### A compatible canonical divisor on the ample model -/

/-- The ample model carries a canonical divisor `K_V` with `p_* K_V = f_* K_X`. -/
private theorem exists_isCanonicalDivisor_transformDivisor_eq [IsNormal V] [CompactSpace V]
    [IsLocallyNoetherian V]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV) :
    ∃ (KV : Divisor V) (n : ℕ), KV.IsCanonicalDivisor (p ≫ sZ) n ∧
      RationalMap.transformDivisor (X := V) p.toRationalMap KV =
        RationalMap.transformDivisor (X := X) f.toRationalMap K := by
  have hX := h.isContraction.isNormalVariety_source
  have hZ := h.isContraction.isNormalVariety_target
  have hcomp : f ≫ sZ = sX := h.isContraction.comp_eq
  obtain ⟨n, hK⟩ := h.isCanonicalDivisor
  obtain ⟨hproj, hbir⟩ := h.isProjectiveMorphism_and_isBirationalMorphism
  obtain ⟨-, hVi, hV, -, -, -⟩ := h.isProper_and_isBirationalMorphism
  have : IsIntegral V := hVi
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : QuasiCompact sZ := hZ.1.toQuasiCompact
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsProper p := isProper_of_isProjectiveMorphism p hproj
  have : IsProper f := isProper_of_isProjectiveMorphism f h.isContraction.isProjectiveMorphism
  have : IsDominant f := h.isBirationalMorphism.isDominant
  have : IsDominant p := hbir.isDominant
  subst hcomp
  have : LocallyOfFiniteType (f ≫ sZ) := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (p ≫ sZ) := hV.1.toLocallyOfFiniteType
  have hnZ : topologicalKrullDim Z = n :=
    (topologicalKrullDim_eq_of_isBirationalMorphism (sX := sZ) h.isBirationalMorphism).symm.trans
      hK.topologicalKrullDim_eq
  have hnV : topologicalKrullDim V = n :=
    (topologicalKrullDim_eq_of_isBirationalMorphism (sX := sZ) hbir).trans hnZ
  obtain ⟨ω, hω0, hωZ, -⟩ :=
    exists_divisorOfForm_eq_transformDivisor hZ hX h.isBirationalMorphism hnZ hK
  obtain ⟨KV0, hKV0⟩ := exists_isCanonicalDivisor (p ≫ sZ) hV hnV
  have hτ := pullbackRationalPluriForms_ne_zero hbir hnZ hω0
  refine ⟨divisorOfForm (pullbackRationalPluriForms sZ p ω), n,
    hKV0.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hV hKV0 hτ), ?_⟩
  rw [← hωZ]
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, heq, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hV hbir P
  rw [htr]
  change E.ordForm _ = P.ordForm ω
  exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p
    hbir.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ) E P heq ω

/-! ### The exceptional set of `p` -/

private theorem two_le_closedsCodimension_exceptionalSet [IsNormal V] [CompactSpace V]
    [IsLocallyNoetherian V]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV)
    {KV : Divisor V} {n : ℕ} (hKV : KV.IsCanonicalDivisor (p ≫ sZ) n)
    (hKVK : RationalMap.transformDivisor (X := V) p.toRationalMap KV =
      RationalMap.transformDivisor (X := X) f.toRationalMap K) :
    2 ≤ closedsCodimension (exceptionalSet p) := by
  obtain ⟨hproj, hbir⟩ := h.isProjectiveMorphism_and_isBirationalMorphism
  obtain ⟨-, hVi, hV, -, -, -⟩ := h.isProper_and_isBirationalMorphism
  have hZ := h.isContraction.isNormalVariety_target
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsProper p := isProper_of_isProjectiveMorphism p hproj
  have : IsProper f := isProper_of_isProjectiveMorphism f h.isContraction.isProjectiveMorphism
  obtain ⟨G, u, v, hG, hGc, hGn⟩ := exists_isNormalizedGraph (sZ := sZ) h.isBirationalMorphism hbir
  have : IsIntegral G := hG.isIntegral
  have : IsNormal G := hG.isNormal
  obtain ⟨hD, hDV, hu, hv, hpush⟩ :=
    h.transformDivisor_pullback_sub_pullback_eq_zero hKV hKVK hG
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro y hy
  have hyb : p y ∉ biregularLocus p := mem_exceptionalSet.mp hy
  by_contra hlt
  push Not at hlt
  have hco := coheight_eq_one_of_map_notMem_biregularLocus hbir hyb hlt
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hco
  have hPy : P.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have : IsProper v := by
    have := hG.isFinite
    rw [← pullback.lift_snd u v hG.comp_eq]
    infer_instance
  have hVv : IsNormalVariety ℂ (v ≫ p ≫ sZ) := by
    have := hV.1
    exact ⟨{}, inferInstance⟩
  obtain ⟨E, hEP, -, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
    hV hVv hG.isBirationalMorphism_plus P
  have h0 := htr ((Divisor.toQDivisor K + B).pullback hD hu -
    (Divisor.toQDivisor KV + BV).pullback hDV hv)
  rw [hpush, Finsupp.zero_apply] at h0
  obtain ⟨_, _, _, _, hsupp⟩ :=
    h.preimage_singleton_subset_supp_pullback_sub_pullback hKV hKVK hG (z := p y)
      (fun hz => hyb hz.2)
  have hmem : E.genericPoint ∈ (u ≫ f) ⁻¹' {p y} := by
    change (u ≫ f) E.genericPoint = p y
    rw [hG.comp_eq, Scheme.Hom.comp_apply, hEP]
    exact congrArg p hPy
  obtain ⟨E', hE', hηE⟩ := DivisorWithCoeffs.mem_supp_iff.mp (hsupp hmem)
  obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hηE
  exact hE' h0.symm

/-- The ample model of an ample-model datum is normal. -/
private theorem isNormal_ampleModel
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV) : IsNormal V := by
  obtain ⟨-, -, D, -, -, -, A, e, -, hind⟩ := h.isRelativeAmpleModel
  have hA := isNormal_model A hind
  rw [isNormal_iff_stalk_normal]
  intro x
  have := hA.stalk_normal (e.hom x)
  exact normal_of_ringEquiv (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv.symm

/-- For an ample-model datum `(M, B_M, q, V, B_V)` of a birational contraction `f : X ⟶ Z`, the
structure morphism `p : V ⟶ Z` is small. -/
@[mmp "lem_oai4_c3_ample_model_small"]
public theorem IsAmpleModelDatum.isSmallMorphism
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV) :
    IsSmallMorphism (p ≫ sZ) sZ p := by
  have : IsNormal V := isNormal_ampleModel h
  obtain ⟨hproj, hbir⟩ := h.isProjectiveMorphism_and_isBirationalMorphism
  obtain ⟨-, -, hV, -, -, -⟩ := h.isProper_and_isBirationalMorphism
  have : IsProper p := isProper_of_isProjectiveMorphism p hproj
  have : LocallyOfFiniteType (p ≫ sZ) := hV.1.toLocallyOfFiniteType
  have : QuasiCompact (p ≫ sZ) := hV.1.toQuasiCompact
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sZ)
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p ≫ sZ)
  obtain ⟨KV, n, hKV, hKVK⟩ := exists_isCanonicalDivisor_transformDivisor_eq h
  exact ⟨hV, h.isContraction.isNormalVariety_target, rfl, inferInstance, hbir,
    two_le_closedsCodimension_exceptionalSet h hKV hKVK⟩

/-- For an ample-model datum `(M, B_M, q, V, B_V)` of a birational contraction `f : X ⟶ Z`, with
structure morphism `p : V ⟶ Z`, the boundary `B_V` is the strict transform `p⁻¹_* f_* B` of
`f_* B` on `V`. -/
@[mmp "lem_oai4_c3_ample_model_boundary"]
public theorem IsAmpleModelDatum.boundary_eq_flipTransform
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV) :
    BV = flipTransform f p B := by
  classical
  have hsm := h.isSmallMorphism
  have : IsNormal V := hsm.isNormalVariety_source.2
  obtain ⟨hqp, _, hV, hMv, _, hqb⟩ := h.isProper_and_isBirationalMorphism
  have hlm := h.isGoodLogMinimalModel
  have hZ : IsNormalVariety ℂ sZ := h.isContraction.isNormalVariety_target
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := hV.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sZ)
  have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_terminal sZ hZ.1.toIsSeparated
  have : IsSeparated (V ↘ ⊤_ Scheme) := isSeparated_terminal (p ≫ sZ) hV.1.toIsSeparated
  have : IsSeparated (M ↘ ⊤_ Scheme) :=
    isSeparated_terminal (q ≫ p ≫ sZ) hMv.1.toIsSeparated
  have : IsProper f := isProper_of_isProjectiveMorphism f h.isContraction.isProjectiveMorphism
  have : IsProper p := hsm.isProper
  have : IsProper πM := isProper_of_isProjectiveMorphism πM hlm.isProjectiveMorphism_model
  have hπb : IsBirationalMorphism πM := hqp ▸ isBirationalMorphism_comp_of_isBirational p q
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hsm.isBirationalMorphism)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hqb)
  refine Finsupp.ext fun P => ?_
  rw [h.boundary_eq]
  have hP := map_genericPoint_mem_biregularLocus_of_two_le p hsm.two_le_codimension P
  obtain ⟨G, hG⟩ := exists_genericPoint_eq_map p P hP
  have hGf : G.genericPoint ∈ biregularLocus f := genericPoint_mem_biregularLocus hZ f
    (by rw [h.isContraction.comp_eq]; exact h.isContraction.isNormalVariety_source.1)
    h.isBirationalMorphism G
  have hGπ : G.genericPoint ∈ biregularLocus πM := genericPoint_mem_biregularLocus hZ πM
    (by rw [← hqp, Category.assoc]; exact hMv.1) hπb G
  obtain ⟨D, hD⟩ := exists_map_genericPoint_eq f hGf
  obtain ⟨F, hFG, hφDF, huφ⟩ := exists_transformPrimeDivisor_eq_some hlm.isOver hGf hGπ hD
  have hqF : q F.genericPoint = P.genericPoint := by
    have h1 : p (q F.genericPoint) = p P.genericPoint := by
      rw [← Scheme.Hom.comp_apply, hqp, hFG, hG]
    exact eq_of_map_eq_of_mem_biregularLocus p h1 (h1 ▸ hP)
  have hL : RationalMap.transformDivisor (X := M) q.toRationalMap BM P = BM F :=
    transformDivisor_toRationalMap_apply q hqF (fun F' hF' =>
      primeDivisor_eq_of_map_genericPoint_eq πM
        (by rw [← hqp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hF', hqF]) (hFG ▸ hGπ)) BM
  have hM : BM F = B D := by
    have hb := hlm.coeff_boundary F
    rw [if_neg fun hF' => hF' D hφDF, add_zero] at hb
    exact hb.trans (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hφDF huφ B)
  rw [flipTransform_apply_eq f p hG hP hD hGf B, hL, hM]

end AmpleModel

end MMP.Fourfold
