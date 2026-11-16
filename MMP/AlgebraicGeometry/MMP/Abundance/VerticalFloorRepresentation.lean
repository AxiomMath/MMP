module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.MMP.Fourfold.VerticalFloorPluriforms
import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
import MMP.AlgebraicGeometry.MMP.Abundance.SubkltSurfacePluriformFinite

/-!
# Finite crepant representations of semiample lc surfaces with vertical floor

Let `X` be a smooth projective complex surface and `B` an snc `ℚ`-divisor with all coefficients
at most one (negative coefficients allowed), with `D = K_X + B` semiample, and let `T = B^{=1}`
be the reduced coefficient-one part. Let `f : X ⟶ Y` be the semiample contraction of `D`, so
that `rD = f^*A` for some `r > 0` and some ample Cartier divisor `A` on `Y`. If every component
of `T` has image a proper subset of `Y` (the floor is vertical), then for every `d > 0` with `dD`
Cartier the crepant birational self-maps of `(X, B)` act on `H⁰(X, dD)` by pluriform pull-back,
and the image of this representation is finite.

The proof multiplies by an invariant section `t ∈ H⁰(X, kmD - kT)`, the product of the finite
orbit of a nonzero vanishing pluriform, which embeds `H⁰(X, dD)` equivariantly into the
pluriform space of the subklt snc boundary `B - (k/(d + km))T`, where the representation is
finite.

## Main results

* `MMP.Fourfold.finite_range_pluriformPullback_of_mem_pluricanonicalSections_sub_coeffOnePart`:
  a nonzero section of `H⁰(X, M(K + B) - T)`, `d ∣ M`, forces finite image on `H⁰(X, d(K + B))`.
* `MMP.Fourfold.finite_range_pluriformPullback_logPluricanonicalSections_of_isVertical`:
  crepant self-maps preserve `H⁰(X, d(K + B))` and act on it with finite image when the floor
  `B^{=1}` is vertical.

## Implementation notes

* A birational self-map is recorded by its pull-back, a `ℂ`-automorphism of `k(X)`
  (`MMP.Fourfold.FunctionFieldEquiv`); the crepant ones form
  `MMP.Fourfold.crepantBirationalAutomorphisms`, acting by `MMP.Fourfold.pluriformPullback`.
* The image of the representation in `GL(H⁰(X, dD))` is stated as the finiteness of the set of
  maps `s ↦ σ^* s` on `H⁰(X, dD)`, `σ` crepant; the conclusion also records that each crepant
  self-map preserves `H⁰(X, dD)`, so that the representation is defined.
* The semiample contraction is a contraction `f` (`MMP.Fourfold.IsContraction`) with
  `r(K + B) = f^*A` for an ample Cartier `A`, as in
  `MMP.Fourfold.exists_pluricanonicalSections_sub_coeffOnePart_ne_bot`.

## References

* [O. Fujino, Y. Gongyo, *Log pluricanonical representations and the abundance conjecture*],
  Compositio Math. 150 (2014).
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Fourfold

universe u

section Coordinates

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}

/-- In coordinates along a basis `b` of the line `Ω^n_{k(X)/k}`, pull-back by a `k`-automorphism
`σ` of `k(X)` multiplies the transported coordinate by a fixed power: there is `u ≠ 0` with
`σ^*(c b^{⊗a}) = σ(c) u^a b^{⊗a}` for all `a`. -/
private theorem exists_repr_pluriformPullback (hn : topologicalKrullDim X = n)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]))
    (σ : FunctionFieldEquiv sX sX) :
    letI := functionFieldAlgebra sX
    ∃ u : X.functionField, u ≠ 0 ∧ ∀ (a : ℕ) (τ : RationalPluriForms sX n a),
      (ZTensorPower.basis b a).repr (pluriformPullback sX sX σ.toHom n a τ) () =
        σ ((ZTensorPower.basis b a).repr τ ()) * u ^ a := by
  let := functionFieldAlgebra sX
  have hspan : Submodule.span X.functionField {b ()} = ⊤ := by
    rw [← b.span_eq, Set.range_unique]
  have hω := isPullbackGenerator_functionFieldHom hn hn σ.toHom hspan (b.ne_zero ())
  obtain ⟨ω', hω'0, hω'⟩ : ∃ ω' : ⋀[X.functionField]^n Ω[X.functionField⁄k], ω' ≠ 0 ∧
      ∀ (a : ℕ) (c : X.functionField),
        pluriformPullback sX sX σ.toHom n a (c • formPow (b ()) a) = σ c • formPow ω' a :=
    ⟨_, hω.2.2, fun a c => pluriformPullback_smul_formPow σ.toHom hω a c⟩
  refine ⟨b.repr ω' (), ?_, fun a τ => ?_⟩
  · intro h
    apply hω'0
    rw [← basis_unit_repr_smul b ω', h, zero_smul]
  · conv_lhs => rw [eq_repr_smul_formPow b τ, hω', ← basis_unit_repr_smul b ω', formPow_smul,
      smul_smul, repr_smul_formPow]

variable (b : letI := functionFieldAlgebra sX
  Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]))

/-- The product `∏_{i ∈ S} f_i` of a finite family of `a`-canonical forms, as a form of degree
`e` (meant to be `|S| a`), computed in coordinates along the basis `b` of the line. -/
public noncomputable def prodForm {ι : Type*} (S : Finset ι) {a : ℕ}
    (f : ι → RationalPluriForms sX n a) (e : ℕ) : RationalPluriForms sX n e :=
  letI := functionFieldAlgebra sX
  (∏ i ∈ S, (ZTensorPower.basis b a).repr (f i) ()) • formPow (b ()) e

omit [CharZero k] [LocallyOfFiniteType sX] in
/-- The coordinate of `∏_{i ∈ S} f_i` is the product of the coordinates. -/
public theorem repr_prodForm {ι : Type*} (S : Finset ι) {a : ℕ}
    (f : ι → RationalPluriForms sX n a) (e : ℕ) :
    letI := functionFieldAlgebra sX
    (ZTensorPower.basis b e).repr (prodForm b S f e) () =
      ∏ i ∈ S, (ZTensorPower.basis b a).repr (f i) () := by
  let := functionFieldAlgebra sX
  exact repr_smul_formPow b e _

omit [CharZero k] [LocallyOfFiniteType sX] in
/-- A product of nonzero forms is nonzero. -/
public theorem prodForm_ne_zero {ι : Type*} {S : Finset ι} {a : ℕ}
    {f : ι → RationalPluriForms sX n a} (hf : ∀ i ∈ S, f i ≠ 0) (e : ℕ) :
    prodForm b S f e ≠ 0 := by
  let := functionFieldAlgebra sX
  intro h
  have h1 := repr_prodForm b S f e
  have h0 : (ZTensorPower.basis b e).repr (prodForm b S f e) = 0 :=
    (ZTensorPower.basis b e).repr.map_eq_zero_iff.mpr h
  rw [h0] at h1
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => repr_ne_zero_of_ne_zero b (hf i hi)) h1.symm

/-- Pull-back of a product form is the product form of the pull-backs. -/
private theorem pluriformPullback_prodForm (hn : topologicalKrullDim X = n)
    (σ : FunctionFieldEquiv sX sX) {ι : Type*} (S : Finset ι) {a : ℕ}
    (f : ι → RationalPluriForms sX n a) {e : ℕ} (he : e = S.card * a) :
    pluriformPullback sX sX σ.toHom n e (prodForm b S f e) =
      prodForm b S (fun i => pluriformPullback sX sX σ.toHom n a (f i)) e := by
  let := functionFieldAlgebra sX
  obtain ⟨u, -, hu⟩ := exists_repr_pluriformPullback hn b σ
  rw [eq_repr_smul_formPow b (pluriformPullback sX sX σ.toHom n e (prodForm b S f e)), hu,
    repr_prodForm, prodForm]
  congr 1
  rw [map_prod, he, pow_mul', ← Finset.prod_const]
  exact Finset.prod_mul_distrib.symm.trans
    (Finset.prod_congr rfl fun i _ => (hu a (f i)).symm)

variable [IsLocallyNoetherian X]

/-- Orders of a finite product of nonzero rational functions add up. -/
private theorem ord_prod {ι : Type*} (S : Finset ι) {g : ι → X.functionField}
    (hg : ∀ i ∈ S, g i ≠ 0) (x : X) : X.ord (∏ i ∈ S, g i) x = ∑ i ∈ S, X.ord (g i) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      Scheme.ord_mul (hg j (Finset.mem_insert_self j S))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

variable [IsNormal X]

/-- The order of a product form is the sum of the orders. -/
public theorem ordForm_prodForm (hn : topologicalKrullDim X = n) (Γ : MMP.Mori.PrimeDivisor X)
    {ι : Type*} {S : Finset ι} {a : ℕ} {f : ι → RationalPluriForms sX n a}
    (hf : ∀ i ∈ S, f i ≠ 0) {e : ℕ} (he : e = S.card * a) :
    Γ.ordForm (prodForm b S f e) = ∑ i ∈ S, Γ.ordForm (f i) := by
  let := functionFieldAlgebra sX
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) b
  rw [hN e _ (prodForm_ne_zero b hf e), repr_prodForm]
  refine (congrArg (· + (e : ℤ) * N)
    (ord_prod S (fun i hi => repr_ne_zero_of_ne_zero b (hf i hi)) Γ.genericPoint)).trans ?_
  rw [Finset.sum_congr rfl fun i hi => hN a (f i) (hf i hi), Finset.sum_add_distrib, he]
  simp only [Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- A product of `|S|` nonzero sections of `𝒪_X(aK + G)` is a section of `𝒪_X(|S|(aK + G))`. -/
private theorem prodForm_mem_pluricanonicalSections (hn : topologicalKrullDim X = n)
    {ι : Type*} {S : Finset ι} {a : ℕ} {f : ι → RationalPluriForms sX n a} {G : Divisor X}
    (hf0 : ∀ i ∈ S, f i ≠ 0) (hf : ∀ i ∈ S, f i ∈ pluricanonicalSections sX n a G ⊤) {e : ℕ}
    (he : e = S.card * a) :
    prodForm b S f e ∈ pluricanonicalSections sX n e (S.card • G) ⊤ := by
  refine (mem_pluricanonicalSections_of_ne_bot top_ne_bot).2 fun Γ hΓ _ => ?_
  have := Finset.sum_nonneg fun i hi => (hf i hi).2 Γ hΓ (hf0 i hi)
  rw [Finset.sum_add_distrib, Finset.sum_const] at this
  rwa [ordForm_prodForm b hn Γ hf0 he, DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply]

end Coordinates

section Divisors

variable {X : Scheme.{u}}

/-- When `bB` is integral, `⌊(a + jb)B⌋ = ⌊aB⌋ + j⌊bB⌋`. -/
public theorem roundDown_smul_add_mul (B : QDivisor X) {b : ℕ}
    (hb : ∀ P, ∃ z : ℤ, (b : ℚ) * B.coeff P = z) (a j : ℕ) :
    DivisorWithCoeffs.roundDown (((a + j * b : ℕ) : ℤ) • B) =
      DivisorWithCoeffs.roundDown ((a : ℤ) • B) +
        j • DivisorWithCoeffs.roundDown ((b : ℤ) • B) := by
  ext P
  obtain ⟨z, hz⟩ := hb P
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_apply (j • _), Finsupp.smul_apply,
    ← DivisorWithCoeffs.coeff_apply]
  simp only [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast]
  rw [show ((a + j * b : ℕ) : ℚ) * B.coeff P = (a : ℚ) * B.coeff P + ((j * z : ℤ) : ℚ) by
    push_cast; rw [← hz]; ring, Int.floor_add_intCast, hz, Int.floor_intCast, nsmul_eq_mul]

/-- `⌊N(B - (a/N)T)⌋ = ⌊NB⌋ - aT`, `T = B^{=1}`. -/
private theorem roundDown_smul_sub_coeffOnePart (B : QDivisor X) {N : ℕ} (hN : 0 < N) (a : ℤ) :
    DivisorWithCoeffs.roundDown
        ((N : ℤ) • (B - ((a : ℚ) / N) • Divisor.toQDivisor (coeffOnePart B))) =
      DivisorWithCoeffs.roundDown ((N : ℤ) • B) - a • coeffOnePart B := by
  ext P
  have hN' : (N : ℚ) ≠ 0 := by positivity
  rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_roundDown,
    DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul, zsmul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  have e : ((N : ℤ) : ℚ) * (B.coeff P - (a : ℚ) / N * ((coeffOnePart B).coeff P : ℚ)) =
      ((N : ℤ) : ℚ) * B.coeff P - ((a * (coeffOnePart B).coeff P : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [e, Int.floor_sub_intCast]

variable {k : Type u} [Field k] {sX : X ⟶ Spec (.of k)}

/-- Lowering the coefficient-one part of an snc subboundary by `c > 0` gives an snc subboundary
with all coefficients less than one. -/
private theorem isSNCSubboundaryPair_sub_smul_coeffOnePart {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) {c : ℚ} (hc : 0 < c) :
    IsSNCSubboundaryPair sX (B - c • Divisor.toQDivisor (coeffOnePart B)) ∧
      ∀ P, (B - c • Divisor.toQDivisor (coeffOnePart B)).coeff P < 1 := by
  have hcoeff : ∀ P, (B - c • Divisor.toQDivisor (coeffOnePart B)).coeff P =
      B.coeff P - c * (if B.coeff P = 1 then 1 else 0) := by
    intro P
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
      coeff_coeffOnePart, smul_eq_mul]
    split_ifs <;> simp
  have hlt : ∀ P, (B - c • Divisor.toQDivisor (coeffOnePart B)).coeff P < 1 := by
    intro P
    rw [hcoeff]
    split_ifs with h
    · linarith
    · have := hXB.coeff_le_one P
      have : B.coeff P < 1 := lt_of_le_of_ne this h
      linarith
  refine ⟨⟨hXB.isProjectiveVariety, hXB.isSmoothScheme, hXB.isSNC.of_support_subset ?_,
    fun P => (hlt P).le⟩, hlt⟩
  intro P hP
  rw [Finsupp.mem_support_iff] at hP ⊢
  intro h0
  apply hP
  have := hcoeff P
  rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply] at this
  rw [this, h0]
  simp

variable [IsLocallyNoetherian X] [IsNormal X]

/-- If `d(K + B)` is Cartier then `NB` is integral for `d ∣ N`. -/
public theorem exists_mul_coeff_eq_intCast {K : Divisor X} {B : QDivisor X} {d N : ℕ}
    (hdD : ((d : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) (hdN : d ∣ N)
    (P : MMP.Mori.PrimeDivisor X) : ∃ z : ℤ, (N : ℚ) * B.coeff P = z := by
  obtain ⟨Dd, hDd, -⟩ := hdD
  obtain ⟨j, rfl⟩ := hdN
  refine ⟨j * (Dd.coeff P - d * K.coeff P), ?_⟩
  have := congrArg (fun D : QDivisor X => D.coeff P) hDd
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_add, zsmul_eq_mul] at this
  push_cast at this ⊢
  linear_combination (-(j : ℚ)) * this

/-- If `d(K + B)` is Cartier then so is `N(K + B)` for `d ∣ N`. -/
public theorem isCartierDivisor_smul_of_dvd {K : Divisor X} {B : QDivisor X} {d N : ℕ}
    (hdD : ((d : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) (hdN : d ∣ N) :
    ((N : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor := by
  obtain ⟨Dd, hDd, hDdc⟩ := hdD
  obtain ⟨j, rfl⟩ := hdN
  refine ⟨j • Dd, ?_, hDdc.nsmul j⟩
  rw [map_nsmul, hDd, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
  push_cast
  ring_nf

end Divisors

section Functoriality

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}

/-- `σ^* τ^* = (σ τ)^*` on rational pluriforms. -/
private theorem pluriformPullback_pluriformPullback (hn : topologicalKrullDim X = n) (m : ℤ)
    (σ τ : FunctionFieldEquiv sX sX) (x : RationalPluriForms sX n m) :
    pluriformPullback sX sX σ.toHom n m (pluriformPullback sX sX τ.toHom n m x) =
      pluriformPullback sX sX (σ * τ).toHom n m x := by
  let := functionFieldAlgebra sX
  rw [pluriformPullback_comp hn hn hn m σ.toHom τ.toHom x]
  rfl

/-- Pull-back along a `k`-automorphism of `k(X)` is injective. -/
private theorem eq_zero_of_pluriformPullback_eq_zero (hn : topologicalKrullDim X = n) {m : ℤ}
    (σ : FunctionFieldEquiv sX sX) {x : RationalPluriForms sX n m}
    (h : pluriformPullback sX sX σ.toHom n m x = 0) : x = 0 := by
  rw [← pluriformPullback_one hn m x, ← inv_mul_cancel σ,
    ← pluriformPullback_pluriformPullback hn, h, map_zero]

end Functoriality

section Sections

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {n : ℕ}

/-- Sections of `𝒪_X(aK + G)` and `𝒪_X(bK + G')` multiply into `𝒪_X((a + b)K + G + G')`. -/
public theorem mul_mem_pluricanonicalSections {a b : ℕ} {G G' : Divisor X}
    {τ : RationalPluriForms sX n a} {τ' : RationalPluriForms sX n b}
    (hτ : τ ∈ pluricanonicalSections sX n a G ⊤) (hτ' : τ' ∈ pluricanonicalSections sX n b G' ⊤) :
    RationalPluriForms.mul sX n a b τ τ' ∈ pluricanonicalSections sX n (a + b : ℕ) (G + G') ⊤ := by
  refine (mem_pluricanonicalSections_of_ne_bot top_ne_bot).2 fun Γ hΓ h0 => ?_
  have hτ0 : τ ≠ 0 := fun h => h0 (by rw [h, map_zero, LinearMap.zero_apply])
  have hτ0' : τ' ≠ 0 := fun h => h0 (by rw [h, map_zero])
  have h1 := hτ.2 Γ hΓ hτ0
  have h2 := hτ'.2 Γ hΓ hτ0'
  rw [ordForm_mul Γ hτ0 hτ0', DivisorWithCoeffs.coeff_add]
  omega

/-- `H⁰(X, N(K + B - (a/N)T)) = H⁰(X, NK + ⌊NB⌋ - aT)`, `T = B^{=1}`. -/
public theorem mem_logPluricanonicalSections_sub_iff {B : QDivisor X} {N : ℕ} (hN : 0 < N)
    {a : ℤ} {τ : RationalPluriForms sX n N} :
    τ ∈ logPluricanonicalSections sX n N
        (B - ((a : ℚ) / N) • Divisor.toQDivisor (coeffOnePart B)) ↔
      τ ∈ pluricanonicalSections sX n N
        (DivisorWithCoeffs.roundDown ((N : ℤ) • B) - a • coeffOnePart B) ⊤ := by
  rw [mem_logPluricanonicalSections, roundDown_smul_sub_coeffOnePart B hN a]

end Sections

/-- Finiteness of a family of maps transfers along an injection of the targets that intertwines
it, through a map of the sources, with a family of finite range. -/
public theorem finite_range_of_injective_comp {ι S V R R' : Type*} {F : ι → S → R}
    {H : ι → V → R'} (hH : (Set.range H).Finite) {μ : R → R'} (hμ : Function.Injective μ)
    (e : S → V) (h : ∀ i s, μ (F i s) = H i (e s)) : (Set.range F).Finite := by
  refine Set.Finite.of_finite_image ((hH.image fun ψ => ψ ∘ e).subset ?_)
    (hμ.comp_left (α := S)).injOn
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨_, ⟨i, rfl⟩, (funext (h i)).symm⟩

section Representation

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} {K : Divisor X} {d : ℕ}

/-- Crepant birational self-maps of an snc surface pair act with finite image on
`H⁰(X, N(K + B) - aT)`, `T = B^{=1}`, for `a ≥ 1` and `d ∣ N` with `d(K + B)` Cartier: these are
the sections of the subklt snc pair `(X, B - (a/N)T)`. -/
public theorem finite_range_pluriformPullback_sub_coeffOnePart
    (hXB : IsSNCSubboundaryPair sX B) (hK : K.IsCanonicalDivisor sX 2)
    (hdD : ((d : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) {N : ℕ} (hN : 0 < N)
    (hdN : d ∣ N) {a : ℤ} (ha : 1 ≤ a) :
    (Set.range fun (σ : crepantBirationalAutomorphisms sX B)
        (s : logPluricanonicalSections sX 2 N
          (B - ((a : ℚ) / N) • Divisor.toQDivisor (coeffOnePart B))) =>
      pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 N
        (s : RationalPluriForms sX 2 N)).Finite := by
  obtain ⟨h1, h2⟩ := isSNCSubboundaryPair_sub_smul_coeffOnePart hXB
    (div_pos (by exact_mod_cast ha) (by exact_mod_cast hN) : (0 : ℚ) < a / N)
  refine finite_range_pluriformPullback_logPluricanonicalSections.1 hK.topologicalKrullDim_eq
    h1 h2 hN (fun P => ?_) _ fun σ hσ s hs => ?_
  · obtain ⟨z, hz⟩ := exists_mul_coeff_eq_intCast hdD hdN P
    refine ⟨z - a * (coeffOnePart B).coeff P, ?_⟩
    have hN' : (N : ℚ) ≠ 0 := by positivity
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
      smul_eq_mul, mul_sub, hz]
    push_cast
    field_simp
  · rw [mem_logPluricanonicalSections_sub_iff hN] at hs ⊢
    exact (pluriformPullback_mem_pluricanonicalSections_sub_coeffOnePart_iff hXB hK hN
      (isCartierDivisor_smul_of_dvd hdD hdN) ha hσ s).2 hs

/-- **Crepant maps preserve `H⁰(X, d(K + B))`** as soon as `H⁰(X, m(K + B) - T)` has a nonzero
section for some `d ∣ m`. -/
private theorem pluriformPullback_mem_logPluricanonicalSections
    (hXB : IsSNCSubboundaryPair sX B) (hK : K.IsCanonicalDivisor sX 2)
    (hd : 0 < d) (hdD : ((d : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) {m : ℕ}
    (hdm : d ∣ m) {s₀ : RationalPluriForms sX 2 m} (hs₀0 : s₀ ≠ 0)
    (hs₀ : s₀ ∈ pluricanonicalSections sX 2 m
      (DivisorWithCoeffs.roundDown ((m : ℤ) • B) - (1 : ℤ) • coeffOnePart B) ⊤)
    {σ : FunctionFieldEquiv sX sX} (hσ : σ ∈ crepantBirationalAutomorphisms sX B)
    {s : RationalPluriForms sX 2 d} (hs : s ∈ logPluricanonicalSections sX 2 d B) :
    pluriformPullback sX sX σ.toHom 2 d s ∈ logPluricanonicalSections sX 2 d B := by
  have hn := hK.topologicalKrullDim_eq
  have : LocallyOfFiniteType sX := hXB.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hn
  have hdB := exists_mul_coeff_eq_intCast hdD dvd_rfl
  by_cases hs0 : s = 0
  · rw [hs0, map_zero]
    exact zero_mem _
  rw [mem_logPluricanonicalSections] at hs ⊢
  refine (mem_pluricanonicalSections_of_ne_bot top_ne_bot).2 fun Γ hΓ hσs0 => ?_
  by_contra hlt
  push Not at hlt
  have hσs₀ : pluriformPullback sX sX σ.toHom 2 m s₀ ≠ 0 :=
    fun h => hs₀0 (eq_zero_of_pluriformPullback_eq_zero hn σ h)
  set C := Γ.ordForm (pluriformPullback sX sX σ.toHom 2 m s₀) +
    (DivisorWithCoeffs.roundDown ((m : ℤ) • B) - (1 : ℤ) • coeffOnePart B).coeff Γ
  set j := C.toNat + 1
  have hjd : j * d = (Finset.range j).card * d := by rw [Finset.card_range]
  have hx : RationalPluriForms.mul sX 2 m (j * d) s₀
      (prodForm b (Finset.range j) (fun _ => s) (j * d)) ∈
      pluricanonicalSections sX 2 (m + j * d : ℕ)
        (DivisorWithCoeffs.roundDown (((m + j * d : ℕ) : ℤ) • B) - (1 : ℤ) • coeffOnePart B) ⊤ := by
    rw [roundDown_smul_add_mul B hdB m j, add_sub_right_comm]
    have := prodForm_mem_pluricanonicalSections b hn (fun _ _ => hs0) (fun _ _ => hs) hjd
    rw [Finset.card_range] at this
    exact mul_mem_pluricanonicalSections hs₀ this
  have hy := (pluriformPullback_mem_pluricanonicalSections_sub_coeffOnePart_iff hXB hK
    (by positivity) (isCartierDivisor_smul_of_dvd hdD (dvd_add hdm (dvd_mul_left d j))) le_rfl
    hσ _).2 hx
  rw [pluriformPullback_mul, pluriformPullback_prodForm b hn σ _ _ hjd] at hy
  have hσP0 := prodForm_ne_zero b (fun _ _ => hσs0) (j * d) (S := Finset.range j)
  have hy' := hy.2 Γ hΓ (RationalPluriForms.mul_ne_zero hn hσs₀ hσP0)
  rw [ordForm_mul Γ hσs₀ hσP0, ordForm_prodForm b hn Γ (fun _ _ => hσs0) hjd, Finset.sum_const,
    Finset.card_range, roundDown_smul_add_mul B hdB m j, add_sub_right_comm,
    DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_apply (j • _), Finsupp.smul_apply,
    ← DivisorWithCoeffs.coeff_apply] at hy'
  have hjC : C + 1 ≤ (j : ℤ) := by omega
  simp only [nsmul_eq_mul] at hy'
  nlinarith

/-- **An invariant section vanishing along `T`.** If `s₀ ≠ 0` lies in `H⁰(X, m(K + B) - T)`,
`T = B^{=1}`, with `d ∣ m`, then for some `j ≥ 1` there is a nonzero section of
`H⁰(X, j(m(K + B) - T))` fixed by every crepant birational self-map. -/
public theorem exists_invariant_mem_pluricanonicalSections
    (hXB : IsSNCSubboundaryPair sX B) (hK : K.IsCanonicalDivisor sX 2)
    (hdD : ((d : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) {m : ℕ} (hm : 0 < m)
    (hdm : d ∣ m) {s₀ : RationalPluriForms sX 2 m} (hs₀0 : s₀ ≠ 0)
    (hs₀ : s₀ ∈ pluricanonicalSections sX 2 m
      (DivisorWithCoeffs.roundDown ((m : ℤ) • B) - (1 : ℤ) • coeffOnePart B) ⊤) :
    ∃ j : ℕ, 1 ≤ j ∧ ∃ t : RationalPluriForms sX 2 (j * m : ℕ), t ≠ 0 ∧
      t ∈ pluricanonicalSections sX 2 (j * m : ℕ)
        (j • (DivisorWithCoeffs.roundDown ((m : ℤ) • B) - (1 : ℤ) • coeffOnePart B)) ⊤ ∧
      ∀ σ ∈ crepantBirationalAutomorphisms sX B,
        pluriformPullback sX sX σ.toHom 2 (j * m : ℕ) t = t := by
  classical
  have hn := hK.topologicalKrullDim_eq
  have : LocallyOfFiniteType sX := hXB.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hn
  set G := crepantBirationalAutomorphisms sX B
  have hs₀W := (mem_logPluricanonicalSections_sub_iff hm).2 hs₀
  have hOfin : (Set.range fun σ : G =>
      pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 m s₀).Finite := by
    refine ((finite_range_pluriformPullback_sub_coeffOnePart hXB hK hdD hm hdm le_rfl).image
      fun φ => φ ⟨s₀, hs₀W⟩).subset ?_
    rintro _ ⟨σ, rfl⟩
    exact ⟨_, ⟨σ, rfl⟩, rfl⟩
  set O := hOfin.toFinset
  have hmemO : ∀ o, o ∈ O ↔
      ∃ σ : G, pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 m s₀ = o :=
    fun o => by rw [Set.Finite.mem_toFinset, Set.mem_range]
  have hO0 : ∀ o ∈ O, o ≠ 0 := by
    intro o ho h0
    obtain ⟨σ, rfl⟩ := (hmemO o).1 ho
    exact hs₀0 (eq_zero_of_pluriformPullback_eq_zero hn _ h0)
  have hOW : ∀ o ∈ O, o ∈ pluricanonicalSections sX 2 m
      (DivisorWithCoeffs.roundDown ((m : ℤ) • B) - (1 : ℤ) • coeffOnePart B) ⊤ := by
    intro o ho
    obtain ⟨σ, rfl⟩ := (hmemO o).1 ho
    exact (pluriformPullback_mem_pluricanonicalSections_sub_coeffOnePart_iff hXB hK hm
      (isCartierDivisor_smul_of_dvd hdD hdm) le_rfl σ.2 s₀).2 hs₀
  have hOmap : ∀ σ ∈ G, ∀ o ∈ O, pluriformPullback sX sX σ.toHom 2 m o ∈ O := by
    intro σ hσ o ho
    obtain ⟨τ, rfl⟩ := (hmemO o).1 ho
    exact (hmemO _).2
      ⟨⟨σ * τ, mul_mem hσ τ.2⟩, (pluriformPullback_pluriformPullback hn _ σ τ s₀).symm⟩
  refine ⟨O.card, Finset.card_pos.2 ⟨s₀, (hmemO s₀).2 ⟨1, pluriformPullback_one hn _ s₀⟩⟩,
    prodForm b O id (O.card * m), prodForm_ne_zero b hO0 _,
    prodForm_mem_pluricanonicalSections b hn hO0 hOW rfl, fun σ hσ => ?_⟩
  rw [pluriformPullback_prodForm b hn σ O id rfl]
  simp only [prodForm, id]
  congr 1
  refine Finset.prod_nbij' (fun o => pluriformPullback sX sX σ.toHom 2 m o)
    (fun o => pluriformPullback sX sX σ⁻¹.toHom 2 m o)
    (fun o ho => hOmap σ hσ o ho) (fun o ho => hOmap σ⁻¹ (inv_mem hσ) o ho)
    (fun o _ => ?_) (fun o _ => ?_) (fun o _ => rfl)
  · rw [pluriformPullback_pluriformPullback hn, inv_mul_cancel, pluriformPullback_one hn]
  · rw [pluriformPullback_pluriformPullback hn, mul_inv_cancel, pluriformPullback_one hn]

/-- **Finite crepant image from a section vanishing along the floor.** On an snc subboundary
surface pair `(X, B)` with `d(K + B)` Cartier, a nonzero section `s₀` of `H⁰(X, M(K + B) - T)`,
`T = B^{=1}`, `d ∣ M`, makes the crepant self-maps act with finite image on `H⁰(X, d(K + B))`. -/
public theorem finite_range_pluriformPullback_of_mem_pluricanonicalSections_sub_coeffOnePart
    (hXB : IsSNCSubboundaryPair sX B) (hK : K.IsCanonicalDivisor sX 2)
    (hdD : ((d : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) {M : ℕ} (hM : 0 < M)
    (hdM : d ∣ M) {s₀ : RationalPluriForms sX 2 M} (hs₀0 : s₀ ≠ 0)
    (hs₀ : s₀ ∈ pluricanonicalSections sX 2 M
      (DivisorWithCoeffs.roundDown ((M : ℤ) • B) - (1 : ℤ) • coeffOnePart B) ⊤) :
    (Set.range fun (σ : crepantBirationalAutomorphisms sX B)
        (s : logPluricanonicalSections sX 2 d B) =>
      pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 d
        (s : RationalPluriForms sX 2 d)).Finite := by
  have : LocallyOfFiniteType sX := hXB.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  obtain ⟨j, hj, t, ht0, ht, htinv⟩ :=
    exists_invariant_mem_pluricanonicalSections hXB hK hdD hM hdM hs₀0 hs₀
  have hN : 0 < d + j * M := by positivity
  refine finite_range_of_injective_comp (finite_range_pluriformPullback_sub_coeffOnePart hXB hK
    hdD hN (dvd_add dvd_rfl (dvd_mul_of_dvd_right hdM j)) (a := j) (by exact_mod_cast hj))
    (μ := fun y => RationalPluriForms.mul sX 2 d (j * M) y t) (fun y y' h => ?_)
    (fun s => ⟨RationalPluriForms.mul sX 2 d (j * M) s t,
      (mem_logPluricanonicalSections_sub_iff hN).2 ?_⟩) fun σ s => ?_
  · by_contra hne
    apply RationalPluriForms.mul_ne_zero hK.topologicalKrullDim_eq (sub_ne_zero.mpr hne) ht0
    rw [map_sub, LinearMap.sub_apply]
    exact sub_eq_zero.2 h
  · have := mul_mem_pluricanonicalSections s.2 ht
    have hjT : j • ((1 : ℤ) • coeffOnePart B) = (j : ℤ) • coeffOnePart B := by simp
    rwa [roundDown_smul_add_mul B (exists_mul_coeff_eq_intCast hdD hdM) d j, add_sub_assoc,
      ← hjT, ← smul_sub]
  · rw [pluriformPullback_mul, htinv σ σ.2]

end Representation

/-- **Finite crepant representations of a semiample surface pair with vertical floor.** Let `X`
be a smooth projective complex surface, `B` an snc `ℚ`-divisor with all coefficients at most one
(`MMP.Fourfold.IsSNCSubboundaryPair`), `K` a canonical divisor with `K + B` semiample, and
`f : X ⟶ Y` a contraction with `r(K + B) = f^*A` for some `r > 0` and some ample Cartier divisor
`A` on `Y`. Suppose every prime divisor along which `B` has coefficient one has image a proper
subset of `Y`. Then for every `d > 0` with `d(K + B)` Cartier, every crepant birational self-map
of `(X, B)` (`MMP.Fourfold.crepantBirationalAutomorphisms`) preserves
`H⁰(X, d(K + B))` (`MMP.Fourfold.logPluricanonicalSections`) under pluriform pull-back, and the
set of maps `s ↦ σ^* s` on it, `σ` crepant, is finite. -/
@[mmp "lem_fourfold_vertical_surface_lc_representation_finite"]
public theorem finite_range_pluriformPullback_logPluricanonicalSections_of_isVertical
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} (hn : topologicalKrullDim X = 2)
    {B : QDivisor X} (hXB : IsSNCSubboundaryPair sX B)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    (hD : Flips.IsEventuallyFree ℂ sX (Divisor.toQDivisor K + B))
    {f : X ⟶ Y} (hf : IsContraction sX sY f)
    {r : ℕ} (hr : 0 < r) {A : Divisor Y} (hAc : A.IsCartier) (hA : A.IsAmple hAc)
    (hrD : ∃ hAf : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ A.supp,
      Divisor.toQDivisor (A.pullback hAc hAf) = (r : ℚ) • (Divisor.toQDivisor K + B))
    (hT : ∀ P : Mori.PrimeDivisor X, B.coeff P = 1 → f '' P.support ≠ Set.univ)
    {d : ℕ} (hd : 0 < d) (hdD : ((d : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) :
    (∀ σ ∈ crepantBirationalAutomorphisms sX B, ∀ s ∈ logPluricanonicalSections sX 2 d B,
        pluriformPullback sX sX σ.toHom 2 d s ∈ logPluricanonicalSections sX 2 d B) ∧
      (Set.range fun (σ : crepantBirationalAutomorphisms sX B)
          (s : logPluricanonicalSections sX 2 d B) =>
        pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 d
          (s : RationalPluriForms sX 2 d)).Finite := by
  obtain ⟨m, hm, ⟨e, rfl⟩, hW⟩ := exists_pluricanonicalSections_sub_coeffOnePart_ne_bot hXB hK
    hD hf hr hAc hA hrD hT (a := 1) le_rfl hd 1
  obtain ⟨⟨s₀, hs₀⟩, hs₀0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hW
  replace hs₀0 : s₀ ≠ 0 := fun h => hs₀0 (Subtype.ext h)
  refine ⟨fun σ hσ s hs => pluriformPullback_mem_logPluricanonicalSections hXB hK hd hdD
    (dvd_mul_right d e) hs₀0 hs₀ hσ hs, ?_⟩
  exact finite_range_pluriformPullback_of_mem_pluricanonicalSections_sub_coeffOnePart hXB hK hdD
    hm (dvd_mul_right d e) hs₀0 hs₀

end MMP.Fourfold
