module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import MMP.RingTheory.RegularLocalRing.SpanMaximalIdeal
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import MMP.AlgebraicGeometry.Variety.SingularLocus
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import StacksFrontier.RingTheory.NormalCrossingsChart.RegularHypersurfaceShrink

/-!
# A uniformizer along a component of a principal divisor on a normal variety

Let `X` be a normal variety over a field `K`, `X₀ ⊆ X` a non-empty affine open with ring
`A = Γ(X, X₀)`, `h ∈ A` non-zero and `Z` a subvariety of `X` with `Z ∩ X₀` an irreducible
component of the zero locus `V(h) = X₀ - D(h)`, and let `m = ord_Z(h)`. Let `𝔭 ⊂ A` be the prime
of the generic point of `Z`. Then `𝔭` is minimal over `h`, so by Krull's principal ideal theorem
`𝒪_{X,Z} = A_𝔭` is a one-dimensional normal local domain, a discrete valuation ring; let `π ∈ A`
map to a uniformizer, so that `h = v πᵐ` in `A_𝔭` with `v` a unit, and `m ≥ 1`.

These identities spread out to a basic open neighbourhood `D(s)` of the generic point of `Z`:
there are `t, u ∈ A` invertible on `D(s)` with `t h = u πᵐ`, and `s 𝔭 ⊆ (π)`, so that on `D(s)`
the zero loci of `h` and `π` both equal `Z`. Shrinking further, `D(s)` lies in the regular locus
of `X`, `D(s) ∩ Z` in the image of the regular locus of `Z`, `D(s)` misses every other component
of `V(h)` (a component meeting `D(s)` is the closure of its intersection with `D(s) ∩ V(h)`,
which lies in `Z`), and `𝒪_{X,x}/(π)` is regular at every point `x ∈ D(s) ∩ Z`: the quotient
`A/(π)` is of finite type over `K`, hence J-1 (Stacks, Tag 07R5), and `A_𝔭/(π)` is the residue
field of `A_𝔭`.

## Main results

* `MMP.LocalNormalForm.exists_uniformizer_of_maximal`: the data `s, π, t, u` above.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2 and Appendix B.
* [Stacks Project, Tag 07R5](https://stacks.math.columbia.edu/tag/07R5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Topology IsLocalRing TopologicalSpace

universe u

namespace MMP

namespace LocalNormalForm

/-- If every element `a` of a finitely generated ideal `I` has a multiple `s a ∈ J` with `s ∈ M`,
one `s ∈ M` works for all of `I`. -/
lemma exists_mul_mem_of_fg {A : Type*} [CommRing A] {I J : Ideal A} (hI : I.FG)
    {M : Submonoid A} (h : ∀ a ∈ I, ∃ s ∈ M, s * a ∈ J) : ∃ s ∈ M, ∀ a ∈ I, s * a ∈ J := by
  classical
  obtain ⟨S, rfl⟩ := hI
  choose! f hfM hf using h
  refine ⟨∏ a ∈ S, f a, prod_mem fun a ha ↦ hfM a (Submodule.subset_span ha), fun a ha ↦ ?_⟩
  induction ha using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ hx, mul_assoc]
    exact J.mul_mem_left _ (hf x (Submodule.subset_span hx))
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact J.add_mem hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, mul_left_comm]
    exact J.mul_mem_left _ hx

/-- A noetherian integrally closed local domain of Krull dimension one is a discrete valuation
ring. -/
theorem isDiscreteValuationRing_of_ringKrullDim_eq_one {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (hdim : ringKrullDim R = 1) :
    IsDiscreteValuationRing R := by
  have hnf : ¬IsField R := fun h ↦ zero_ne_one ((ringKrullDim_eq_zero_of_isField h).symm.trans hdim)
  have h1 : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff, hdim]
    rfl
  have : Ring.DimensionLEOne R :=
    ⟨fun hp hpr ↦ Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 _ hp hpr⟩
  have : IsDedekindRing R := IsDedekindRing.mk
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 1 3).mpr IsDedekindDomain.mk

/-- The quotient of a discrete valuation ring by a uniformizer is a regular local ring. -/
theorem isRegularLocalRing_quotient_of_irreducible {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) :
    IsRegularLocalRing (R ⧸ Ideal.span {ϖ}) := by
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hϖ]
  let := Ideal.Quotient.field (maximalIdeal R)
  infer_instance

section Localization

variable {A : Type*} (R : Type*) [CommRing A] [CommRing R] [Algebra A R] (P : Ideal A) [P.IsPrime]
  [IsLocalization.AtPrime R P]

/-- The localization of a noetherian domain at a prime minimal over a non-zero element has Krull
dimension one. -/
theorem ringKrullDim_eq_one_of_mem_minimalPrimes [IsDomain A] [IsNoetherianRing A] {h : A}
    (hh : h ≠ 0) (hP : P ∈ (Ideal.span {h}).minimalPrimes) : ringKrullDim R = 1 := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P R]
  refine le_antisymm
    (by exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP) ?_
  have h0 : P.height ≠ 0 := fun h0 ↦
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes ((Ideal.span_singleton_le_iff_mem _).1 hP.1.2)
      (Ideal.height_eq_zero_iff.mp h0) (mem_nonZeroDivisors_of_ne_zero hh)
  exact_mod_cast Order.one_le_iff_ne_zero.mpr h0

include P in
/-- If the localization `R` of `A` at `P` is a discrete valuation ring, some element of `A` maps to
a uniformizer of `R`. -/
theorem exists_irreducible_algebraMap [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ π : A, Irreducible (algebraMap A R π) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨x, hx⟩ := IsLocalization.surj P.primeCompl ϖ
  refine ⟨x.1, ?_⟩
  rw [← hx]
  exact (irreducible_mul_isUnit (IsLocalization.map_units R x.2)).2 hϖ

/-- If `π ∈ A` maps to a uniformizer of the discrete valuation ring `R = A_P`, a non-zero
`h ∈ P` is `v πᵐ` in `R` with `v` a unit and `m ≥ 1`, and `t h = u πᵐ` in `A` for some
`t, u ∉ P`. -/
theorem exists_mul_eq_mul_pow [IsDomain A] [IsDomain R] [IsDiscreteValuationRing R] {π h : A}
    (hπ : Irreducible (algebraMap A R π)) (hh : h ≠ 0) (hhP : h ∈ P) :
    ∃ (m : ℕ) (v : Rˣ) (t u : A), 0 < m ∧ algebraMap A R h = v * algebraMap A R π ^ m ∧
      t ∉ P ∧ u ∉ P ∧ t * h = u * π ^ m := by
  have hinj := IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors P)
  obtain ⟨m, v, hv⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ((map_ne_zero_iff _ hinj).2 hh) hπ
  have hm : 0 < m := Nat.pos_of_ne_zero fun hm0 ↦
    (mem_maximalIdeal _).1 ((IsLocalization.AtPrime.to_map_mem_maximal_iff R P h).2 hhP) (by
      rw [hv, hm0, pow_zero, mul_one]
      exact v.isUnit)
  obtain ⟨x, hx⟩ := IsLocalization.surj P.primeCompl (v : R)
  have hx₁ : x.1 ∉ P := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R P x.1, mem_maximalIdeal,
      mem_nonunits_iff, not_not, ← hx]
    exact v.isUnit.mul (IsLocalization.map_units R x.2)
  have heq : algebraMap A R (x.2 * h) = algebraMap A R (x.1 * π ^ m) := by
    rw [map_mul, map_mul, map_pow, hv, ← hx]
    ring
  obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists P.primeCompl R).1 heq
  exact ⟨m, v, w * x.2, w * x.1, hm, hv, P.primeCompl.mul_mem w.2 x.2.2,
    P.primeCompl.mul_mem w.2 hx₁, by simpa only [mul_assoc] using hw⟩

/-- If `π ∈ A` maps to a uniformizer of the discrete valuation ring `A_P` and `A` is noetherian,
some `s ∉ P` satisfies `s P ⊆ (π)`. -/
theorem exists_mul_mem_span_singleton [IsNoetherianRing A] [IsDomain R]
    [IsDiscreteValuationRing R] {π : A} (hπ : Irreducible (algebraMap A R π)) :
    ∃ s ∈ P.primeCompl, ∀ a ∈ P, s * a ∈ Ideal.span {π} := by
  refine exists_mul_mem_of_fg (IsNoetherian.noetherian P) fun a ha ↦ ?_
  have ha' : algebraMap A R a ∈ Ideal.span {algebraMap A R π} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R P a).2 ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha'
  obtain ⟨y, hy⟩ := IsLocalization.surj P.primeCompl c
  have hya : algebraMap A R (y.2 * a) = algebraMap A R (y.1 * π) := by
    rw [map_mul, map_mul, ← hc, ← hy]
    ring
  obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists P.primeCompl R).1 hya
  refine ⟨w * y.2, P.primeCompl.mul_mem w.2 y.2.2, ?_⟩
  rw [mul_assoc, hw]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self π))

end Localization

/-- A maximal irreducible subset `T` of `S ⊆ V` meeting an open `U` in a subset of a closed `C`
equals `C ∩ V`, when `C ∩ V` is itself maximal irreducible in `S`. -/
theorem eq_of_maximal_of_inter_subset {α : Type*} [TopologicalSpace α] {S V C T U : Set α}
    (hSV : S ⊆ V) (hC : IsClosed C) (hU : IsOpen U)
    (hZ : Maximal (fun T ↦ IsIrreducible T ∧ T ⊆ S) (C ∩ V))
    (hT : Maximal (fun T ↦ IsIrreducible T ∧ T ⊆ S) T) (hTU : (T ∩ U).Nonempty)
    (hTC : T ∩ U ⊆ C) : T = C ∩ V := by
  have hTC' : T ⊆ C := (subset_closure_inter_of_isPreirreducible_of_isOpen
    hT.prop.1.isPreirreducible hU hTU).trans (closure_minimal hTC hC)
  have hTCV : T ⊆ C ∩ V := fun y hy ↦ ⟨hTC' hy, hSV (hT.prop.2 hy)⟩
  exact le_antisymm hTCV (hT.2 hZ.prop hTCV)

/-- A point of `Spec Γ(X, X₀)` lies in `D(a)` exactly when its prime does not contain `a`. -/
theorem fromSpec_mem_basicOpen_iff {X : Scheme.{u}} {X₀ : X.Opens} (hX₀ : IsAffineOpen X₀)
    (Q : Spec Γ(X, X₀)) (a : Γ(X, X₀)) : hX₀.fromSpec Q ∈ X.basicOpen a ↔ a ∉ Q.asIdeal := by
  change Q ∈ hX₀.fromSpec ⁻¹ᵁ X.basicOpen a ↔ _
  rw [hX₀.fromSpec_preimage_basicOpen]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- A point `x ∈ X₀` lies in `D(a)` exactly when its prime in `Γ(X, X₀)` does not contain `a`. -/
theorem mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {X₀ : X.Opens}
    (hX₀ : IsAffineOpen X₀) {x : X} (hx : x ∈ X₀) (a : Γ(X, X₀)) :
    x ∈ X.basicOpen a ↔ a ∉ (hX₀.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have := fromSpec_mem_basicOpen_iff hX₀ (hX₀.primeIdealOf ⟨x, hx⟩) a
  rwa [hX₀.fromSpec_primeIdealOf] at this

/-- Specialization of points of `Spec Γ(X, X₀)` in `X` is inclusion of primes. -/
theorem fromSpec_specializes_iff {X : Scheme.{u}} {X₀ : X.Opens} (hX₀ : IsAffineOpen X₀)
    (Q Q' : Spec Γ(X, X₀)) : hX₀.fromSpec Q ⤳ hX₀.fromSpec Q' ↔ Q.asIdeal ≤ Q'.asIdeal := by
  rw [hX₀.fromSpec.isOpenEmbedding.isInducing.specializes_iff]
  exact (PrimeSpectrum.le_iff_specializes Q Q').symm

/-- A point of `Spec Γ(X, X₀)` lies on a subvariety `Z` whose generic point is in `X₀` exactly when
its prime contains the prime of `Z`. -/
theorem fromSpec_mem_support_iff {X : Scheme.{u}} {X₀ : X.Opens} (hX₀ : IsAffineOpen X₀)
    {Z : Intersection.Scheme.Subvariety X} (hη : Z.genericPoint ∈ X₀) (Q : Spec Γ(X, X₀)) :
    hX₀.fromSpec Q ∈ (Z.support : Set X) ↔ (hX₀.primeIdealOf ⟨_, hη⟩).asIdeal ≤ Q.asIdeal := by
  have hP : hX₀.fromSpec (hX₀.primeIdealOf ⟨_, hη⟩) = Z.genericPoint :=
    hX₀.fromSpec_primeIdealOf _
  have := fromSpec_specializes_iff hX₀ (hX₀.primeIdealOf ⟨_, hη⟩) Q
  rwa [hP, specializes_iff_mem_closure, Z.closure_genericPoint] at this

/-- The prime of the generic point of a subvariety `Z`, with `Z ∩ X₀` an irreducible component of
`V(h) = X₀ - D(h)`, is a minimal prime over `h`. -/
theorem primeIdealOf_mem_minimalPrimes {X : Scheme.{u}} {X₀ : X.Opens} (hX₀ : IsAffineOpen X₀)
    {h : Γ(X, X₀)} {Z : Intersection.Scheme.Subvariety X}
    (hZ : Maximal (fun T : Set X ↦ IsIrreducible T ∧ T ⊆ (X₀ : Set X) \ X.basicOpen h)
      ((Z.support : Set X) ∩ X₀))
    (hη : Z.genericPoint ∈ X₀) :
    (hX₀.primeIdealOf ⟨_, hη⟩).asIdeal ∈ (Ideal.span {h}).minimalPrimes := by
  have hZmem := fromSpec_mem_support_iff hX₀ hη
  have hhP : h ∈ (hX₀.primeIdealOf ⟨_, hη⟩).asIdeal := not_not.1 <|
    (mem_basicOpen_iff_notMem_primeIdealOf hX₀ hη h).not.1
      (hZ.prop.2 ⟨Z.isGenericPoint_genericPoint.mem, hη⟩).2
  set P := hX₀.primeIdealOf ⟨_, hη⟩
  refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hhP⟩, fun q ⟨hq, hhq⟩ hqP ↦ ?_⟩
  let Q : Spec Γ(X, X₀) := ⟨q, hq⟩
  have hcl : {Q' : Spec Γ(X, X₀) | Q.asIdeal ≤ Q'.asIdeal} = closure {Q} := by
    ext Q'
    rw [Set.mem_ofPred_eq, ← specializes_iff_mem_closure]
    exact PrimeSpectrum.le_iff_specializes Q Q'
  have hTirr : IsIrreducible (hX₀.fromSpec '' {Q' : Spec Γ(X, X₀) | Q.asIdeal ≤ Q'.asIdeal}) := by
    rw [hcl]
    exact isIrreducible_singleton.closure.image _ hX₀.fromSpec.continuous.continuousOn
  have hTsub : hX₀.fromSpec '' {Q' : Spec Γ(X, X₀) | Q.asIdeal ≤ Q'.asIdeal} ⊆
      (X₀ : Set X) \ X.basicOpen h := by
    rintro _ ⟨Q', hQQ', rfl⟩
    refine ⟨hX₀.range_fromSpec.le ⟨Q', rfl⟩, ?_⟩
    rw [SetLike.mem_coe, fromSpec_mem_basicOpen_iff, not_not]
    exact hQQ' (hhq (Ideal.mem_span_singleton_self h))
  have hZT : (Z.support : Set X) ∩ X₀ ⊆
      hX₀.fromSpec '' {Q' : Spec Γ(X, X₀) | Q.asIdeal ≤ Q'.asIdeal} := by
    rintro x ⟨hxZ, hxX₀⟩
    obtain ⟨Q', rfl⟩ := hX₀.range_fromSpec.ge hxX₀
    exact ⟨Q', hqP.trans ((hZmem Q').1 hxZ), rfl⟩
  exact (hZmem Q).1 (hZ.2 ⟨hTirr, hTsub⟩ hZT ⟨Q, show Q.asIdeal ≤ Q.asIdeal from le_rfl, rfl⟩).1

/-- If `π` vanishes on `Z` and `s P ⊆ (π)` for the prime `P` of `Z`, every zero of `π` in `D(s)`
lies on `Z`. -/
theorem mem_support_of_notMem_basicOpen {X : Scheme.{u}} {X₀ : X.Opens} (hX₀ : IsAffineOpen X₀)
    {Z : Intersection.Scheme.Subvariety X} (hη : Z.genericPoint ∈ X₀) {π s : Γ(X, X₀)}
    (hs : ∀ a ∈ (hX₀.primeIdealOf ⟨_, hη⟩).asIdeal, s * a ∈ Ideal.span {π}) {x : X}
    (hxs : x ∈ X.basicOpen s) (hxπ : x ∉ X.basicOpen π) : x ∈ (Z.support : Set X) := by
  obtain ⟨Q, rfl⟩ := hX₀.range_fromSpec.ge (X.basicOpen_le s hxs)
  rw [fromSpec_mem_basicOpen_iff] at hxs
  rw [fromSpec_mem_basicOpen_iff, not_not] at hxπ
  refine (fromSpec_mem_support_iff hX₀ hη Q).2 fun a ha ↦ ?_
  exact (Q.isPrime.mem_or_mem ((Ideal.span_singleton_le_iff_mem _).2 hxπ (hs a ha))).resolve_left
    hxs

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- On a scheme locally of finite type over `K`, regularity of `𝒪_{X,ξ}/(π)` at a zero `ξ` of `π`
spreads to the zeros of `π` in a basic open neighbourhood of `ξ` (Stacks, Tag 07R5). -/
theorem exists_basicOpen_isRegularLocalRing_quotient [LocallyOfFiniteType (X ↘ Spec (.of K))]
    {X₀ : X.Opens} (hX₀ : IsAffineOpen X₀) (π : Γ(X, X₀)) {ξ : X} (hξ : ξ ∈ X₀)
    (hπ : π ∈ (hX₀.primeIdealOf ⟨ξ, hξ⟩).asIdeal)
    (hreg : IsRegularLocalRing (X.presheaf.stalk ξ ⧸ Ideal.span {X.presheaf.germ X₀ ξ hξ π})) :
    ∃ s : Γ(X, X₀), ξ ∈ X.basicOpen s ∧ ∀ (x : X) (hx : x ∈ X₀), x ∈ X.basicOpen s →
      x ∉ X.basicOpen π →
        IsRegularLocalRing (X.presheaf.stalk x ⧸ Ideal.span {X.presheaf.germ X₀ x hx π}) := by
  let : Algebra K Γ(X, X₀) :=
    (((X ↘ Spec (.of K)).appLE ⊤ X₀ (le_top.trans (Scheme.Hom.preimage_top _).ge)).hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  have : Algebra.FiniteType K Γ(X, X₀) := by
    refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _ ?_)
    · exact HasRingHomProperty.appLE @LocallyOfFiniteType (X ↘ Spec (.of K)) inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨X₀, hX₀⟩ _
    · exact (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective
  have hJ1 : IsJ1 (Γ(X, X₀) ⧸ Ideal.span {π}) :=
    (isJ2_of_standard_classes_and_finiteType.{u, u}).1 K _
  let : Algebra Γ(X, X₀) (X.presheaf.stalk ξ) := (X.presheaf.germ X₀ ξ hξ).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk ξ) (hX₀.primeIdealOf ⟨ξ, hξ⟩).asIdeal :=
    hX₀.isLocalization_stalk ⟨ξ, hξ⟩
  obtain ⟨s, hs, hsreg⟩ :=
    Stacks.NormalCrossingsChart.exists_notMem_forall_isRegularLocalRing_quotient_of_isJ1 π hJ1 _
      hπ (X.presheaf.stalk ξ) hreg
  refine ⟨s, (mem_basicOpen_iff_notMem_primeIdealOf hX₀ hξ s).2 hs, fun x hx hxs hxπ ↦ ?_⟩
  obtain ⟨Q, rfl⟩ := hX₀.range_fromSpec.ge hx
  have : Q.asIdeal.IsPrime := Q.isPrime
  rw [fromSpec_mem_basicOpen_iff] at hxs
  rw [fromSpec_mem_basicOpen_iff, not_not] at hxπ
  let : Algebra Γ(X, X₀) (X.presheaf.stalk (hX₀.fromSpec Q)) :=
    (X.presheaf.germ X₀ _ hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk (hX₀.fromSpec Q)) Q.asIdeal :=
    hX₀.isLocalization_stalk' Q hx
  exact hsreg Q hxs hxπ _

/-- **Shrinking to `D(s)`.** Given a uniformizer `π` at the generic point of `Z`, with
`t h = u πᵐ`, `s₁ P ⊆ (π)` and `𝒪_{X,Z}/(π)` regular, there is a basic open `D(s)` around the
generic point of `Z` on which the conclusions of `exists_uniformizer_of_maximal` hold. -/
theorem exists_basicOpen_of_uniformizer [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))] {X₀ : X.Opens} (hX₀ : IsAffineOpen X₀) {h : Γ(X, X₀)}
    {Z : Intersection.Scheme.Subvariety X}
    (hZ : Maximal (fun T : Set X ↦ IsIrreducible T ∧ T ⊆ (X₀ : Set X) \ X.basicOpen h)
      ((Z.support : Set X) ∩ X₀))
    (hη : Z.genericPoint ∈ X₀) (hηreg : Z.genericPoint ∈ regularLocus X)
    {π s₁ t u : Γ(X, X₀)} {m : ℕ} (hm : 0 < m) (htu : t * h = u * π ^ m)
    (hs₁ : s₁ ∉ (hX₀.primeIdealOf ⟨_, hη⟩).asIdeal)
    (hs₁P : ∀ a ∈ (hX₀.primeIdealOf ⟨_, hη⟩).asIdeal, s₁ * a ∈ Ideal.span {π})
    (ht : t ∉ (hX₀.primeIdealOf ⟨_, hη⟩).asIdeal) (hu : u ∉ (hX₀.primeIdealOf ⟨_, hη⟩).asIdeal)
    (hπ : π ∈ (hX₀.primeIdealOf ⟨_, hη⟩).asIdeal)
    (hreg : IsRegularLocalRing
      (X.presheaf.stalk Z.genericPoint ⧸ Ideal.span {X.presheaf.germ X₀ _ hη π})) :
    ∃ s : Γ(X, X₀),
      Z.genericPoint ∈ X.basicOpen s ∧ Z.genericPoint ∉ X.basicOpen π ∧
      X.basicOpen s ≤ X.basicOpen t ⊓ X.basicOpen u ∧
      (∀ x ∈ X.basicOpen s, x ∈ regularLocus X) ∧
      (∀ x ∈ X.basicOpen s, x ∉ X.basicOpen π →
        x ∈ (Z.support : Set X) ∧ (∃ z ∈ regularLocus Z.toScheme, Z.ι z = x) ∧
        ∀ T : Set X,
          Maximal (fun T : Set X ↦ IsIrreducible T ∧ T ⊆ (X₀ : Set X) \ X.basicOpen h) T →
          T ≠ (Z.support : Set X) ∩ X₀ → x ∉ T) ∧
      ∀ (x : X) (hx : x ∈ X.basicOpen s), x ∉ X.basicOpen π →
        IsRegularLocalRing (X.presheaf.stalk x ⧸
          Ideal.span {X.presheaf.germ X₀ x (X.basicOpen_le s hx) π}) := by
  have hbo := mem_basicOpen_iff_notMem_primeIdealOf hX₀ hη
  have hZsing : IsClosed (Z.ι '' singularLocus Z.toScheme) :=
    Z.ι.isClosedEmbedding.isClosedMap _ (isClosed_singularLocus_of_isAlgebraicScheme K Z.toScheme)
  have hηsing : Z.genericPoint ∉ Z.ι '' singularLocus Z.toScheme := by
    rintro ⟨z, hz, hzη⟩
    have : z = genericPoint Z.toScheme := Z.ι.isClosedEmbedding.injective hzη
    exact hz (this ▸ genericPoint_mem_regularLocus Z.toScheme)
  obtain ⟨s₂, hs₂le, hηs₂⟩ := hX₀.exists_basicOpen_le
    (V := X₀ ⊓ ⟨regularLocus X, isOpen_regularLocus_of_isAlgebraicScheme K X⟩ ⊓
      ⟨_, hZsing.isOpen_compl⟩) ⟨Z.genericPoint, ⟨hη, hηreg⟩, hηsing⟩ hη
  obtain ⟨s₄, hηs₄, hs₄⟩ := exists_basicOpen_isRegularLocalRing_quotient K hX₀ π hη hπ hreg
  set s := s₁ * s₂ * s₄ * t * u with hs
  have hsmem : ∀ x : X, x ∈ X.basicOpen s ↔ x ∈ X.basicOpen s₁ ∧ x ∈ X.basicOpen s₂ ∧
      x ∈ X.basicOpen s₄ ∧ x ∈ X.basicOpen t ∧ x ∈ X.basicOpen u := fun x ↦ by
    simp only [hs, Scheme.basicOpen_mul, TopologicalSpace.Opens.mem_inf, and_assoc]
  have hπZ : ∀ x ∈ X.basicOpen s, x ∉ X.basicOpen π → x ∈ (Z.support : Set X) := fun x hx ↦
    mem_support_of_notMem_basicOpen hX₀ hη hs₁P ((hsmem x).1 hx).1
  have hhπ : ∀ x ∈ X.basicOpen u, x ∉ X.basicOpen h → x ∉ X.basicOpen π := by
    intro x hxu hxh hxπ
    have hx : x ∈ X.basicOpen (t * h) := by
      rw [htu, Scheme.basicOpen_mul, Scheme.basicOpen_pow _ _ hm]
      exact ⟨hxu, hxπ⟩
    rw [Scheme.basicOpen_mul] at hx
    exact hxh hx.2
  refine ⟨s, (hsmem _).2 ⟨(hbo s₁).2 hs₁, hηs₂, hηs₄, (hbo t).2 ht, (hbo u).2 hu⟩,
    fun hηπ ↦ (hbo π).1 hηπ hπ, fun x hx ↦ ⟨((hsmem x).1 hx).2.2.2.1, ((hsmem x).1 hx).2.2.2.2⟩,
    fun x hx ↦ (hs₂le ((hsmem x).1 hx).2.1).1.2,
    fun x hx hxπ ↦ ⟨hπZ x hx hxπ, ?_, fun T hT hTne hxT ↦ hTne ?_⟩,
    fun x hx hxπ ↦ hs₄ x _ ((hsmem x).1 hx).2.2.1 hxπ⟩
  · obtain ⟨z, rfl⟩ : x ∈ Set.range Z.ι := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact hπZ x hx hxπ
    refine ⟨z, ?_, rfl⟩
    by_contra hz
    exact (hs₂le ((hsmem _).1 hx).2.1).2 ⟨z, hz, rfl⟩
  · exact eq_of_maximal_of_inter_subset Set.sdiff_subset Z.isClosed_support (X.basicOpen s).isOpen
      hZ hT ⟨x, hxT, hx⟩ fun y ⟨hyT, hys⟩ ↦
        hπZ y hys (hhπ y ((hsmem y).1 hys).2.2.2.2 (hT.prop.2 hyT).2)

/-- **A uniformizer along a component of `V(h)`, spread out.** Let `X` be a normal variety over
`K`, `X₀` a non-empty affine open, `h ∈ Γ(X, X₀)` non-zero and `Z` a subvariety with `Z ∩ X₀` an
irreducible component of `V(h) = X₀ - D(h)`, and `r` the rational function `h`. There are
`s, π, t, u ∈ Γ(X, X₀)` and `m = ord_Z(h) ≥ 1` with `t h = u πᵐ`, the generic point of `Z` in
`D(s) ⊆ D(t) ∩ D(u)`, `π` vanishing at the generic point of `Z`, and, for `x ∈ D(s)`: `x` is a
regular point of `X`, and if `π(x) = 0` then
`x ∈ Z`, `x` lies over a regular point of `Z`, `x` lies on no other component of `V(h)`, and
`𝒪_{X,x}/(π)` is a regular local ring. -/
theorem exists_uniformizer_of_maximal [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))] [IsNormal X] {X₀ : X.Opens}
    (hX₀ : IsAffineOpen X₀) [Nonempty X₀] {h : Γ(X, X₀)} (hh : h ≠ 0)
    {Z : MMP.Intersection.Scheme.Subvariety X}
    (hZ : Maximal (fun T : Set X ↦ IsIrreducible T ∧ T ⊆ (X₀ : Set X) \ X.basicOpen h)
      ((Z.support : Set X) ∩ X₀))
    {r : X.functionFieldˣ}
    (hr : (r : X.functionField) = X.germToFunctionField X₀ h) :
    ∃ (s π t u : Γ(X, X₀)) (m : ℕ),
      haveI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K));
      (m : ℤ) = X.ord (r : X.functionField) Z.genericPoint ∧
      Order.coheight Z.genericPoint = 1 ∧
      0 < m ∧ t * h = u * π ^ m ∧ π ≠ 0 ∧
      Z.genericPoint ∈ X.basicOpen s ∧ Z.genericPoint ∉ X.basicOpen π ∧
      X.basicOpen s ≤ X.basicOpen t ⊓ X.basicOpen u ∧
      (∀ x ∈ X.basicOpen s, x ∈ regularLocus X) ∧
      (∀ x ∈ X.basicOpen s, x ∉ X.basicOpen π →
        x ∈ (Z.support : Set X) ∧ (∃ z ∈ regularLocus Z.toScheme, Z.ι z = x) ∧
        ∀ T : Set X,
          Maximal (fun T : Set X ↦ IsIrreducible T ∧ T ⊆ (X₀ : Set X) \ X.basicOpen h) T →
          T ≠ (Z.support : Set X) ∩ X₀ → x ∉ T) ∧
      ∀ (x : X) (hx : x ∈ X.basicOpen s), x ∉ X.basicOpen π →
        IsRegularLocalRing (X.presheaf.stalk x ⧸
          Ideal.span {X.presheaf.germ X₀ x (X.basicOpen_le s hx) π}) := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have : IsDomain Γ(X, X₀) := IsIntegral.component_integral X₀
  have : IsNoetherianRing Γ(X, X₀) := IsLocallyNoetherian.component_noetherian ⟨X₀, hX₀⟩
  set η := Z.genericPoint
  have hηX₀ : η ∈ X₀ :=
    (Z.isGenericPoint_genericPoint.mem_open_set_iff X₀.isOpen).2 hZ.prop.1.nonempty
  set P : Spec Γ(X, X₀) := hX₀.primeIdealOf ⟨η, hηX₀⟩
  have hPmin : P.asIdeal ∈ (Ideal.span {h}).minimalPrimes :=
    primeIdealOf_mem_minimalPrimes hX₀ hZ hηX₀
  have hhP : h ∈ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).1 hPmin.1.2
  let : Algebra Γ(X, X₀) (X.presheaf.stalk η) := (X.presheaf.germ X₀ η hηX₀).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk η) P.asIdeal :=
    hX₀.isLocalization_stalk ⟨η, hηX₀⟩
  have hdim := ringKrullDim_eq_one_of_mem_minimalPrimes (X.presheaf.stalk η) P.asIdeal hh hPmin
  have : IsNoetherianRing (X.presheaf.stalk η) :=
    IsLocalization.isNoetherianRing P.asIdeal.primeCompl _ inferInstance
  have : IsIntegrallyClosed (X.presheaf.stalk η) := IsNormal.stalk_normal η
  have := isDiscreteValuationRing_of_ringKrullDim_eq_one hdim
  obtain ⟨π, hπ⟩ := exists_irreducible_algebraMap (X.presheaf.stalk η) P.asIdeal
  obtain ⟨m, v, t, u, hm, hv, ht, hu, htu⟩ :=
    exists_mul_eq_mul_pow (X.presheaf.stalk η) P.asIdeal hπ hh hhP
  have hco : Order.coheight η = 1 := by
    exact_mod_cast (ringKrullDim_stalk_eq_coheight η).symm.trans hdim
  have hord : (m : ℤ) = X.ord (r : X.functionField) η := by
    have hnzd : algebraMap Γ(X, X₀) (X.presheaf.stalk η) π ∈ nonZeroDivisors _ :=
      mem_nonZeroDivisors_of_ne_zero hπ.ne_zero
    have hRing : Ring.ord (X.presheaf.stalk η) ((X.presheaf.germ X₀ η hηX₀).hom h) = m := by
      change Ring.ord _ (algebraMap Γ(X, X₀) (X.presheaf.stalk η) h) = m
      rw [hv, Ring.ord_mul _ (pow_mem hnzd m), Ring.ord_of_isUnit v.isUnit, Ring.ord_pow hnzd,
        Ring.ord_of_irreducible hπ]
      simp
    rw [hr]
    exact (Stacks.Chow.ord_eq_ringOrd_germ hco hηX₀ h hh hRing).symm
  obtain ⟨s₁, hs₁, hs₁P⟩ := exists_mul_mem_span_singleton (X.presheaf.stalk η) P.asIdeal hπ
  have hηreg : η ∈ regularLocus X := by
    change IsRegularLocalRing (X.presheaf.stalk η)
    refine (MMP.isRegularLocalRing_iff_exists_span_eq_maximalIdeal _).2
      ⟨1, ![algebraMap Γ(X, X₀) _ π], ?_, ?_⟩
    · rw [hdim]
      rfl
    · rw [Set.range_unique, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ]
      rfl
  have hπP : π ∈ P.asIdeal := (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P.asIdeal π).1
    ((mem_maximalIdeal _).2 hπ.not_isUnit)
  obtain ⟨s, hs⟩ :=
    exists_basicOpen_of_uniformizer K hX₀ hZ hηX₀ hηreg hm htu hs₁ hs₁P ht hu hπP
      (isRegularLocalRing_quotient_of_irreducible hπ)
  exact ⟨s, π, t, u, m, hord, hco, hm, htu, fun h0 ↦ hπ.ne_zero (by rw [h0, map_zero]), hs⟩

end LocalNormalForm

end MMP
