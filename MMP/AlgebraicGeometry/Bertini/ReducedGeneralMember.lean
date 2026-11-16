module

public import MMP.Attr
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneIsProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibre.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniUniversalFamilyChart
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniInvertibleChart
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGeneratingSystem
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniChartFunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniRationalMember
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeUnits

/-!
# Reducedness of general members of free linear systems in characteristic zero

Let `k` be an algebraically closed field of characteristic zero, `X` a scheme of finite type over
`k`, `L` an invertible sheaf on `X` and `V ⊆ H⁰(X, L)` a finite-dimensional subspace generating
`L`. A section `s = ∑ᵢ cᵢ sᵢ ∈ V` is a point of `V`, and, if `s ≠ 0`, it gives a point `[s]` of
the projective space `ℙ(V)` of lines of `V`; its zero scheme `Z(s) ⊆ X` depends only on `[s]`.
This file sets up the parameter spaces of the Bertini theorems for such systems (normality,
reducedness and irreducibility of general members, and the dimension of general linear sections
of constructible sets) and proves the reducedness theorem: if `X` is reduced, `Z(s)` is reduced
for `s` in one dense open of `V`, and for `[s]` in one dense open of `ℙ(V)`.

## Main definitions

* Projective space `ℙᴺ_k` is the Stacks/Mathlib term
  `Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) = Proj k[T₀, …, T_N]`; with the
  coefficients of a linear form as homogeneous coordinates it is also the dual space of
  hyperplanes.
* `MMP.Threefold.Bridges.linearForm`: the linear form `∑ᵢ cᵢ Tᵢ` of a coefficient vector.
* `MMP.Threefold.Bridges.dualPoint`: the point `[c] ∈ (ℙᴺ_k)^∨` of a nonzero coefficient vector.
* `MMP.Threefold.Bridges.hyperplaneSection`: the ideal sheaf of `φ⁻¹(H)` for `φ : Z → ℙᴺ_k`.
* `MMP.Threefold.Bridges.coefficientSpace`: the affine space `𝔸ᴺ⁺¹_k` of coefficient vectors,
  and `MMP.Threefold.Bridges.coefficientPoint` its `k`-point with given coordinates.
* `MMP.Threefold.Bridges.systemSection`: the section `∑ᵢ cᵢ sᵢ` of a system `s₀, …, s_N`.

## Main results

* `MMP.Threefold.Bridges.exists_dense_open_isReduced_zeroScheme`: general members of a free
  system on a reduced scheme of finite type are reduced.

## Implementation notes

The system `V` is presented by sections `s₀, …, s_N` spanning it, and a section of `V` by its
coefficient vector `c ∈ kᴺ⁺¹`: the section is `∑ᵢ cᵢ sᵢ`. "A dense open of `V`" is a dense open
of the affine space `𝔸ᴺ⁺¹_k = Spec k[a₀, …, a_N]` of coefficient vectors, and "a dense open of
`ℙ(V)`" a dense open of `ℙᴺ_k = Proj k[T₀, …, T_N]`, the coefficient vector `c ≠ 0` giving the
point `[c]` whose homogeneous prime consists of the forms vanishing at `c`. When `s` is a basis of
`V` these are `V` and `ℙ(V)` themselves. The sections are not required to be linearly
independent: the statements for a spanning family are the statements for `V`, since a linear
surjection `kᴺ⁺¹ → V` is open and pulls dense opens back to dense opens; allowing a spanning
family also covers `V = 0`. A section lies in the general open when its coefficient vector is a
`k`-rational point of it, as `k` is algebraically closed.

`V` generates `L` when every point of `X` lies in the non-vanishing locus of some section of `V`.
The morphism `φ : X → ℙ(V^*) = Proj (Sym (kᴺ⁺¹))` of the system is
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections`, and
the dimension of its image is the Krull dimension of `φ(X)` as a subspace of `ℙ(V^*)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 3.39
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Threefold.Bridges

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Hyperplanes of projective space -/

section Hyperplanes

variable {k : Type u} [Field k] {N : ℕ}

/-- The linear form `∑ᵢ cᵢ Tᵢ`, a homogeneous polynomial of degree one, of a coefficient vector
`c ∈ kᴺ⁺¹`. -/
def linearForm (c : Fin (N + 1) → k) : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1 :=
  ∑ i, c i • ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩

/-- The point `[c₀ : ⋯ : c_N]` of the dual projective space `(ℙᴺ_k)^∨` attached to a nonzero
coefficient vector, that is, to the hyperplane `V(∑ᵢ cᵢ Tᵢ)`: its homogeneous prime is the
ideal of the polynomials all of whose homogeneous components vanish at `c`, the homogeneous core
of the kernel of evaluation at `c`. -/
def dualPoint (c : Fin (N + 1) → k) (hc : c ≠ 0) :
    AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) :=
  show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) from
  { asHomogeneousIdeal := (RingHom.ker (MvPolynomial.eval c)).homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
    isPrime := (RingHom.ker_isPrime _).homogeneousCore
    not_irrelevant_le := by
      intro h
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra h'
        exact hc (funext fun i => not_not.mp fun hi => h' ⟨i, hi⟩)
      have hX : MvPolynomial.X i ∈ HomogeneousIdeal.irrelevant
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) := by
        rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
          DirectSum.decompose_of_mem_ne _ (MvPolynomial.isHomogeneous_X k i) one_ne_zero]
      have h2 := Ideal.toIdeal_homogeneousCore_le _ _ (h hX)
      simp only [RingHom.mem_ker, MvPolynomial.eval_X] at h2
      exact hi h2 }

/-- A homogeneous polynomial lies in the prime of `[c₀ : ⋯ : c_N]` iff it vanishes at `c`. -/
theorem mem_dualPoint_iff (c : Fin (N + 1) → k) (hc : c ≠ 0)
    {φ : MvPolynomial (Fin (N + 1)) k} {d : ℕ} (hφ : φ.IsHomogeneous d) :
    φ ∈ (dualPoint c hc).asHomogeneousIdeal ↔ MvPolynomial.eval c φ = 0 :=
  ⟨fun h => RingHom.mem_ker.mp (Ideal.toIdeal_homogeneousCore_le _ _ h),
    fun h => Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hφ⟩ (RingHom.mem_ker.mpr h)⟩

variable {Z : Scheme.{u}}
  (φ : Z ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))

/-- The ideal sheaf of `Z_H = φ⁻¹(H)` in `Z`, for the hyperplane `H = V(∑ᵢ cᵢ Tᵢ) ⊆ ℙᴺ_k`: the
scheme-theoretic inverse image along `φ` of the zero scheme of the section `∑ᵢ cᵢ Tᵢ` of
`𝒪(1)`. -/
def hyperplaneSection (c : Fin (N + 1) → k) : Z.IdealSheafData :=
  (Stacks.ProjectiveSpace.hyperplane (linearForm c)).comap φ

end Hyperplanes

/-! ### The affine space of coefficient vectors and the sections of a system -/

section System

variable (k : Type u) [Field k] (N : ℕ)

/-- The affine space `𝔸ᴺ⁺¹_k = Spec k[a₀, …, a_N]` of coefficient vectors `c ∈ kᴺ⁺¹`; for a
system of sections `s₀, …, s_N` it parametrises the sections `∑ᵢ cᵢ sᵢ`. -/
abbrev coefficientSpace : Scheme.{u} :=
  Spec (.of (MvPolynomial (Fin (N + 1)) k))

variable {k N}

/-- The `k`-rational point of `𝔸ᴺ⁺¹_k` with coordinates `c`: the maximal ideal of the polynomials
vanishing at `c`. -/
def coefficientPoint (c : Fin (N + 1) → k) : coefficientSpace k N :=
  ⟨RingHom.ker (MvPolynomial.eval c), RingHom.ker_isPrime _⟩

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)

attribute [local instance] globalSectionsModule

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] {L : X.Modules}

/-- The section `∑ᵢ cᵢ sᵢ` of `L` of the system spanned by `s₀, …, s_N`, as a `k`-linear map of
the coefficient vector `c`. -/
def systemSection (s : Fin (N + 1) → Γ(L, ⊤)) : (Fin (N + 1) → k) →ₗ[k] Γ(L, ⊤) :=
  Fintype.linearCombination k s

/-- `systemSection s c = ∑ᵢ cᵢ sᵢ`. -/
theorem systemSection_apply (s : Fin (N + 1) → Γ(L, ⊤)) (c : Fin (N + 1) → k) :
    systemSection s c = ∑ i, c i • s i := by
  simp [systemSection, Fintype.linearCombination_apply]

end System

/-! ### Reducedness of the universal divisor and of its general fibres -/

section ReducedHelpers

open Stacks.Bertini Stacks.Bertini.FamilyDivisors MvPolynomial

/-- **Eliminating a variable with a unit coefficient keeps a reduced ring reduced.** If `A` is
reduced and some `f i₀` is a unit, then `A[xᵢ]/(∑ᵢ fᵢ xᵢ)` is reduced: it is a polynomial ring
over `A` in the remaining variables. -/
theorem isReduced_quotient_span_sum_C_mul_X {A σ : Type*} [CommRing A] [_root_.IsReduced A]
    [Fintype σ] [DecidableEq σ] (f : σ → A) (i₀ : σ) (hu : IsUnit (f i₀)) :
    _root_.IsReduced (MvPolynomial σ A ⧸ Ideal.span {∑ j, C (f j) * X j}) := by
  haveI : Nonempty σ := ⟨i₀⟩
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card σ = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e₀ : σ ≃ Fin (n + 1) := (Fintype.equivFin σ).trans (finCongr hn)
  let e : σ ≃ Fin (n + 1) := e₀.trans (Equiv.swap (e₀ i₀) 0)
  have he : e i₀ = 0 := by simp [e]
  let g : Fin (n + 1) → A := fun i => f (e.symm i)
  have hg0 : g 0 = f i₀ := by simp [g, ← he]
  obtain ⟨w, hw⟩ : ∃ w, w * g 0 = 1 := by
    obtain ⟨v, hv⟩ := hu
    exact ⟨(v⁻¹ : Aˣ), by
      rw [hg0, ← hv]
      simp⟩
  have hmap : Ideal.span {Algebra.universalLinearForm g} =
      Ideal.map (renameEquiv A e : MvPolynomial σ A →+* MvPolynomial (Fin (n + 1)) A)
      (Ideal.span {∑ j, C (f j) * X j}) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp only [RingHom.coe_coe, renameEquiv_apply, map_sum, map_mul, rename_C, rename_X,
      Algebra.universalLinearForm, g]
    exact (Fintype.sum_equiv e _ _ (fun j => by simp)).symm
  let φ := (Ideal.quotientEquivAlg _ _ (renameEquiv A e) hmap).trans
    (Algebra.quotientSpanUniversalLinearFormEquiv g hw)
  exact isReduced_of_injective (φ : _ →+* MvPolynomial (Fin n) A) φ.injective

/-- A scheme is reduced as soon as every point has a reduced open neighbourhood. -/
theorem isReduced_of_forall_exists_opens {Y : Scheme.{u}}
    (h : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ IsReduced W.toScheme) : IsReduced Y := by
  choose W hxW hW using h
  have hcov : ⨆ y, W y = ⊤ :=
    eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxW y⟩
  haveI : ∀ i, IsReduced ((Y.openCoverOfIsOpenCover W hcov).X i) := hW
  exact IsReduced.of_openCover (X := Y) (Y.openCoverOfIsOpenCover W hcov)

variable {D : FamilyDivisors.{u, u}}

/-- **The universal divisor over a chart on which a basis section is invertible is reduced**,
when `X` is: its ring `A[xⱼ]/(∑ⱼ xⱼ fⱼ)` is a polynomial ring over the reduced ring `A`. -/
theorem isReduced_chartDivisorOpen [IsReduced D.X] (c : D.Chart)
    {i₀ : Fin (Module.finrank D.k D.V)} (hu : IsUnit (D.chartEquation c.triv i₀)) :
    IsReduced (D.chartDivisorOpen c.U).toScheme := by
  classical
  haveI : _root_.IsReduced (MvPolynomial D.basisIndex Γ(c.U.toScheme, ⊤) ⧸
      Ideal.span {∑ j, MvPolynomial.C (D.chartEquationIndex c.U c.triv j) * MvPolynomial.X j}) :=
    isReduced_quotient_span_sum_C_mul_X _ (ULift.up i₀) hu
  haveI : _root_.IsReduced Γ(D.universalDivisorScheme, D.chartDivisorOpen c.U) :=
    isReduced_of_injective (D.chartSubschemeΓEquiv c.U c.triv).toRingHom
      (D.chartSubschemeΓEquiv c.U c.triv).injective
  haveI : _root_.IsReduced Γ((D.chartDivisorOpen c.U).toScheme, ⊤) :=
    isReduced_of_injective ((D.chartDivisorOpen c.U).topIso.hom.hom)
      (D.chartDivisorOpen c.U).topIso.commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isAffine_isReduced _

/-- **The universal divisor of a generating system on a reduced scheme is reduced.** Over a
trivializing chart on which some basis section vanishes nowhere, the universal linear form can be
solved for one variable. -/
theorem isReduced_universalDivisorScheme [IsReduced D.X]
    (hgen : ∀ x : D.X, ∃ i, x ∈ Stacks.NonvanishingOpen.nonvanishingOpen D.X D.L
      (D.sectionOf (D.basis i))) :
    IsReduced D.universalDivisorScheme := by
  refine isReduced_of_forall_exists_opens fun z => ?_
  obtain ⟨i, hi⟩ := hgen (D.parameterProjection (D.universalDivisor.subschemeι z))
  obtain ⟨c, hcU, hxc⟩ := D.exists_chart_le
    (Stacks.NonvanishingOpen.nonvanishingOpen D.X D.L (D.sectionOf (D.basis i))) _ hi
  have hu : IsUnit (D.chartEquation c.triv i) :=
    isUnit_chartFunction_of_subset_compl_divisorSet c.triv (D.basis i)
      fun y hy => D.notMem_divisorSet_of_mem_nonvanishingOpen (D.basis i) (hcU hy)
  refine ⟨D.chartDivisorOpen c.U, ?_, isReduced_chartDivisorOpen c hu⟩
  show D.universalDivisor.subschemeι z ∈ ((D.chartOpen c.U).1 : Set D.parameterSpace)
  rw [chartOpen_coe]
  exact hxc

/-- **Stacks 0578 for the universal family.** In characteristic zero, if `X` is of finite type
over `k` and the universal divisor is reduced, then the universal family `H_univ → 𝔸^r_k` has
geometrically reduced fibres over a nonempty open of `𝔸^r_k`: its generic fibre is reduced, hence
geometrically reduced over the perfect field `κ(η)`. -/
theorem exists_opens_geometricallyReduced_universalFamily [CharZero D.k]
    [LocallyOfFiniteType D.toBase] [QuasiCompact D.toBase] [IsReduced D.universalDivisorScheme] :
    ∃ V : D.parameterBase.Opens, Nonempty V ∧ GeometricallyReduced (D.universalFamily ∣_ V) := by
  haveI := D.irreducibleSpace_parameterBase
  haveI := D.locallyOfFiniteType_universalFamily
  haveI := D.quasiCompact_universalFamily
  haveI : IsReduced (D.universalFamily.fiber (genericPoint D.parameterBase)) :=
    isReduced_fiber_genericPoint D.universalFamily
  let φ : D.k →+* D.parameterBase.residueField (genericPoint D.parameterBase) :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (D.parameterBase ↘ Spec (.of D.k)).appTop ≫
      D.parameterBase.evaluation ⊤ _ trivial).hom
  haveI : CharZero (IsLocalRing.ResidueField
      (D.parameterBase.presheaf.stalk (genericPoint D.parameterBase))) :=
    charZero_of_injective_ringHom φ.injective
  haveI : PerfectField (IsLocalRing.ResidueField
      (D.parameterBase.presheaf.stalk (genericPoint D.parameterBase))) :=
    PerfectField.ofCharZero
  haveI : GeometricallyReduced
      (D.universalFamily.fiberToSpecResidueField (genericPoint D.parameterBase)) :=
    geometricallyReduced_of_isReduced _
  exact exists_opens_nonempty_geometricallyReduced_morphismRestrict_of_finiteType
    D.universalFamily (genericPoint D.parameterBase) (genericPoint_spec _)

/-- **A `k`-point of a geometrically reduced open gives a reduced divisor.** The divisor `H_v`
of a `k`-point of `𝔸^r_k` is the fibre of the universal family over it, hence a base change of
the restriction of the universal family over any open containing the point. -/
theorem isReduced_specializedDivisor_of_mem {V : D.parameterBase.Opens}
    (hV : GeometricallyReduced (D.universalFamily ∣_ V)) (a : Fin (Module.finrank D.k D.V) → D.k)
    (ha : ∀ p : Spec (.of D.k), D.parameterPoint a p ∈ V) :
    IsReduced (D.specializedDivisor D.k a).subscheme := by
  obtain ⟨p, hup⟩ := D.exists_isPullback_universalFamily D.k a
  have hrange : Set.range (D.parameterPoint a).base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    exact ha q
  rw [← IsOpenImmersion.lift_fac V.ι (D.parameterPoint a) hrange] at hup
  exact hV.geometrically_isReduced _ _ _
    (IsPullback.of_right' hup (isPullback_morphismRestrict D.universalFamily V).flip)

/-- **`H_v` over `k` itself is the zero scheme of `ψ(v)`, for reducedness.** For a `k`-point the
base change `X_k` is `X` and `H_v` is the zero scheme of `ψ(∑ aᵢ vᵢ)` pulled back along this
isomorphism. -/
theorem isReduced_zeroScheme_of_isReduced_specializedDivisor
    (a : Fin (Module.finrank D.k D.V) → D.k)
    (h : IsReduced (D.specializedDivisor D.k a).subscheme) :
    IsReduced
      (Stacks.Divisors.zeroScheme D.X D.L (D.sectionOf (∑ i, a i • D.basis i))).subscheme := by
  set φ := Spec.map (CommRingCat.ofHom (algebraMap D.k D.k))
  have hφ : φ = 𝟙 _ := by
    simp only [φ]
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have : IsIso φ := by
    rw [hφ]
    infer_instance
  set e : D.baseChange D.k ⟶ D.X := D.baseChangeToX D.k
  have : IsIso e := by
    change IsIso (pullback.fst D.toBase φ)
    infer_instance
  have hscalar : ∀ c : D.k, D.baseChangeScalar D.k c = e.appTop (D.baseScalar c) := by
    intro c
    have hc : pullback.snd D.toBase φ = pullback.fst D.toBase φ ≫ D.toBase := by
      rw [pullback.condition, hφ, Category.comp_id]
    change (pullback.snd D.toBase φ).appTop ((Scheme.ΓSpecIso (.of D.k)).inv c) = _
    rw [hc, Scheme.Hom.comp_appTop]
    rfl
  set s := D.sectionOf (∑ i, a i • D.basis i)
  have hsec : D.specializedSection D.k a = pullbackGlobalSections e D.L s := by
    have hs : s = ∑ i, D.baseScalar (a i) • D.sectionOf (D.basis i) := by
      change D.ψ (∑ i, a i • D.basis i) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => D.sectionOf_smul _ _
    rw [specializedSection, hs, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul, hscalar]
  have hdiv : D.specializedDivisor D.k a = (Stacks.Divisors.zeroScheme D.X D.L s).comap e := by
    rw [specializedDivisor, hsec]
    exact Stacks.Divisors.zeroScheme_pullback e D.L s
  set I := Stacks.Divisors.zeroScheme D.X D.L s
  set m := Scheme.IdealSheafData.subschemeMap (I.comap e) I e (I.le_map_comap e)
  have : IsIso m := (Scheme.IdealSheafData.isPullback_comap I e).isIso_snd_of_isIso
  rw [hdiv] at h
  exact isReduced_of_isOpenImmersion (inv m)

/-- **A nonempty open of `𝔸^r_k` contains the non-vanishing locus of a nonzero polynomial**, read
on `k`-points: there is a nonzero polynomial `P` such that every coordinate tuple at which `P`
does not vanish gives a `k`-point of the open. -/
theorem exists_polynomial_parameterPoint_mem
    (U : (𝔸(D.basisIndex; Spec (.of D.k))).Opens) (hU : U.1.Nonempty) :
    ∃ P : MvPolynomial D.basisIndex D.k, P ≠ 0 ∧ ∀ a' : D.basisIndex → D.k, eval a' P ≠ 0 →
      ∀ p : Spec (.of D.k), D.parameterPoint (fun i => a' (ULift.up i)) p ∈ U := by
  classical
  obtain ⟨p₀, hp₀⟩ := hU
  obtain ⟨-, ⟨-, ⟨G, rfl⟩, rfl⟩, hp₀G, hGU⟩ :=
    (isBasis_basicOpen (𝔸(D.basisIndex; Spec (.of D.k)))).exists_subset_of_mem_open hp₀ U.isOpen
  have hG0 : G ≠ 0 := by
    rintro rfl
    simp at hp₀G
  set e := Scheme.ΓSpecIso (CommRingCat.of D.k)
  set P : MvPolynomial D.basisIndex D.k :=
    MvPolynomial.map e.hom.hom ((AffineSpace.ΓIso D.basisIndex (Spec (.of D.k))).hom G) with hP
  have hPG : (AffineSpace.ΓIso D.basisIndex (Spec (.of D.k))).inv (MvPolynomial.map e.inv.hom P) =
      G := by
    rw [hP, MvPolynomial.map_map]
    have : e.inv.hom.comp e.hom.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, e.hom_inv_id]
      rfl
    rw [this, MvPolynomial.map_id, ← CommRingCat.comp_apply, Iso.hom_inv_id]
    rfl
  have hP0 : P ≠ 0 := by
    intro h0
    apply hG0
    rw [← hPG, h0, map_zero, map_zero]
  refine ⟨P, hP0, fun a' ha' p => ?_⟩
  apply hGU
  have hval := AffineSpace.homOfVector_appTop_ΓIso_inv_map a' P
  rw [hPG] at hval
  rw [D.parameterPoint_self]
  change p ∈ _ ⁻¹ᵁ (𝔸(D.basisIndex; Spec (.of D.k))).basicOpen G
  rw [Scheme.preimage_basicOpen_top]
  have hfun : (fun q : D.basisIndex => e.inv (a' (ULift.up q.down))) =
      fun q => e.inv (a' q) := rfl
  rw [hfun, hval, Scheme.basicOpen_of_isUnit]
  · exact TopologicalSpace.Opens.mem_top p
  · exact IsUnit.map e.inv.hom (isUnit_iff_ne_zero.mpr ha')

end ReducedHelpers

/-! ### Scaling and density lemmas for coefficient vectors -/

section Coefficients

open MvPolynomial

/-- A homogeneous polynomial of degree `n` scales by `tⁿ`: `φ(t c) = tⁿ φ(c)`. -/
theorem eval_smul_of_isHomogeneous {σ R : Type*} [CommRing R] [Fintype σ]
    {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsHomogeneous n) (t : R) (c : σ → R) :
    eval (t • c) φ = t ^ n * eval c φ := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have := hφ (mem_support_iff.mp hd)
    rw [← this, ← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    rfl
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- Homogeneous coordinates are defined up to a nonzero scalar:
`[t c₀ : ⋯ : t c_N] = [c₀ : ⋯ : c_N]` for `t ≠ 0`. -/
theorem dualPoint_smul {k : Type u} [Field k] {N : ℕ} (c : Fin (N + 1) → k) (hc : c ≠ 0)
    {t : k} (ht : t ≠ 0) :
    dualPoint (t • c) (smul_ne_zero ht hc) = dualPoint c hc := by
  refine ProjectiveSpectrum.ext ?_
  refine HomogeneousIdeal.ext' fun d φ hφ => ?_
  have hφ' : φ.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hφ
  rw [mem_dualPoint_iff _ _ hφ', mem_dualPoint_iff _ _ hφ', eval_smul_of_isHomogeneous hφ',
    mul_eq_zero, or_iff_right (pow_ne_zero _ ht)]

/-- **A polynomial not vanishing on the line through `c` somewhere off the origin.** If some
homogeneous component of `Q` does not vanish at `c`, then `Q(t c) ≠ 0` for some `t ≠ 0`, over an
infinite field: `t ↦ Q(t c)` is the nonzero polynomial `∑ₘ Qₘ(c) tᵐ`. -/
theorem exists_ne_zero_eval_smul_ne_zero {σ K : Type*} [Field K] [Infinite K] [Fintype σ]
    (Q : MvPolynomial σ K) (c : σ → K) {d : ℕ}
    (hd : eval c (homogeneousComponent d Q) ≠ 0) : ∃ t : K, t ≠ 0 ∧ eval (t • c) Q ≠ 0 := by
  classical
  set p : Polynomial K := ∑ i ∈ Finset.range (Q.totalDegree + 1),
    Polynomial.monomial i (eval c (homogeneousComponent i Q)) with hp
  have hpeval : ∀ t : K, p.eval t = eval (t • c) Q := by
    intro t
    conv_rhs => rw [← sum_homogeneousComponent Q]
    rw [hp, Polynomial.eval_finset_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_monomial, eval_smul_of_isHomogeneous
      (homogeneousComponent_isHomogeneous i Q), mul_comm]
  have hdle : d < Q.totalDegree + 1 := by
    by_contra! h
    exact hd (by rw [homogeneousComponent_eq_zero d Q (by omega), map_zero])
  have hp0 : p ≠ 0 := by
    intro h0
    have := congrArg (fun q => Polynomial.coeff q d) h0
    simp only [hp, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero,
      Finset.sum_ite_eq', Finset.mem_range, hdle, if_true] at this
    exact hd this
  by_contra! hcon
  apply hp0
  have hX : p * Polynomial.X = 0 := Polynomial.funext fun t => by
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_zero]
    by_cases ht : t = 0
    · rw [ht, mul_zero]
    · rw [hpeval, hcon t ht, zero_mul]
  exact (mul_eq_zero.mp hX).resolve_right Polynomial.X_ne_zero

/-- A basic open of a nonzero element in the spectrum of a domain is dense: it contains the
generic point `(0)`. -/
theorem dense_basicOpen_of_ne_zero {R : Type*} [CommRing R] [IsDomain R] {f : R} (hf : f ≠ 0) :
    Dense (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  let g : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hg : g ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    change f ∉ (⊥ : Ideal R)
    simpa using hf
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun x => ?_)
  exact closure_mono (Set.singleton_subset_iff.mpr hg)
    ((PrimeSpectrum.le_iff_mem_closure g x).mp (show (⊥ : Ideal R) ≤ x.asIdeal from bot_le))

variable {k : Type u} [Field k] {N : ℕ}

/-- The generic point of `ℙᴺ_k`: the zero ideal. -/
def projectiveSpaceGenericPoint :
    AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) :=
  show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) from
  { asHomogeneousIdeal := ⊥
    isPrime := by
      change (⊥ : Ideal (MvPolynomial (Fin (N + 1)) k)).IsPrime
      exact Ideal.isPrime_bot
    not_irrelevant_le := by
      intro h
      have hX : MvPolynomial.X 0 ∈ HomogeneousIdeal.irrelevant
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) := by
        rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
          DirectSum.decompose_of_mem_ne _ (MvPolynomial.isHomogeneous_X k 0) one_ne_zero]
      have h2 : (MvPolynomial.X 0 : MvPolynomial (Fin (N + 1)) k) ∈ (⊥ : Ideal _) := h hX
      exact (MvPolynomial.X_ne_zero (R := k) (0 : Fin (N + 1))) (by simpa using h2) }

/-- A basic open `D₊(f)` of a nonzero `f` is dense in `ℙᴺ_k`: it contains the generic point. -/
theorem dense_projectiveSpace_basicOpen {f : MvPolynomial (Fin (N + 1)) k} (hf : f ≠ 0) :
    Dense ((ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) f :
      TopologicalSpace.Opens _) :
      Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))) := by
  let g : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) :=
    projectiveSpaceGenericPoint (k := k) (N := N)
  have hg : g ∈ ((ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) f : TopologicalSpace.Opens _) :
      Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))) := by
    change f ∉ (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal
    rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot]
    exact hf
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun x => ?_)
  exact closure_mono (Set.singleton_subset_iff.mpr hg)
    ((ProjectiveSpectrum.le_iff_mem_closure _ g x).mp
      (show (⊥ : HomogeneousIdeal _) ≤ x.asHomogeneousIdeal from bot_le))

end Coefficients

/-! ### Bertini theorems for free systems -/

section FreeSystem

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule
  morphismOfGeneratingSections)
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [local instance] globalSectionsModule

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

/-- **The standing situation of the Bertini theorems attached to a system `s₀, …, s_N`**: the
linear system is the coefficient space `kᴺ⁺¹`, mapped to `Γ(X, L)` by `c ↦ ∑ᵢ cᵢ sᵢ`, with its
standard basis reindexed by `Fin (dim kᴺ⁺¹)`. -/
def systemFamily (s : Fin (N + 1) → Γ(L, ⊤)) : Stacks.Bertini.FamilyDivisors.{u, u} where
  k := k
  V := Fin (N + 1) → k
  X := X
  toBase := X ↘ Spec (.of k)
  L := L
  isInvertible := (inferInstance : Stacks.Ample.IsInvertibleModule X L)
  ψ := systemSection s
  basis := (Pi.basisFun k (Fin (N + 1))).reindex (finCongr (Module.finrank_fin_fun k).symm)

omit [X.Over (Spec (.of k))] in
/-- The coordinates of a coefficient vector in the reindexed standard basis. -/
theorem sum_smul_reindex_basisFun (c : Fin (N + 1) → k) :
    ∑ i, c (Fin.cast (Module.finrank_fin_fun k) i) •
      ((Pi.basisFun k (Fin (N + 1))).reindex (finCongr (Module.finrank_fin_fun k).symm)) i = c := by
  set b := (Pi.basisFun k (Fin (N + 1))).reindex (finCongr (Module.finrank_fin_fun k).symm)
  conv_rhs => rw [← b.sum_repr c]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

/-- **The general members of a free system on a reduced scheme are reduced**, in polynomial form:
there is a nonzero polynomial `Q` in the coefficients such that `Z(∑ᵢ cᵢ sᵢ)` is reduced as soon
as `Q(c) ≠ 0`. -/
theorem exists_polynomial_isReduced_zeroScheme [CharZero k]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] [IsReduced X]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c Q ≠ 0 → IsReduced (zeroScheme X L (systemSection s c)).subscheme := by
  classical
  set D := systemFamily (k := k) s with hD
  haveI : IsReduced D.X := ‹IsReduced X›
  haveI : CharZero D.k := ‹CharZero k›
  haveI : LocallyOfFiniteType D.toBase := ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
  haveI : QuasiCompact D.toBase := ‹QuasiCompact (X ↘ Spec (.of k))›
  have hid : D.GeneratesBy (id : D.V → D.V) := by
    refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
    have hx : x ∈ (⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c)) := by
      rw [hs]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  have hgen : ∀ x : D.X, ∃ i, x ∈ nonvanishingOpen D.X D.L (D.sectionOf (D.basis i)) :=
    fun x => Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks _
      (D.generatesBy_basis hid D.basis) x
  haveI := isReduced_universalDivisorScheme hgen
  obtain ⟨V, hVne, hV⟩ := exists_opens_geometricallyReduced_universalFamily (D := D)
  obtain ⟨P, hP0, hP⟩ := exists_polynomial_parameterPoint_mem (D := D) V
    ⟨_, hVne.some.2⟩
  let σ : D.basisIndex ≃ Fin (N + 1) :=
    Equiv.ulift.trans (finCongr (Module.finrank_fin_fun k))
  refine ⟨MvPolynomial.rename σ P, fun h => hP0 (MvPolynomial.rename_injective _ σ.injective
    (h.trans (map_zero _).symm)), fun c hc => ?_⟩
  have hmem := hP (c ∘ σ) fun h0 => hc ((MvPolynomial.eval_rename _ _ _).trans h0)
  let a : Fin (Module.finrank D.k D.V) → D.k := fun i => (c ∘ σ) (ULift.up i)
  have hred := isReduced_zeroScheme_of_isReduced_specializedDivisor a
    (isReduced_specializedDivisor_of_mem hV a hmem)
  exact (congrArg (fun v => IsReduced (Stacks.Divisors.zeroScheme D.X D.L
    (D.sectionOf v)).subscheme) (sum_smul_reindex_basisFun c : (∑ i, a i • D.basis i) = _)).mp
    hred

/-- `Z(∑ᵢ (t cᵢ) sᵢ) = Z(∑ᵢ cᵢ sᵢ)` for a nonzero scalar `t`. -/
theorem zeroScheme_systemSection_smul (s : Fin (N + 1) → Γ(L, ⊤)) (c : Fin (N + 1) → k)
    {t : k} (ht : t ≠ 0) :
    zeroScheme X L (systemSection s (t • c)) = zeroScheme X L (systemSection s c) := by
  rw [map_smul]
  exact Stacks.Divisors.zeroScheme_smul_of_isUnit L _
    ((isUnit_iff_ne_zero.mpr ht).map
      (Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k X))

/-- **Reducedness of general members of a free system.** Let `k` be algebraically closed of
characteristic zero, `X` a reduced scheme of finite type over `k`, `L` an invertible sheaf on `X`
and `V ⊆ H⁰(X, L)` the finite-dimensional system spanned by `s₀, …, s_N`, generating `L`. There
are a dense open of `V` and a dense open of `ℙ(V)` such that the sections `∑ᵢ cᵢ sᵢ` with
coefficient vector `c` in the first, and with `c ≠ 0` and `[c]` in the second, have reduced zero
scheme. -/
@[mmp "lem_mmp_foundation_free_system_reduced_bertini"]
theorem exists_dense_open_isReduced_zeroScheme [IsAlgClosed k] [CharZero k]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] [IsReduced X]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤) :
    (∃ U : (coefficientSpace k N).Opens, Dense (U : Set (coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, coefficientPoint c ∈ U →
        IsReduced (zeroScheme X L (systemSection s c)).subscheme) ∧
    (∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        IsReduced (zeroScheme X L (systemSection s c)).subscheme) := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_isReduced_zeroScheme s hs
  refine ⟨⟨PrimeSpectrum.basicOpen Q, dense_basicOpen_of_ne_zero hQ0, fun c hc => hQ c ?_⟩, ?_⟩
  · exact fun h0 => hc (RingHom.mem_ker.mpr h0)
  obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.homogeneousComponent d Q ≠ 0 := by
    by_contra! h
    apply hQ0
    rw [← MvPolynomial.sum_homogeneousComponent Q]
    exact Finset.sum_eq_zero fun i _ => h i
  refine ⟨ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      (MvPolynomial.homogeneousComponent d Q), dense_projectiveSpace_basicOpen hd,
    fun c hc hmem => ?_⟩
  have hhc : MvPolynomial.eval c (MvPolynomial.homogeneousComponent d Q) ≠ 0 := fun h0 =>
    hmem ((mem_dualPoint_iff c hc (MvPolynomial.homogeneousComponent_isHomogeneous d Q)).mpr h0)
  obtain ⟨t, ht, htQ⟩ := exists_ne_zero_eval_smul_ne_zero Q c hhc
  rw [← zeroScheme_systemSection_smul s c ht]
  exact hQ (t • c) htQ

end FreeSystem

end MMP.Threefold.Bridges
