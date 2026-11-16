module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Semismooth.SingularLocus
public import MMP.AlgebraicGeometry.Resolution.Blowup.Charts
public import MMP.AlgebraicGeometry.MMP.Fourfold.BranchCounts
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.Divisor.DivisorialValuation
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Analytic.BorelMoore
import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicTopology.CapProduct.Restriction
public import MMP.AlgebraicGeometry.Intersection.OneCycles

/-!
# Free resolutions, products with a line, small morphisms, cycle ranks and curves

This file collects five independent foundational results used across the minimal model program:
regular local rings and (graded) finite free resolutions; products of a complex variety with a
line and base change to `ℂ(s)`; the divisor lost by a non-small threefold step; invariance of
Borel–Moore cycle ranks under isomorphism; and curves on positive-dimensional varieties.

## Regular local rings and finite free resolutions

Three standard facts from commutative algebra used in the algebraic part of GAGA.

1. If `(A, 𝔪)` is a regular local ring of dimension `n ≥ 1` and `x ∈ 𝔪 \ 𝔪²`, then `x` is a
   nonzerodivisor and `A ⧸ (x)` is a regular local ring of dimension `n - 1`.
2. Every finite module over a regular local ring of dimension `n` has a projective resolution
   whose terms are finite free modules and vanish above degree `n`.
3. (Hilbert's syzygy theorem, graded form.) Every finitely generated `ℤ`-graded module over
   `S = ℂ[x₀, …, x_N]` has a resolution of length at most `N + 1` by finite direct sums of shifted
   free modules `S(-d)`, all of whose maps are homogeneous of degree zero.

## Main results

* `MMP.GAGA.regularLocalRing_quotient_and_finite_free_resolutions`
* `MMP.isVariety_pullback_line_and_irreducibleComponents_baseChange_ratFunc`
* `IsThreefoldStepDiagram.exists_primeDivisor_isExceptionalValuation_of_not_isSmallMorphism`
  (in `MMP.Fourfold`)
* `MMP.Analytic.cycleRank_eq_of_iso`
* `MMP.Mori.exists_topologicalKrullDim_curveSubschemeAt_eq_one`

## Implementation notes

In (2) the resolution is a `CategoryTheory.ProjectiveResolution` of `ModuleCat.of A M`, which
records the augmentation and exactness; finite freeness of the terms and their vanishing in
degrees `> n` are stated termwise.

In (3) the polynomial ring is graded by total degree, written as the weighted grading
`MvPolynomial.weightedHomogeneousSubmodule ℂ (fun _ ↦ (1 : ℤ))` so that it is `ℤ`-indexed like
the module. A graded module is an `S`-module `M` with a decomposition `𝓜 : ℤ → Submodule ℂ M`
satisfying `SetLike.GradedSMul`. The term `F i = ⊕_{j < r i} S(-d i j)` is modelled as
`Fin (r i) → S`, whose `j`-th basis vector sits in degree `d i j`; a map is homogeneous of degree
zero exactly when it sends the `j`-th basis vector of `F (i+1)` to a vector whose `k`-th
coordinate is homogeneous of degree `d (i+1) j - d i k`, and the augmentation sends the `j`-th
basis vector of `F 0` into `𝓜 (d 0 j)`. Exactness, including surjectivity of the augmentation
and injectivity of the last map, is stated through ranges and kernels.
-/

section

universe u v

open CategoryTheory CategoryTheory.Limits IsLocalRing MvPolynomial

namespace MMP.GAGA.Internal.GagaMinimalResolutions

/-- In `WithBot ℕ∞`, `d + 1 = n` for a natural number `n` forces `d = n - 1`. -/
private theorem eq_natCast_sub_one_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ} (h : d + 1 = n) :
    d = ((n - 1 : ℕ) : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
      simp at h
    | coe k =>
      obtain rfl : k + 1 = n := by exact_mod_cast h
      rfl

/-- Cutting a regular local ring of dimension `n ≥ 1` by `x ∈ 𝔪 \ 𝔪²`. -/
private theorem part_one (A : Type u) [CommRing A] [IsRegularLocalRing A] (n : ℕ)
    (hn : ringKrullDim A = n) (x : A) (hx : x ∈ maximalIdeal A)
    (hx2 : x ∉ maximalIdeal A ^ 2) :
    x ∈ nonZeroDivisors A ∧ IsRegularLocalRing (A ⧸ Ideal.span {x}) ∧
      ringKrullDim (A ⧸ Ideal.span {x}) = ((n - 1 : ℕ) : WithBot ℕ∞) := by
  have hdom : IsDomain A := IsRegularLocalRing.isDomain A
  have hnzd : x ∈ nonZeroDivisors A :=
    mem_nonZeroDivisors_of_ne_zero fun h => hx2 (h ▸ Submodule.zero_mem _)
  have hdim : ringKrullDim (A ⧸ Ideal.span {x}) + 1 = ringKrullDim A :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd hx
  have : Nontrivial (A ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hx))
  have : IsLocalRing (A ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hsf := Stacks.RegularLocalRing.SpanFinrank.spanFinrank_maximalIdeal_succ_le_of_surjective
    (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective hx hx2
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x))
  have hle : ((maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞)
        + ((1 : ℕ) : WithBot ℕ∞)
      ≤ ringKrullDim (A ⧸ Ideal.span {x}) + ((1 : ℕ) : WithBot ℕ∞) := by
    rw [Nat.cast_one, hdim, ← IsRegularLocalRing.spanFinrank_maximalIdeal]
    exact_mod_cast hsf
  refine ⟨hnzd, IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _
    (ENat.WithBot.add_le_add_natCast_right_iff.mp hle), ?_⟩
  exact eq_natCast_sub_one_of_add_one_eq (hdim.trans hn)

/-- Part (2) for modules in the universe of the ring: Stacks 00O7 with depth bound `e = 0`. -/
private theorem part_two_sameUniverse (A : Type u) [CommRing A] [IsRegularLocalRing A] (n : ℕ)
    (hn : ringKrullDim A = n) (M : Type u) [AddCommGroup M] [Module A M]
    (hM : Module.Finite A M) :
    ∃ P : ProjectiveResolution (ModuleCat.of A M),
      (∀ i, Module.Free A (P.complex.X i) ∧ Module.Finite A (P.complex.X i)) ∧
        ∀ i, n < i → IsZero (P.complex.X i) := by
  obtain ⟨F, hF⟩ :=
    (IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE
      (R := A) (d := n) hn.le).1 (ModuleCat.of A M) 0 (by simp)
  refine ⟨F.toProjectiveResolution fun i => ?_, F.property, fun i hi => hF i (by omega)⟩
  have := (F.property i).1
  infer_instance

/-- If `A ⧸ I` and `A ⧸ I ^ i` are `v`-small and `A` is Noetherian, so is `A ⧸ I ^ (i + 1)`:
it is covered by `A ⧸ I ^ i × (s → A ⧸ I)` for a finite generating set `s` of `I ^ i`. -/
private theorem small_quotient_pow_succ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [Small.{v} (A ⧸ I)] (i : ℕ) [Small.{v} (A ⧸ I ^ i)] : Small.{v} (A ⧸ I ^ (i + 1)) := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (I ^ i) : (I ^ i).FG)
  refine small_of_surjective (α := (A ⧸ I ^ i) × (s → A ⧸ I))
    (f := fun p => Ideal.Quotient.mk _ (p.1.out + ∑ h : s, (p.2 h).out * h)) ?_
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have ha : a - (Ideal.Quotient.mk (I ^ i) a).out ∈ I ^ i :=
    Ideal.Quotient.eq.mp (by rw [Ideal.Quotient.mk_out])
  have ha' : a - (Ideal.Quotient.mk (I ^ i) a).out ∈ Submodule.span A (s : Set A) := by
    rwa [hs]
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp ha'
  refine ⟨(Ideal.Quotient.mk _ a, fun h => Ideal.Quotient.mk I (c h)), ?_⟩
  refine Ideal.Quotient.eq.mpr ?_
  have hc' : ∑ h : s, c h * h = a - (Ideal.Quotient.mk (I ^ i) a).out := by
    rw [Finset.sum_coe_sort s (fun h => c h * h)]; simpa only [smul_eq_mul] using hc
  have : (Ideal.Quotient.mk (I ^ i) a).out + ∑ h : s, (Ideal.Quotient.mk I (c h)).out * h - a =
      ∑ h : s, ((Ideal.Quotient.mk I (c h)).out - c h) * h := by
    simp only [sub_mul, Finset.sum_sub_distrib, hc']; ring
  rw [this, pow_succ']
  refine Ideal.sum_mem _ fun h _ => Ideal.mul_mem_mul ?_ ?_
  · exact Ideal.Quotient.eq.mp (by rw [Ideal.Quotient.mk_out])
  · rw [← hs]; exact Submodule.subset_span h.2

/-- A Noetherian local ring is `v`-small once its residue field is: by Krull's intersection
theorem it embeds in `∏ i, A ⧸ 𝔪 ^ i`. -/
private theorem small_of_isLocalRing {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [Small.{v} (A ⧸ maximalIdeal A)] : Small.{v} A := by
  have hI : ∀ i : ℕ, Small.{v} (A ⧸ maximalIdeal A ^ i) := by
    intro i
    induction i with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      have : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      exact small_of_surjective (f := fun _ : PUnit.{v + 1} => (0 : A ⧸ (⊤ : Ideal A)))
        fun q => ⟨PUnit.unit, Subsingleton.elim _ _⟩
    | succ i ih => exact small_quotient_pow_succ _ i
  have := Countable.toSmall.{v} ℕ
  refine small_of_injective (β := ∀ i : ℕ, A ⧸ maximalIdeal A ^ i)
    (f := fun a i => Ideal.Quotient.mk _ a) ?_
  intro a b hab
  have h := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro i
  exact Ideal.Quotient.eq.mp (congrFun hab i)

/-- The residue field of a local ring is `v`-small if some nontrivial finite module lives in
`Type v`: by Nakayama it embeds in `M ⧸ 𝔪 M`. -/
private theorem small_residue_of_module {A : Type u} [CommRing A] [IsLocalRing A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] :
    Small.{v} (A ⧸ maximalIdeal A) := by
  have hann : Module.annihilator A M ≠ ⊤ := by
    intro h
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    exact hm (by simpa using (Module.mem_annihilator.mp (h ▸ Submodule.mem_top : (1 : A) ∈ _)) m)
  have hne := Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (R := A) (M := M)
    (I := maximalIdeal A) (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ hann])
  obtain ⟨m, -, hm⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne.symm)
  let Q := M ⧸ (maximalIdeal A • (⊤ : Submodule A M))
  have hw : (Submodule.Quotient.mk m : Q) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have : Small.{v} Q := small_of_surjective (Submodule.Quotient.mk_surjective _)
  refine small_of_injective (β := Q) (f := fun c => c • (Submodule.Quotient.mk m : Q)) ?_
  intro c c' h
  let := Ideal.Quotient.field (maximalIdeal A)
  by_contra hcc
  have h0 : (c - c') • (Submodule.Quotient.mk m : Q) = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr h
  apply hw
  rw [← inv_smul_smul₀ (sub_ne_zero.mpr hcc) (Submodule.Quotient.mk m : Q), h0, smul_zero]

/-- Finiteness transfers along a ring isomorphism compatible with the two scalar actions. -/
private theorem module_finite_of_ringEquiv {R S N : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid N] [Module R N] [Module S N]
    (e : R ≃+* S) (h : ∀ (r : R) (x : N), e r • x = r • x)
    [hN : Module.Finite S N] : Module.Finite R N := by
  obtain ⟨t, ht⟩ := hN.fg_top
  refine ⟨⟨t, eq_top_iff.mpr fun m hmt => ?_⟩⟩
  clear hmt
  have hm : m ∈ Submodule.span S (t : Set N) := ht ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add _ _ _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    have hx' := Submodule.smul_mem _ (e.symm a) hx
    rwa [← h, e.apply_symm_apply] at hx'

/-- Finite freeness transfers along a ring isomorphism compatible with the two scalar actions. -/
private theorem module_free_finite_of_ringEquiv {R S N : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid N] [Module R N] [Module S N]
    (e : R ≃+* S) (h : ∀ (r : R) (x : N), e r • x = r • x)
    [Module.Free S N] [Module.Finite S N] : Module.Free R N ∧ Module.Finite R N :=
  ⟨Module.Free.of_basis ((Module.Free.chooseBasis S N).mapCoeffs e.symm fun c x => by
      rw [← h, e.apply_symm_apply]),
    module_finite_of_ringEquiv e h⟩

/-- Part (2) for a module `M` in an arbitrary universe `v`. -/
private theorem part_two (A : Type u) [CommRing A] [IsRegularLocalRing A] (n : ℕ)
    (hn : ringKrullDim A = n) (M : Type v) [AddCommGroup M] [Module A M]
    (hM : Module.Finite A M) :
    ∃ P : ProjectiveResolution (ModuleCat.of A M),
      (∀ i, Module.Free A (P.complex.X i) ∧ Module.Finite A (P.complex.X i)) ∧
        ∀ i, n < i → IsZero (P.complex.X i) := by
  rcases subsingleton_or_nontrivial M with hM0 | hM0
  · have hZ : IsZero (ModuleCat.of A M) := ModuleCat.isZero_of_subsingleton _
    have : Projective (ModuleCat.of A M) := hZ.projective
    refine ⟨ProjectiveResolution.self (ModuleCat.of A M), ?_⟩
    have hX : ∀ i, IsZero ((ProjectiveResolution.self (ModuleCat.of A M)).complex.X i) := by
      intro i
      rcases i with _ | i
      · exact hZ.of_iso (HomologicalComplex.singleObjXSelf _ _ _)
      · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    refine ⟨fun i => ?_, fun i _ => hX i⟩
    have : Subsingleton ((ProjectiveResolution.self (ModuleCat.of A M)).complex.X i) :=
      ModuleCat.subsingleton_of_isZero (hX i)
    exact ⟨Module.Free.of_subsingleton _ _, Module.Finite.of_finite⟩
  have := small_residue_of_module (A := A) M
  have := small_of_isLocalRing (A := A)
  let e : A ≃+* Shrink.{v} A := (Shrink.ringEquiv A).symm
  have : IsRegularLocalRing (Shrink.{v} A) := .of_ringEquiv e
  have hn' : ringKrullDim (Shrink.{v} A) = n := (ringKrullDim_eq_of_ringEquiv e).symm.trans hn
  let : Module (Shrink.{v} A) M := Module.compHom M (e.symm : Shrink.{v} A →+* A)
  have hfin : Module.Finite (Shrink.{v} A) M :=
    module_finite_of_ringEquiv e.symm fun _ _ => rfl
  obtain ⟨P, hfree, hzero⟩ := part_two_sameUniverse (Shrink.{v} A) n hn' M hfin
  let F := ModuleCat.restrictScalars.{v} e.toRingHom
  let Q := F.mapProjectiveResolution P
  let iso : F.obj (ModuleCat.of (Shrink.{v} A) M) ≅ ModuleCat.of A M :=
    LinearEquiv.toModuleIso (X₁ := F.obj (ModuleCat.of (Shrink.{v} A) M)) (X₂ := M)
      { toFun := fun m => (m : M)
        invFun := fun m => m
        map_add' := fun _ _ => rfl
        map_smul' := fun a m => by
          rw [RingHom.id_apply]
          exact congrArg (fun x : A => x • (show M from m)) (e.symm_apply_apply a)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl : F.obj (ModuleCat.of (Shrink.{v} A) M) ≃ₗ[A] M }
  refine ⟨ProjectiveResolution.mk Q.complex Q.projective
    (Q.π ≫ (ChainComplex.single₀ _).map iso.hom), fun i => ?_, fun i hi => ?_⟩
  · obtain ⟨_, _⟩ := hfree i
    let : Module A (P.complex.X i) := (F.obj (P.complex.X i)).isModule
    exact module_free_finite_of_ringEquiv (N := P.complex.X i) e fun _ _ => rfl
  · exact F.map_isZero (hzero i hi)

section Graded

variable {σ : Type}

/-- The data of a `ℤ`-grading of a module over `ℂ[σ]` (variables of weight `1`), presented by
its homogeneous pieces and the projections onto them. -/
private structure GrInfo (σ : Type) (X : Type*) [AddCommGroup X]
    [Module (MvPolynomial σ ℂ) X] where
  hom : ℤ → Set X
  proj : ℤ → X →+ X
  proj_mem : ∀ e x, proj e x ∈ hom e
  proj_same : ∀ e x, x ∈ hom e → proj e x = x
  proj_ne : ∀ e e' x, x ∈ hom e' → e' ≠ e → proj e x = 0
  exists_sum : ∀ x, ∃ s : Finset ℤ, ∑ e ∈ s, proj e x = x
  smul_mem : ∀ a b (c : MvPolynomial σ ℂ) x,
    c ∈ weightedHomogeneousSubmodule ℂ (fun _ : σ ↦ (1 : ℤ)) a → x ∈ hom b → c • x ∈ hom (a + b)

private theorem GrInfo.proj_smul {X : Type*} [AddCommGroup X] [Module (MvPolynomial σ ℂ) X]
    (G : GrInfo σ X) (e b : ℤ) (c : MvPolynomial σ ℂ) {x : X} (hx : x ∈ G.hom b) :
    G.proj e (c • x) = weightedHomogeneousComponent (fun _ : σ ↦ (1 : ℤ)) (e - b) c • x := by
  induction c using MvPolynomial.induction_on' with
  | monomial s a =>
    have hm : monomial s a ∈ weightedHomogeneousSubmodule ℂ (fun _ : σ ↦ (1 : ℤ))
        (Finsupp.weight (fun _ : σ ↦ (1 : ℤ)) s) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : Finsupp.weight (fun _ : σ ↦ (1 : ℤ)) s = e - b
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same (h ▸ hm)]
      refine G.proj_same _ _ ?_
      have := G.smul_mem _ _ _ _ hm hx
      rwa [h, sub_add_cancel] at this
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hm (Ne.symm h), zero_smul]
      exact G.proj_ne _ _ _ (G.smul_mem _ _ _ _ hm hx) (by omega)
  | add p q hp hq => rw [add_smul, map_add, hp, hq, map_add, add_smul]

/-- The grading of a module given by a decomposition into `ℂ`-submodules. -/
private noncomputable def grInfoOfDecomposition {X : Type*} [AddCommGroup X]
    [Module (MvPolynomial σ ℂ) X] [Module ℂ X]
    (𝓧 : ℤ → Submodule ℂ X) [DirectSum.Decomposition 𝓧]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule ℂ (fun _ : σ ↦ (1 : ℤ))) 𝓧] :
    GrInfo σ X where
  hom e := 𝓧 e
  proj e :=
    { toFun := fun x => (DirectSum.decompose 𝓧 x e : X)
      map_zero' := by simp
      map_add' := by simp }
  proj_mem e x := (DirectSum.decompose 𝓧 x e).2
  proj_same e x hx := by simp [DirectSum.decompose_of_mem_same 𝓧 hx]
  proj_ne e e' x hx h := by simp [DirectSum.decompose_of_mem_ne 𝓧 hx h]
  exists_sum x := by classical exact ⟨_, DirectSum.sum_support_decompose 𝓧 x⟩
  smul_mem a b c x hc hx := SetLike.GradedSMul.smul_mem hc hx

/-- The grading of the free module `ℂ[σ]^r` with generators in degrees `d`. -/
private noncomputable def grInfoPi (r : ℕ) (d : Fin r → ℤ) :
    GrInfo σ (Fin r → MvPolynomial σ ℂ) where
  hom e := {v | ∀ k, v k ∈ weightedHomogeneousSubmodule ℂ (fun _ : σ ↦ (1 : ℤ)) (e - d k)}
  proj e :=
    { toFun := fun v k => weightedHomogeneousComponent (fun _ : σ ↦ (1 : ℤ)) (e - d k) (v k)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  proj_mem e v k := weightedHomogeneousComponent_isWeightedHomogeneous _ _
  proj_same e v hv := funext fun k => (hv k).weightedHomogeneousComponent_same
  proj_ne e e' v hv h := funext fun k => (hv k).weightedHomogeneousComponent_ne _ (by omega)
  exists_sum v := by
    classical
    have hT : ∀ k, (Function.support fun m =>
        weightedHomogeneousComponent (fun _ : σ ↦ (1 : ℤ)) m (v k)).Finite :=
      fun k => weightedHomogeneousComponent_finsupp (v k)
    refine ⟨Finset.univ.biUnion fun k => (hT k).toFinset.image (· + d k), funext fun k => ?_⟩
    simp only [Finset.sum_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [← finsum_eq_sum_of_support_subset
      (fun e => weightedHomogeneousComponent (fun _ : σ ↦ (1 : ℤ)) (e - d k) (v k)) ?_]
    · conv_rhs => rw [← finsum_weightedHomogeneousComponent (fun _ : σ ↦ (1 : ℤ)) (v k)]
      exact finsum_comp_equiv (Equiv.subRight (d k))
        (f := fun m => weightedHomogeneousComponent (fun _ : σ ↦ (1 : ℤ)) m (v k))
    · intro e he
      simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
        Finset.coe_image, Set.mem_iUnion, Set.mem_image, Set.Finite.coe_toFinset]
      exact ⟨k, e - d k, he, sub_add_cancel _ _⟩
  smul_mem a b c v hc hv k := by
    simpa [add_sub_assoc] using hc.mul (hv k)

end Graded

section Syzygy

variable {σ : Type}

/-- A finitely generated submodule stable under the homogeneous projections is spanned by finitely
many homogeneous elements. -/
private theorem exists_homogeneous_span {X : Type*} [AddCommGroup X]
    [Module (MvPolynomial σ ℂ) X] (G : GrInfo σ X) (K : Submodule (MvPolynomial σ ℂ) X)
    (hKfg : K.FG) (hK : ∀ x ∈ K, ∀ e, G.proj e x ∈ K) :
    ∃ (r : ℕ) (d : Fin r → ℤ) (g : Fin r → X), (∀ j, g j ∈ G.hom (d j)) ∧
      Submodule.span (MvPolynomial σ ℂ) (Set.range g) = K := by
  classical
  obtain ⟨t, ht⟩ := hKfg
  choose s hs using G.exists_sum
  let T : Finset (ℤ × X) := t.biUnion fun x => (s x).image fun e => (e, G.proj e x)
  have hT : ∀ p ∈ T, p.2 ∈ G.hom p.1 ∧ p.2 ∈ K := by
    intro p hp
    simp only [T, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨x, hx, e, -, rfl⟩ := hp
    exact ⟨G.proj_mem e x, hK x (ht ▸ Submodule.subset_span hx) e⟩
  let eT := T.equivFin
  refine ⟨T.card, fun j => (eT.symm j).1.1, fun j => (eT.symm j).1.2,
    fun j => (hT _ (eT.symm j).2).1, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (hT _ (eT.symm j).2).2
  · rw [← ht, Submodule.span_le]
    intro x hx
    rw [← hs x]
    refine Submodule.sum_mem _ fun e he => Submodule.subset_span ⟨eT ⟨(e, G.proj e x), ?_⟩, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
    · simp

/-- A map from a graded free module sending the basis to homogeneous elements commutes with the
homogeneous projections. -/
private theorem proj_linearCombination {X : Type*} [AddCommGroup X]
    [Module (MvPolynomial σ ℂ) X] (G : GrInfo σ X) {r : ℕ} (d : Fin r → ℤ) (g : Fin r → X)
    (hg : ∀ j, g j ∈ G.hom (d j)) (e : ℤ) (v : Fin r → MvPolynomial σ ℂ) :
    G.proj e (Fintype.linearCombination (MvPolynomial σ ℂ) g v) =
      Fintype.linearCombination (MvPolynomial σ ℂ) g ((grInfoPi r d).proj e v) := by
  simp only [Fintype.linearCombination_apply, map_sum, G.proj_smul e _ _ (hg _)]
  rfl

private theorem ker_closed {X : Type*} [AddCommGroup X]
    [Module (MvPolynomial σ ℂ) X] (G : GrInfo σ X) {r : ℕ} (d : Fin r → ℤ) (g : Fin r → X)
    (hg : ∀ j, g j ∈ G.hom (d j)) :
    ∀ v ∈ LinearMap.ker (Fintype.linearCombination (MvPolynomial σ ℂ) g), ∀ e,
      (grInfoPi r d).proj e v ∈ LinearMap.ker (Fintype.linearCombination (MvPolynomial σ ℂ) g) := by
  intro v hv e
  rw [LinearMap.mem_ker] at hv ⊢
  rw [← proj_linearCombination G d g hg, hv, map_zero]

/-- A homogeneous polynomial of degree `0` (all variables of weight `1`) is constant. -/
private theorem eq_C_of_mem_weightedHomogeneousSubmodule_zero {p : MvPolynomial σ ℂ}
    (hp : p ∈ weightedHomogeneousSubmodule ℂ (fun _ : σ ↦ (1 : ℤ)) 0) : p = C (p.coeff 0) := by
  classical
  ext s
  rw [coeff_C]
  split_ifs with h
  · rw [h]
  · by_contra hs
    apply h
    have hw : Finsupp.weight (fun _ : σ ↦ (1 : ℤ)) s = 0 := hp hs
    have : ((s.degree : ℕ) : ℤ) = 0 := by
      rw [← hw, Finsupp.weight_apply, Finsupp.sum]
      change ((∑ i ∈ s.support, s i : ℕ) : ℤ) = _
      push_cast
      simp
    exact ((Finsupp.degree_eq_zero_iff s).mp (by exact_mod_cast this)).symm

/-- Dropping a redundant member of a homogeneous generating family. -/
private theorem exists_drop {X : Type*} [AddCommGroup X] [Module (MvPolynomial σ ℂ) X]
    (G : GrInfo σ X) {m : ℕ} (d : Fin m → ℤ) (g : Fin m → X) (hg : ∀ j, g j ∈ G.hom (d j))
    (j₀ : Fin m) (hj : g j₀ ∈ Submodule.span (MvPolynomial σ ℂ) (g '' {j | j ≠ j₀})) :
    ∃ (d' : Fin (m - 1) → ℤ) (g' : Fin (m - 1) → X), (∀ j, g' j ∈ G.hom (d' j)) ∧
      Submodule.span (MvPolynomial σ ℂ) (Set.range g') =
        Submodule.span (MvPolynomial σ ℂ) (Set.range g) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := j₀.pos; omega⟩
  refine ⟨d ∘ j₀.succAbove, g ∘ j₀.succAbove, fun j => hg _, le_antisymm ?_ ?_⟩
  · exact Submodule.span_mono (Set.range_comp_subset_range _ _)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨i, rfl⟩
    · refine Submodule.span_mono ?_ hj
      rintro _ ⟨k, hk, rfl⟩
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
      exact ⟨i, rfl⟩
    · exact Submodule.subset_span ⟨i, rfl⟩

/-- A homogeneous generating family of minimal length: its relations have coefficients in the
irrelevant ideal. -/
private theorem exists_homogeneous_span_minimal {X : Type*} [AddCommGroup X]
    [Module (MvPolynomial σ ℂ) X] (G : GrInfo σ X) (K : Submodule (MvPolynomial σ ℂ) X)
    (hKfg : K.FG) (hK : ∀ x ∈ K, ∀ e, G.proj e x ∈ K) :
    ∃ (r : ℕ) (d : Fin r → ℤ) (g : Fin r → X), (∀ j, g j ∈ G.hom (d j)) ∧
      Submodule.span (MvPolynomial σ ℂ) (Set.range g) = K ∧
      LinearMap.ker (Fintype.linearCombination (MvPolynomial σ ℂ) g) ≤
        (RingHom.ker (constantCoeff : MvPolynomial σ ℂ →+* ℂ)) • ⊤ ∧ (K = ⊥ → r = 0) := by
  classical
  have hex : ∃ r, ∃ (d : Fin r → ℤ) (g : Fin r → X), (∀ j, g j ∈ G.hom (d j)) ∧
      Submodule.span (MvPolynomial σ ℂ) (Set.range g) = K := exists_homogeneous_span G K hKfg hK
  obtain ⟨d, g, hg, hspan⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, d, g, hg, hspan, ?_, fun h0 => Nat.eq_zero_of_le_zero
    (Nat.find_min' hex ⟨Fin.elim0, Fin.elim0, fun j => j.elim0, by simp [h0]⟩)⟩
  intro z hz
  by_contra hzm
  obtain ⟨s, hs⟩ := (grInfoPi (Nat.find hex) d).exists_sum z
  obtain ⟨e, he⟩ : ∃ e, (grInfoPi (Nat.find hex) d).proj e z ∉
      (RingHom.ker (constantCoeff : MvPolynomial σ ℂ →+* ℂ)) •
        (⊤ : Submodule (MvPolynomial σ ℂ) (Fin (Nat.find hex) → MvPolynomial σ ℂ)) := by
    by_contra! h
    exact hzm (hs ▸ Submodule.sum_mem _ fun e _ => h e)
  set y := (grInfoPi (Nat.find hex) d).proj e z with hy
  have hyker : y ∈ LinearMap.ker (Fintype.linearCombination (MvPolynomial σ ℂ) g) :=
    ker_closed G d g hg z hz e
  have hyhom := (grInfoPi (Nat.find hex) d).proj_mem e z
  obtain ⟨j₀, hj₀⟩ : ∃ j, (y j).coeff 0 ≠ 0 := by
    by_contra! h
    apply he
    rw [pi_eq_sum_univ y]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [RingHom.mem_ker, constantCoeff_eq]
    exact h j
  have hdeg : e - d j₀ = 0 := ((hyhom j₀) hj₀).symm.trans (map_zero _)
  have hC : y j₀ = C ((y j₀).coeff 0) :=
    eq_C_of_mem_weightedHomogeneousSubmodule_zero (hdeg ▸ hyhom j₀)
  have hsum : ∑ j, y j • g j = 0 := hyker
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)] at hsum
  have hmem : g j₀ ∈ Submodule.span (MvPolynomial σ ℂ) (g '' {j | j ≠ j₀}) := by
    have : g j₀ = (C ((y j₀).coeff 0)⁻¹ : MvPolynomial σ ℂ) •
        -∑ j ∈ Finset.univ.erase j₀, y j • g j := by
      rw [← eq_neg_of_add_eq_zero_left hsum, smul_smul, hC, coeff_zero_C, ← C_mul,
        inv_mul_cancel₀ hj₀, C_1, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_))
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, Finset.ne_of_mem_erase hj, rfl⟩)
  obtain ⟨d', g', hg', hspan'⟩ := exists_drop G d g hg j₀ hmem
  have := Nat.find_min' hex ⟨d', g', hg', hspan'.trans hspan⟩
  have := j₀.pos
  omega

variable [Finite σ]

/-- If the span of a minimal homogeneous generating family is projective, the family is a basis:
the relation module `Z` is a direct summand with `Z ≤ 𝔪 • Z`, hence `Z = 0` by Nakayama. -/
private theorem ker_eq_bot_of_projective {X : Type*} [AddCommGroup X]
    [Module (MvPolynomial σ ℂ) X] {m : ℕ} (g : Fin m → X)
    (hP : Module.Projective (MvPolynomial σ ℂ)
      (LinearMap.range (Fintype.linearCombination (MvPolynomial σ ℂ) g)))
    (hker : LinearMap.ker (Fintype.linearCombination (MvPolynomial σ ℂ) g) ≤
        (RingHom.ker (constantCoeff : MvPolynomial σ ℂ →+* ℂ)) • ⊤) :
    LinearMap.ker (Fintype.linearCombination (MvPolynomial σ ℂ) g) = ⊥ := by
  set φ := Fintype.linearCombination (MvPolynomial σ ℂ) g
  set Z := LinearMap.ker φ
  let π := φ.rangeRestrict
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id φ.surjective_rangeRestrict
  let ρ := LinearMap.id - s ∘ₗ π
  have hρZ : ∀ z ∈ Z, ρ z = z := fun z hz => by
    have : π z = 0 := Subtype.ext (by simpa [π] using LinearMap.mem_ker.mp hz)
    simp [ρ, this]
  have hρ : ∀ v, ρ v ∈ Z := fun v => by
    rw [LinearMap.mem_ker]
    have h1 : π (s (π v)) = π v := LinearMap.congr_fun hs (π v)
    have h2 : φ (s (π v)) = φ v := congrArg Subtype.val h1
    simp [ρ, h2]
  have hle : Z ≤ (RingHom.ker (constantCoeff : MvPolynomial σ ℂ →+* ℂ)) • Z := by
    intro z hz
    have : z ∈ Submodule.map ρ ((RingHom.ker (constantCoeff : MvPolynomial σ ℂ →+* ℂ)) • ⊤) :=
      ⟨z, hker hz, hρZ z hz⟩
    rw [Submodule.map_smul''] at this
    have hmap : Submodule.map ρ ⊤ ≤ Z := by
      rintro _ ⟨v, -, rfl⟩
      exact hρ v
    exact Submodule.smul_mono le_rfl hmap this
  obtain ⟨a, ha, haz⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul _ Z
    (IsNoetherian.noetherian Z) hle
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  rw [eq_bot_iff]
  intro z hz
  exact (smul_eq_zero.mp (haz z hz)).resolve_left ha0

/-- Dimension shifting: the kernel of a surjection from a projective module onto a module of
projective dimension `≤ k + 1` has projective dimension `≤ k`. -/
private theorem hasProjectiveDimensionLE_ker {R : Type} [CommRing R] {B C : Type}
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [Module.Projective R B]
    (f : B →ₗ[R] C) (hf : Function.Surjective f) (k : ℕ)
    (hC : HasProjectiveDimensionLE (ModuleCat.of R C) (k + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) k := by
  have hS := LinearMap.shortExact_shortComplexKer hf
  have : HasProjectiveDimensionLT (ModuleCat.of R B) (k + 1) :=
    hasProjectiveDimensionLT_of_ge _ 1 _ (by omega)
  exact hS.hasProjectiveDimensionLT_X₁ (k + 1) this hC

/-- One step of a graded free resolution: cover a graded submodule of a graded free module by a
graded free module on a minimal homogeneous generating family. -/
private theorem exists_step {r : ℕ} (d : Fin r → ℤ)
    (K : Submodule (MvPolynomial σ ℂ) (Fin r → MvPolynomial σ ℂ))
    (hK : ∀ x ∈ K, ∀ e, (grInfoPi r d).proj e x ∈ K) (m : ℕ)
    (hpd : HasProjectiveDimensionLE (ModuleCat.of (MvPolynomial σ ℂ) K) m) :
    ∃ (r' : ℕ) (d' : Fin r' → ℤ)
      (φ : (Fin r' → MvPolynomial σ ℂ) →ₗ[MvPolynomial σ ℂ] (Fin r → MvPolynomial σ ℂ)),
      (∀ j k, φ (Pi.single j 1) k ∈
        weightedHomogeneousSubmodule ℂ (fun _ : σ ↦ (1 : ℤ)) (d' j - d k)) ∧
      LinearMap.range φ = K ∧
      (∀ x ∈ LinearMap.ker φ, ∀ e, (grInfoPi r' d').proj e x ∈ LinearMap.ker φ) ∧
      HasProjectiveDimensionLE (ModuleCat.of (MvPolynomial σ ℂ) (LinearMap.ker φ)) (m - 1) ∧
      (m = 0 → LinearMap.ker φ = ⊥) ∧ (K = ⊥ → r' = 0) := by
  classical
  obtain ⟨r', d', g, hg, hspan, hker, h0⟩ :=
    exists_homogeneous_span_minimal (grInfoPi r d) K (IsNoetherian.noetherian K) hK
  have hrange : LinearMap.range (Fintype.linearCombination (MvPolynomial σ ℂ) g) = K := by
    rw [Fintype.range_linearCombination, hspan]
  have hbot : m = 0 → LinearMap.ker (Fintype.linearCombination (MvPolynomial σ ℂ) g) = ⊥ := by
    rintro rfl
    have hP : Projective (ModuleCat.of (MvPolynomial σ ℂ) K) :=
      (projective_iff_hasProjectiveDimensionLE_zero _).mpr hpd
    have : Module.Projective (MvPolynomial σ ℂ) K :=
      ModuleCat.projective_of_module_projective (ModuleCat.of (MvPolynomial σ ℂ) K)
    exact ker_eq_bot_of_projective g (hrange ▸ this) hker
  refine ⟨r', d', Fintype.linearCombination _ g, fun j k => ?_, hrange,
    ker_closed (grInfoPi r d) d' g hg, ?_, hbot, h0⟩
  · rw [Fintype.linearCombination_apply_single, one_smul]; exact hg j k
  · rcases m with _ | m
    · rw [hbot rfl]
      have : Projective (ModuleCat.of (MvPolynomial σ ℂ)
          (⊥ : Submodule (MvPolynomial σ ℂ) (Fin r' → MvPolynomial σ ℂ))) :=
        (ModuleCat.isZero_of_subsingleton _).projective
      exact (projective_iff_hasProjectiveDimensionLE_zero _).mp this
    · rw [← hrange] at hpd
      have := hasProjectiveDimensionLE_ker (Fintype.linearCombination _ g).rangeRestrict
        (LinearMap.surjective_rangeRestrict _) m hpd
      rwa [LinearMap.ker_rangeRestrict] at this

omit [Finite σ] in
/-- The first step: cover a finitely generated graded module by a graded free module. -/
private theorem exists_start (M : Type v) [AddCommGroup M] [Module (MvPolynomial σ ℂ) M]
    [Module ℂ M] (𝓜 : ℤ → Submodule ℂ M) [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule ℂ (fun _ : σ ↦ (1 : ℤ))) 𝓜]
    (hM : Module.Finite (MvPolynomial σ ℂ) M) (N : ℕ)
    (hgl : ∀ X : ModuleCat.{0} (MvPolynomial σ ℂ), HasProjectiveDimensionLE X (N + 1)) :
    ∃ (r : ℕ) (d : Fin r → ℤ) (ε : (Fin r → MvPolynomial σ ℂ) →ₗ[MvPolynomial σ ℂ] M),
      (∀ j, ε (Pi.single j 1) ∈ 𝓜 (d j)) ∧ LinearMap.range ε = ⊤ ∧
      (∀ x ∈ LinearMap.ker ε, ∀ e, (grInfoPi r d).proj e x ∈ LinearMap.ker ε) ∧
      HasProjectiveDimensionLE (ModuleCat.of (MvPolynomial σ ℂ) (LinearMap.ker ε)) N := by
  classical
  obtain ⟨r, d, g, hg, hspan⟩ := exists_homogeneous_span (grInfoOfDecomposition (σ := σ) 𝓜) ⊤
    hM.fg_top (fun _ _ _ => Submodule.mem_top)
  refine ⟨r, d, Fintype.linearCombination _ g, fun j => ?_, by
    rw [Fintype.range_linearCombination, hspan], ker_closed _ d g hg, ?_⟩
  · rw [Fintype.linearCombination_apply_single, one_smul]; exact hg j
  · have := hasProjectiveDimensionLE_ker
      (LinearMap.ker (Fintype.linearCombination (MvPolynomial σ ℂ) g)).mkQ
      (Submodule.mkQ_surjective _) N (hgl _)
    rwa [Submodule.ker_mkQ] at this

end Syzygy

/-- Every module over `ℂ[x₀, …, x_N]` has projective dimension at most `N + 1`: the ring is
regular of Krull dimension `N + 1` (Stacks 00OE). -/
private theorem hasProjectiveDimensionLE_mvPolynomial {N : ℕ}
    (X : ModuleCat.{0} (MvPolynomial (Fin (N + 1)) ℂ)) : HasProjectiveDimensionLE X (N + 1) := by
  rw [← projectiveDimension_le_iff]
  have hd : ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ) = ((N + 1 : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hglobal : (⨆ M : ModuleCat.{0} (MvPolynomial (Fin (N + 1)) ℂ), projectiveDimension M) =
      ((N + 1 : ℕ) : WithBot ℕ∞) :=
    ((Stacks.RegularRing.GlobalDimension.solution (N + 1)).out 1 2).mpr
      (show IsRegularRing (MvPolynomial (Fin (N + 1)) ℂ) ∧ _ from ⟨inferInstance, hd⟩)
  exact (le_iSup (fun M : ModuleCat.{0} (MvPolynomial (Fin (N + 1)) ℂ) ↦
    projectiveDimension M) X).trans hglobal.le

/-- Part (3), the graded Hilbert syzygy theorem. -/
private theorem part_three (N : ℕ) (M : Type v) [AddCommGroup M]
    [Module (MvPolynomial (Fin (N + 1)) ℂ) M]
    [Module ℂ M] [IsScalarTower ℂ (MvPolynomial (Fin (N + 1)) ℂ) M]
    (𝓜 : ℤ → Submodule ℂ M) [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule ℂ (fun _ : Fin (N + 1) ↦ (1 : ℤ))) 𝓜]
    (hM : Module.Finite (MvPolynomial (Fin (N + 1)) ℂ) M) :
    ∃ (r : ℕ → ℕ) (d : ∀ i, Fin (r i) → ℤ)
      (δ : ∀ i, (Fin (r (i + 1)) → MvPolynomial (Fin (N + 1)) ℂ) →ₗ[MvPolynomial (Fin (N + 1)) ℂ]
        (Fin (r i) → MvPolynomial (Fin (N + 1)) ℂ))
      (ε : (Fin (r 0) → MvPolynomial (Fin (N + 1)) ℂ) →ₗ[MvPolynomial (Fin (N + 1)) ℂ] M),
      (∀ i, N + 1 < i → r i = 0) ∧
      (∀ j, ε (Pi.single j 1) ∈ 𝓜 (d 0 j)) ∧
      (∀ i j k, δ i (Pi.single j 1) k ∈
        weightedHomogeneousSubmodule ℂ (fun _ : Fin (N + 1) ↦ (1 : ℤ)) (d (i + 1) j - d i k)) ∧
      LinearMap.range ε = ⊤ ∧ LinearMap.range (δ 0) = LinearMap.ker ε ∧
      ∀ i, LinearMap.range (δ (i + 1)) = LinearMap.ker (δ i) := by
  classical
  obtain ⟨r₀, d₀, ε, hε, hεr, hεK, hεpd⟩ :=
    exists_start M 𝓜 hM N hasProjectiveDimensionLE_mvPolynomial
  let Stage := Σ r : ℕ, (Fin r → ℤ) × Submodule (MvPolynomial (Fin (N + 1)) ℂ)
    (Fin r → MvPolynomial (Fin (N + 1)) ℂ)
  let Q : ℕ → Stage → Prop := fun i t =>
    (∀ x ∈ t.2.2, ∀ e, (grInfoPi t.1 t.2.1).proj e x ∈ t.2.2) ∧
      HasProjectiveDimensionLE (ModuleCat.of (MvPolynomial (Fin (N + 1)) ℂ) t.2.2) (N - i)
  let Rel : ℕ → Stage → Stage → Prop := fun i t t' =>
    ∃ φ : (Fin t'.1 → MvPolynomial (Fin (N + 1)) ℂ) →ₗ[MvPolynomial (Fin (N + 1)) ℂ]
        (Fin t.1 → MvPolynomial (Fin (N + 1)) ℂ),
      (∀ j k, φ (Pi.single j 1) k ∈
        weightedHomogeneousSubmodule ℂ (fun _ : Fin (N + 1) ↦ (1 : ℤ)) (t'.2.1 j - t.2.1 k)) ∧
      LinearMap.range φ = t.2.2 ∧ LinearMap.ker φ = t'.2.2 ∧ (N ≤ i → t'.2.2 = ⊥) ∧
      (t.2.2 = ⊥ → t'.1 = 0)
  have hstep : ∀ i t, Q i t → ∃ t', Q (i + 1) t' ∧ Rel i t t' := by
    rintro i ⟨r, d, K⟩ ⟨hK, hpd⟩
    obtain ⟨r', d', φ, hφ, hr, hk, hkpd, h0, hb⟩ := exists_step d K hK (N - i) hpd
    exact ⟨⟨r', d', LinearMap.ker φ⟩, ⟨hk, by rwa [Nat.sub_sub] at hkpd⟩, φ, hφ, hr, rfl,
      fun h => h0 (by omega), hb⟩
  choose nxt hnxt using hstep
  let seq : (i : ℕ) → {t : Stage // Q i t} := fun i => Nat.rec
    (motive := fun i => {t : Stage // Q i t})
    ⟨⟨r₀, d₀, LinearMap.ker ε⟩, hεK, by simpa using hεpd⟩
    (fun i t => ⟨nxt i t.1 t.2, (hnxt i t.1 t.2).1⟩) i
  have hseq : ∀ i, Rel i (seq i).1 (seq (i + 1)).1 := fun i => (hnxt i (seq i).1 (seq i).2).2
  choose δ hδ using hseq
  refine ⟨fun i => (seq i).1.1, fun i => (seq i).1.2.1, δ, ε, fun i hi => ?_, hε,
    fun i => (hδ i).1, hεr, (hδ 0).2.1, fun i => (hδ (i + 1)).2.1.trans (hδ i).2.2.1.symm⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  exact (hδ (j + 1)).2.2.2.2 ((hδ j).2.2.2.1 (by omega))

end MMP.GAGA.Internal.GagaMinimalResolutions

namespace MMP.GAGA

open MMP.GAGA.Internal.GagaMinimalResolutions in
/-- (1) Cutting a regular local ring by an element of `𝔪 \ 𝔪²` gives a regular local ring of one
less dimension, and such an element is a nonzerodivisor; (2) finite modules over a regular local
ring of dimension `n` have finite free resolutions of length `≤ n`; (3) finitely generated graded
modules over `ℂ[x₀, …, x_N]` have graded resolutions of length `≤ N + 1` by finite sums of
shifted free modules. -/
@[mmp "lem_mmp_gaga_minimal_resolutions"]
public theorem regularLocalRing_quotient_and_finite_free_resolutions :
    (∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] (n : ℕ), ringKrullDim A = n → 1 ≤ n →
      ∀ x : A, x ∈ maximalIdeal A → x ∉ maximalIdeal A ^ 2 →
        x ∈ nonZeroDivisors A ∧ IsRegularLocalRing (A ⧸ Ideal.span {x}) ∧
          ringKrullDim (A ⧸ Ideal.span {x}) = ((n - 1 : ℕ) : WithBot ℕ∞)) ∧
    (∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] (n : ℕ), ringKrullDim A = n →
      ∀ (M : Type v) [AddCommGroup M] [Module A M], Module.Finite A M →
        ∃ P : ProjectiveResolution (ModuleCat.of A M),
          (∀ i, Module.Free A (P.complex.X i) ∧ Module.Finite A (P.complex.X i)) ∧
            ∀ i, n < i → IsZero (P.complex.X i)) ∧
    (∀ (N : ℕ) (M : Type v) [AddCommGroup M] [Module (MvPolynomial (Fin (N + 1)) ℂ) M]
      [Module ℂ M] [IsScalarTower ℂ (MvPolynomial (Fin (N + 1)) ℂ) M]
      (𝓜 : ℤ → Submodule ℂ M) [DirectSum.Decomposition 𝓜]
      [SetLike.GradedSMul (weightedHomogeneousSubmodule ℂ (fun _ : Fin (N + 1) ↦ (1 : ℤ))) 𝓜],
      Module.Finite (MvPolynomial (Fin (N + 1)) ℂ) M →
        ∃ (r : ℕ → ℕ) (d : ∀ i, Fin (r i) → ℤ)
          (δ : ∀ i, (Fin (r (i + 1)) → MvPolynomial (Fin (N + 1)) ℂ)
            →ₗ[MvPolynomial (Fin (N + 1)) ℂ] (Fin (r i) → MvPolynomial (Fin (N + 1)) ℂ))
          (ε : (Fin (r 0) → MvPolynomial (Fin (N + 1)) ℂ) →ₗ[MvPolynomial (Fin (N + 1)) ℂ] M),
          (∀ i, N + 1 < i → r i = 0) ∧
          (∀ j, ε (Pi.single j 1) ∈ 𝓜 (d 0 j)) ∧
          (∀ i j k, δ i (Pi.single j 1) k ∈
            weightedHomogeneousSubmodule ℂ (fun _ : Fin (N + 1) ↦ (1 : ℤ)) (d (i + 1) j - d i k)) ∧
          LinearMap.range ε = ⊤ ∧ LinearMap.range (δ 0) = LinearMap.ker ε ∧
          ∀ i, LinearMap.range (δ (i + 1)) = LinearMap.ker (δ i)) :=
  ⟨fun A _ _ n hn _ => part_one A n hn, fun A _ _ n hn M _ _ hM => part_two A n hn M hM,
    fun N M _ _ _ _ 𝓜 _ _ hM => part_three N M 𝓜 hM⟩

end MMP.GAGA

end

/-!
## Products of a complex variety with a line

Let `Z` be a complex variety and `L` the affine line `𝔸¹_ℂ = Spec ℂ[s]` or the projective line
`ℙ¹_ℂ`. Then `Z ×_ℂ L` is again a variety, of dimension `dim Z + 1`, and its function field is the
rational function field `ℂ(Z)(s)` in the affine coordinate `s`: the dense open
`Z ×_ℂ 𝔸¹ ⊆ Z ×_ℂ L` has the same function field, and that of `Z ×_ℂ 𝔸¹` is `ℂ(Z)(s)`, with
`ℂ(Z)` embedded by the first projection and `s` the pull-back of the coordinate along the second.

Moreover, for a reduced complex scheme `G` of finite type, the irreducible components of the base
change `G ×_ℂ Spec ℂ(s)` are exactly the preimages `G_k ×_ℂ Spec ℂ(s)` of the irreducible
components `G_k` of `G`, distinct for distinct `G_k`, and of the same dimension as `G_k`.

### Main results

* `MMP.isVariety_pullback_line_and_irreducibleComponents_baseChange_ratFunc`

### Implementation notes

* The product `Z × L` is the fibre product over `Spec ℂ`. The affine line is `Spec ℂ[X]` over
  `Spec ℂ` through `Polynomial.C`, and the projective line is `AlgebraicGeometry.projectiveLine ℂ`
  with its chart `AlgebraicGeometry.projectiveLineXChart ℂ`, whose coordinate is the affine
  coordinate `s`. The two cases are stated uniformly for a line `L` with structure morphism `l`
  and a chart `j : 𝔸¹ ⟶ L` over `Spec ℂ`, the chart being the identity for `L = 𝔸¹`.
* The function field is pinned by a ring isomorphism `RatFunc ℂ(Z) ≃+* ℂ(Z ×_ℂ 𝔸¹)` sending the
  constants `RatFunc.C a` to the pull-back of `a` along the first projection
  (`AlgebraicGeometry.functionFieldMap`) and `RatFunc.X` to the germ of the pulled-back coordinate,
  together with the bijectivity of the map of function fields induced by the dense open immersion
  `Z ×_ℂ 𝔸¹ ⟶ Z ×_ℂ L`. Integrality and dominance needed to form these maps are part of the
  conclusion.
* The field `ℂ(s)` is `RatFunc ℂ`. The scheme `G_k ×_ℂ Spec ℂ(s)` has underlying space the
  preimage of `G_k` under the projection, so the components are stated as a bijection
  `Set.BijOn` of preimages between irreducible components, and the dimensions as Krull dimensions
  of these subspaces (dimension over `ℂ(s)` of a scheme of finite type over `ℂ(s)`).
-/

section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace MMP.Internal.IndexbProductIrreducible

/-- The map of function fields of a dominant morphism sends the germ of a section to the germ of
its pull-back. -/
private theorem functionFieldMap_germToFunctionField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] (V : Y.Opens) [Nonempty V] (W : X.Opens)
    [Nonempty W] (hVW : W ≤ f ⁻¹ᵁ V) (s : Γ(Y, V)) :
    functionFieldMap f (Y.germToFunctionField V s) =
      X.germToFunctionField W (f.appLE V W hVW s) := by
  simp only [functionFieldMap, Scheme.germToFunctionField, TopCat.Presheaf.stalkCongr_hom,
    Scheme.Hom.appLE, ← ConcreteCategory.comp_apply, Category.assoc,
    TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

/-- Over an affine open `V ⊆ Z`, the sections of `Z ×_k 𝔸¹_k` over the preimage of `V` are the
polynomial ring `Γ(Z, V)[X]`, the variable being the pulled-back coordinate. -/
private theorem bijective_eval₂_appLE_pullback_affineLine {k : Type u} [Field k]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) {V : Z.Opens} (hV : IsAffineOpen V) :
    let a : Spec (.of (Polynomial k)) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
    Function.Bijective (Polynomial.eval₂RingHom
      ((pullback.fst f a).appLE V (pullback.fst f a ⁻¹ᵁ V) le_rfl).hom
      ((pullback.snd f a).appLE ⊤ (pullback.fst f a ⁻¹ᵁ V) (by simp)
        ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X))) := by
  intro a
  let UY := pullback.fst f a ⁻¹ᵁ V
  have H := IsPullback.of_hasPullback f a
  have hUY' : UY = pullback.fst f a ⁻¹ᵁ V ⊓ pullback.snd f a ⁻¹ᵁ ⊤ := by simp [UY]
  have hPO := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (by simp) (by simp) hUY').mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ hUY' (isAffineOpen_top _) (isAffineOpen_top _) hV)
  let iZ := f.appLE ⊤ V (by simp)
  let iA := a.appLE ⊤ ⊤ (by simp)
  let jZ := (pullback.fst f a).appLE V UY le_rfl
  let jA := (pullback.snd f a).appLE ⊤ UY (by simp)
  replace hPO : IsPushout iZ iA jZ jA := hPO
  let eK := Scheme.ΓSpecIso (.of k)
  let eP := Scheme.ΓSpecIso (.of (Polynomial k))
  have hC : ∀ c : k, eP.hom (iA (eK.inv c)) = Polynomial.C c := by
    intro c
    have h2 := congr($(Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) c)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h2
    change eP.hom (a.appTop (eK.inv c)) = _
    rw [← h2]
    simp [eP]
  let φ : k →+* Γ(Z, V) := iZ.hom.comp eK.inv.hom
  let θ : Polynomial Γ(Z, V) →+* Γ(pullback f a, UY) :=
    Polynomial.eval₂RingHom jZ.hom (jA (eP.inv Polynomial.X))
  have hw : iZ ≫ CommRingCat.ofHom Polynomial.C =
      iA ≫ eP.hom ≫ CommRingCat.ofHom (Polynomial.mapRingHom φ) := by
    ext r
    obtain ⟨c, rfl⟩ : ∃ c, eK.inv c = r := ⟨eK.hom r, by simp⟩
    simp [hC, φ]
  let ρ := hPO.desc _ _ hw
  have hρl : ∀ x, ρ (jZ x) = Polynomial.C x := fun x => congr($(hPO.inl_desc _ _ hw) x)
  have hρr : ∀ y, ρ (jA y) = Polynomial.map φ (eP.hom y) :=
    fun y => congr($(hPO.inr_desc _ _ hw) y)
  have hθρ : ∀ p, ρ (θ p) = p := by
    intro p
    have : ρ.hom.comp θ = RingHom.id _ := by
      apply Polynomial.ringHom_ext
      · intro x; simp [θ, hρl]
      · simp [θ, hρr]
    exact congr($this p)
  have hjA : ∀ q : Polynomial k, θ (Polynomial.map φ q) = jA (eP.inv q) := by
    intro q
    have : θ.comp (Polynomial.mapRingHom φ) = jA.hom.comp eP.inv.hom := by
      apply Polynomial.ringHom_ext
      · intro c
        have hw' := congr($(hPO.w) (eK.inv c))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hw'
        simp only [θ, φ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        rw [hw', ← hC c]
        simp
      · simp [θ]
    exact congr($this q)
  have hρθ : ∀ b, θ (ρ b) = b := by
    have : ρ ≫ CommRingCat.ofHom θ = 𝟙 _ := by
      apply hPO.hom_ext
      · ext x; simp [hρl, θ]
      · ext y; simp [hρr, hjA]
    exact fun b => congr($this b)
  exact ⟨Function.LeftInverse.injective hθρ, Function.RightInverse.surjective hρθ⟩

/-- The function field of `Z ×_k 𝔸¹_k`, for an integral scheme `Z` over a field `k`, is the field
of rational functions over the function field of `Z`, in the pulled-back coordinate. -/
private theorem exists_ratFunc_ringEquiv_functionField {k : Type u} [Field k] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of k)) [IsIntegral Z]
    [IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))] :
    let a : Spec (.of (Polynomial k)) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
    let U : Scheme.{u} := pullback f a
    let s₀ : Γ(U, ⊤) :=
      (pullback.snd f a).appTop ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)
    ∃ (_ : IsDominant (pullback.fst f a)) (_ : Nonempty (⊤ : U.Opens)),
      ∃ e : RatFunc Z.functionField ≃+* U.functionField,
        (∀ x : Z.functionField, e (RatFunc.C x) = functionFieldMap (pullback.fst f a) x) ∧
        e RatFunc.X = U.germToFunctionField ⊤ s₀ := by
  intro a U s₀
  have : Surjective a := ⟨fun y => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  obtain ⟨z⟩ : Nonempty Z := inferInstance
  obtain ⟨u, hu⟩ := (inferInstance : Surjective (pullback.fst f a)).surj z
  refine ⟨inferInstance, ⟨⟨u, trivial⟩⟩, ?_⟩
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top z)
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  let UY : U.Opens := pullback.fst f a ⁻¹ᵁ V
  have : Nonempty UY := ⟨⟨u, show pullback.fst f a u ∈ V from hu ▸ hzV⟩⟩
  have : IsAffineHom a := by unfold a; infer_instance
  have : IsAffineHom (pullback.fst f a) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback f a).flip this
  have hUY : IsAffineOpen UY := hV.preimage _
  let jA := (pullback.snd f a).appLE ⊤ UY (by simp)
  let θ : Polynomial Γ(Z, V) →+* Γ(U, UY) :=
    Polynomial.eval₂RingHom ((pullback.fst f a).appLE V UY le_rfl).hom
      (jA ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X))
  have hθ : Function.Bijective θ := bijective_eval₂_appLE_pullback_affineLine f hV
  have := functionField_isFractionRing_of_isAffineOpen Z V hV
  have := functionField_isFractionRing_of_isAffineOpen U UY hUY
  let ψ : Polynomial Z.functionField →+* U.functionField :=
    Polynomial.eval₂RingHom (functionFieldMap (pullback.fst f a)) (U.germToFunctionField ⊤ s₀)
  have hs₀ : U.germToFunctionField ⊤ s₀ = U.germToFunctionField UY
      (jA ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)) := by
    simp only [s₀, jA, Scheme.germToFunctionField, Scheme.Hom.appLE, Scheme.Hom.appTop,
      ← ConcreteCategory.comp_apply, Category.assoc]
    erw [TopCat.Presheaf.germ_res]
    rfl
  have hψθ : ∀ q : Polynomial Γ(Z, V),
      ψ (q.map (algebraMap Γ(Z, V) Z.functionField)) = U.germToFunctionField UY (θ q) := by
    intro q
    have : ψ.comp (Polynomial.mapRingHom (algebraMap Γ(Z, V) Z.functionField)) =
        (U.germToFunctionField UY).hom.comp θ := by
      apply Polynomial.ringHom_ext
      · intro x
        simp only [ψ, θ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        exact functionFieldMap_germToFunctionField _ V UY le_rfl x
      · simp [ψ, θ, hs₀]
    exact congr($this q)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have h1 := IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors Γ(Z, V))
      (functionFieldMap (pullback.fst f a)) p (x := U.germToFunctionField ⊤ s₀) hp
    rw [← Polynomial.eval₂_map] at h1
    have h2 : U.germToFunctionField UY
        (θ (IsLocalization.integerNormalization (nonZeroDivisors Γ(Z, V)) p)) = 0 := by
      rw [← hψθ]; exact h1
    rwa [map_eq_zero_iff _ (Scheme.germToFunctionField_injective U UY), map_eq_zero_iff _ hθ.1,
      IsLocalization.integerNormalization_eq_zero_iff le_rfl] at h2
  let e₀ : RatFunc Z.functionField →+* U.functionField := IsFractionRing.lift hψ
  have he₀ : ∀ p, e₀ (algebraMap _ _ p) = ψ p := fun p => IsFractionRing.lift_algebraMap hψ p
  have hsurj : Function.Surjective e₀ := by
    intro y
    obtain ⟨b1, b2, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(U, UY)) y
    obtain ⟨q1, rfl⟩ := hθ.2 b1
    obtain ⟨q2, rfl⟩ := hθ.2 b2
    refine ⟨algebraMap _ (RatFunc Z.functionField) (q1.map (algebraMap _ Z.functionField)) /
      algebraMap _ (RatFunc Z.functionField) (q2.map (algebraMap _ Z.functionField)), ?_⟩
    rw [map_div₀, he₀, he₀, hψθ, hψθ]
    rfl
  refine ⟨RingEquiv.ofBijective e₀ ⟨e₀.injective, hsurj⟩, fun x => ?_, ?_⟩
  · change e₀ _ = _
    rw [← RatFunc.algebraMap_C, he₀]
    simp [ψ]
  · change e₀ _ = _
    rw [← RatFunc.algebraMap_X, he₀]
    simp [ψ]

/-- The affine line over a field is a variety. -/
private theorem isVariety_affineLine (k : Type u) [Field k] :
    IsVariety k (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := by
  have := projectiveLineAffineStructureMorphism_locallyOfFiniteType k
  exact {}

/-- The affine line over a field has dimension one. -/
private theorem topologicalKrullDim_affineLine (k : Type u) [Field k] :
    topologicalKrullDim (Spec (.of (Polynomial k))) = 1 := by
  change topologicalKrullDim (PrimeSpectrum (Polynomial k)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  rfl

/-- The product of a variety `Z` with a line `L` over an algebraically closed field which
contains the affine line as a dense open chart. -/
private theorem isVariety_pullback_line {k : Type u} [Field k] [IsAlgClosed k] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of k)) [IsVariety k f] {L : Scheme.{u}} (l : L ⟶ Spec (.of k))
    [IsVariety k l] (hL : topologicalKrullDim L = 1) (j : Spec (.of (Polynomial k)) ⟶ L)
    [IsOpenImmersion j]
    (hj : j ≫ l = Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) :
    let a : Spec (.of (Polynomial k)) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
    let U : Scheme.{u} := pullback f a
    let s₀ : Γ(U, ⊤) :=
      (pullback.snd f a).appTop ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)
    IsVariety k (pullback.snd f l ≫ l) ∧
        topologicalKrullDim (pullback f l : Scheme.{u}) = topologicalKrullDim Z + 1 ∧
        ∃ (_ : IsIntegral (pullback f l)) (_ : IsIntegral U)
          (_ : IsDominant (pullback.map f a f l (𝟙 _) j (𝟙 _) (by simp) (by simp [hj, a])))
          (_ : IsDominant (pullback.fst f a)) (_ : Nonempty (⊤ : U.Opens)),
          Function.Bijective
            (functionFieldMap (pullback.map f a f l (𝟙 _) j (𝟙 _) _ _)) ∧
          ∃ e : RatFunc Z.functionField ≃+* U.functionField,
            (∀ x : Z.functionField, e (RatFunc.C x) = functionFieldMap (pullback.fst f a) x) ∧
            e RatFunc.X = U.germToFunctionField ⊤ s₀ := by
  intro a U s₀
  have ha : IsVariety k a := isVariety_affineLine k
  obtain ⟨hvL, hdL⟩ := isVariety_and_topologicalKrullDim_pullback k f l
  obtain ⟨hvU, -⟩ := isVariety_and_topologicalKrullDim_pullback k f a
  have hiL : IsIntegral (pullback f l) := hvL.toIsIntegral
  have hiU : IsIntegral U := hvU.toIsIntegral
  obtain ⟨hdom, hne, e, he⟩ := exists_ratFunc_ringEquiv_functionField f
  let m := pullback.map f a f l (𝟙 _) j (𝟙 _) (by simp) (by simp [hj, a])
  have hm : IsOpenImmersion m := by unfold m; infer_instance
  have hmd : IsDominant m := by
    refine ⟨?_⟩
    have : Nonempty U := ⟨hne.some.1⟩
    exact m.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  refine ⟨?_, ?_, hiL, hiU, hmd, hdom, hne,
    by rw [functionFieldMap]; exact ConcreteCategory.bijective_of_isIso _, e, he⟩
  · rw [← pullback.condition]
    exact hvL
  · rw [hdL, hL]

end MMP.Internal.IndexbProductIrreducible

namespace MMP

open MMP.Internal.IndexbProductIrreducible in
/-- For a complex variety `Z` and `L` the affine or projective line, `Z ×_ℂ L` is a variety of
dimension `dim Z + 1` whose function field is `ℂ(Z)(s)`, `s` the affine coordinate; and for a
reduced complex scheme `G` of finite type, the irreducible components of `G ×_ℂ Spec ℂ(s)` are the
preimages of the irreducible components of `G`, pairwise distinct and of the same dimension. -/
@[mmp "lem_mmp_indexb_product_irreducible"]
public theorem isVariety_pullback_line_and_irreducibleComponents_baseChange_ratFunc
    {Z : Scheme.{0}} (f : Z ⟶ Spec (.of ℂ)) [IsVariety ℂ f]
    {G : Scheme.{0}} (g : G ⟶ Spec (.of ℂ)) [IsReduced G] [LocallyOfFiniteType g]
    [QuasiCompact g] :
    let a : Spec (.of (Polynomial ℂ)) ⟶ Spec (.of ℂ) :=
      Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ))
    let U : Scheme.{0} := pullback f a
    let s₀ : Γ(U, ⊤) :=
      (pullback.snd f a).appTop ((Scheme.ΓSpecIso (.of (Polynomial ℂ))).inv Polynomial.X)
    let IsGoodLine : ∀ {L : Scheme.{0}} (l : L ⟶ Spec (.of ℂ))
        (j : Spec (.of (Polynomial ℂ)) ⟶ L), j ≫ l = a → Prop :=
      fun {L} l j hj =>
        IsVariety ℂ (pullback.snd f l ≫ l) ∧
        topologicalKrullDim (pullback f l : Scheme.{0}) = topologicalKrullDim Z + 1 ∧
        ∃ (_ : IsIntegral (pullback f l)) (_ : IsIntegral U)
          (_ : IsDominant (pullback.map f a f l (𝟙 _) j (𝟙 _) (by simp) (by simp [hj])))
          (_ : IsDominant (pullback.fst f a)) (_ : Nonempty (⊤ : U.Opens)),
          Function.Bijective
            (functionFieldMap (pullback.map f a f l (𝟙 _) j (𝟙 _) (by simp) (by simp [hj]))) ∧
          ∃ e : RatFunc Z.functionField ≃+* U.functionField,
            (∀ x : Z.functionField, e (RatFunc.C x) = functionFieldMap (pullback.fst f a) x) ∧
            e RatFunc.X = U.germToFunctionField ⊤ s₀
    let h : Spec (.of (RatFunc ℂ)) ⟶ Spec (.of ℂ) :=
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (RatFunc ℂ)))
    let p : pullback g h ⟶ G := pullback.fst g h
    IsGoodLine a (𝟙 _) (Category.id_comp a) ∧
    IsGoodLine (projectiveLine ℂ ↘ Spec (.of ℂ)) (projectiveLineXChart ℂ)
      (projectiveLineXChart_comp_structureMorphism ℂ) ∧
    Set.BijOn (fun T : Set G => p.base ⁻¹' T)
      (irreducibleComponents G) (irreducibleComponents (pullback g h : Scheme.{0})) ∧
    ∀ T ∈ irreducibleComponents G,
      topologicalKrullDim (p.base ⁻¹' T : Set (pullback g h : Scheme.{0})) =
        topologicalKrullDim T := by
  intro a U s₀ IsGoodLine h p
  have ha : IsVariety ℂ a := isVariety_affineLine ℂ
  obtain ⟨-, -, -, hcomp, hdim⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := RatFunc ℂ) g
  refine ⟨isVariety_pullback_line f a (topologicalKrullDim_affineLine ℂ) (𝟙 _)
      (Category.id_comp a),
    isVariety_pullback_line f _ (topologicalKrullDim_projectiveLine ℂ) (projectiveLineXChart ℂ)
      (projectiveLineXChart_comp_structureMorphism ℂ), hcomp, fun T hT => ?_⟩
  exact hdim T (isClosed_of_mem_irreducibleComponents T hT).isLocallyClosed

end MMP

end

/-!
## A non-small threefold step loses a divisor

In a threefold step diagram `X⁻ → Z ← X⁺` (`MMP.Fourfold.IsThreefoldStepDiagram`) the morphism
`f⁺` is small. If `f⁻` is not small, its exceptional locus contains a prime divisor `E` of `X⁻`,
and the divisorial valuation `ord_E`, carried to `k(X⁺)` through the identifications
`k(X⁻) ≅ k(Z) ≅ k(X⁺)`, is exceptional over `X⁺`: its centre on `X⁺` has codimension at least two.

### Main results

* `IsThreefoldStepDiagram.exists_primeDivisor_isExceptionalValuation_of_not_isSmallMorphism`
  (in `MMP.Fourfold`)

### Implementation notes

A valuation `v` of `k(X⁺)` is identified with `ord_E` on `k(X⁻)` when their restrictions to
`k(Z)` along `f⁺` and `f⁻` agree; since `f^±` are birational, this determines `v`.
-/

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold TopologicalSpace

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

namespace MMP.Fourfold.Internal.IndexcNotSmallLosesDivisor

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- In an integral scheme, a point has coheight zero iff it is the generic point. -/
private theorem coheight_eq_zero_iff_eq_genericPoint {X : Scheme.{0}} [IsIntegral X] (x : X) :
    Order.coheight x = 0 ↔ x = genericPoint X := by
  refine ⟨fun h ↦ Specializes.antisymm (Order.coheight_eq_zero.mp h (genericPoint_specializes x))
    (genericPoint_specializes x) |>.eq, ?_⟩
  rintro rfl
  exact Order.coheight_eq_zero.mpr fun z _ ↦ genericPoint_specializes z

omit [IsIntegral Xm] [IsIntegral Xp] in
/-- The base of a step diagram is Noetherian. -/
private theorem isNoetherian_target
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) : IsNoetherian Z := by
  have : AlgebraicGeometry.IsVariety ℂ sZ := h.isProjectiveVariety_target.toIsVariety
  have := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  exact {}

private theorem functionFieldMap_comp_apply {X Y W : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral W] (f : X ⟶ Y) (g : Y ⟶ W) [IsDominant f] [IsDominant g] [IsDominant (f ≫ g)]
    (a : W.functionField) :
    functionFieldMap (f ≫ g) a = functionFieldMap f (functionFieldMap g a) := by
  suffices h : CommRingCat.ofHom (functionFieldMap (f ≫ g)) =
      CommRingCat.ofHom ((functionFieldMap f).comp (functionFieldMap g)) from
    congrArg (fun φ : W.functionField ⟶ X.functionField ↦ φ.hom a) h
  apply Spec.map_injective
  apply (cancel_mono (W.fromSpecStalk (genericPoint W))).mp
  rw [functionFieldMap_fromSpecStalk (f ≫ g)]
  have hof : CommRingCat.ofHom ((functionFieldMap f).comp (functionFieldMap g)) =
      CommRingCat.ofHom (functionFieldMap g) ≫ CommRingCat.ofHom (functionFieldMap f) := rfl
  rw [hof, Spec.map_comp, Category.assoc, functionFieldMap_fromSpecStalk g,
    ← Category.assoc (Spec.map (CommRingCat.ofHom (functionFieldMap f))),
    functionFieldMap_fromSpecStalk f]
  exact (Category.assoc _ _ _).symm

omit [IsIntegral Xp] in
/-- If a step diagram's `f⁻` is not small, some prime divisor `E` of `X⁻` has image
`f⁻(η_E)` of coheight at least two in `Z`: `E` lies in the exceptional locus, and `f⁻` is an
isomorphism over every codimension-one point of the normal variety `Z`. -/
private theorem exists_primeDivisor_two_le_coheight_map
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hm : ¬ IsSmallMorphism sXm sZ fm) :
    ∃ E : MMP.Mori.PrimeDivisor Xm, 2 ≤ Order.coheight (fm E.genericPoint) := by
  have : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  have : IsNormal Z := h.isNormalVariety_target.2
  have : IsNoetherian Z := isNoetherian_target h
  have : IsDominant fm := h.isBirationalMorphism_minus.isDominant
  have : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    h.isBirationalMorphism_minus
  have key : ∀ y : Z, Order.coheight y ≤ 1 → y ∈ biregularLocus fm := by
    intro y hy
    obtain ⟨U, hyU, hU⟩ : ∃ U : Z.Opens, y ∈ U ∧ IsIso (fm ∣_ U) := by
      rcases lt_or_eq_of_le hy with h0 | h1
      · have hgy := (coheight_eq_zero_iff_eq_genericPoint y).mp (Order.lt_one_iff.mp h0)
        refine exists_isIso_restrict_of_mem_genericPoints fm hb y ?_
        rw [hgy]
        exact Stacks.Chow.genericPoint_mem_genericPoints Z
      · have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk h1
        exact exists_isIso_restrict_of_isDiscreteValuationRing fm hb y
    exact le_biregularLocus (f := fm) (V := U) hU hyU
  have hcod : ¬ 2 ≤ closedsCodimension (exceptionalSet fm) := fun hc ↦
    hm ⟨h.isNormalVariety_minus, h.isNormalVariety_target, h.comp_eq_minus, inferInstance,
      h.isBirationalMorphism_minus, hc⟩
  rw [le_closedsCodimension_iff] at hcod
  push Not at hcod
  obtain ⟨W, hWE, hW⟩ := hcod
  set x := irreducibleSetEquivPoints (α := Xm) W with hx
  have hWx : (irreducibleSetEquivPoints (α := Xm)).symm x = W := by simp [hx]
  have hxc : Order.coheight x < 2 := by
    rwa [← hWx, codimension_eq_coheight, Order.coheight_orderIso] at hW
  have hxE : x ∈ exceptionalSet fm := hWE (by
    rw [← hWx]
    exact subset_closure rfl)
  have hfx : ¬ Order.coheight (fm x) ≤ 1 := fun h1 ↦ (mem_exceptionalSet.mp hxE) (key _ h1)
  have hx1 : Order.coheight x = 1 := by
    refine (Order.le_of_lt_add_one (show Order.coheight x < 1 + 1 from hxc)).eq_of_not_lt
      fun h0 ↦ hfx ?_
    rw [(coheight_eq_zero_iff_eq_genericPoint x).mp (Order.lt_one_iff.mp h0),
      MMP.Positivity.map_genericPoint_eq_of_isDominant]
    exact ((coheight_eq_zero_iff_eq_genericPoint _).mpr rfl).le.trans zero_le_one
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1, ?_⟩
  rw [show MMP.Mori.PrimeDivisor.genericPoint (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1)
    = x from AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hx1]
  exact not_le.mp hfx |> Order.add_one_le_of_lt

/-! ### The normalized graph of two birational morphisms to `Z` -/

section NormalizedGraph

variable {M P S : Scheme.{0}} [IsIntegral M] [IsIntegral P] [IsIntegral S]
  {fm : M ⟶ S} {fp : P ⟶ S} [IsDominant fm] [IsDominant fp]

private theorem isIso_functionFieldMap (hp : IsBirational fp) : IsIso fp.functionFieldMap := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(functionFieldMap fp).injective, hp.surjective_functionFieldMap⟩

private theorem specMap_functionFieldMap_fromSpecStalk {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    Spec.map f.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f :=
  functionFieldMap_fromSpecStalk f

variable (fm) in
/-- The generic point of `X⁻`, mapped to `X⁻ ×_Z X⁺` through `k(X⁺) ≅ k(Z) ≅ k(X⁻)`. -/
private noncomputable def graphPoint (hp : IsBirational fp) :
    Spec M.functionField ⟶ Limits.pullback fp fm :=
  haveI := isIso_functionFieldMap hp
  Limits.pullback.lift (Spec.map (inv fp.functionFieldMap ≫ fm.functionFieldMap) ≫
      P.fromSpecStalk (genericPoint P)) (M.fromSpecStalk (genericPoint M)) (by
    rw [Category.assoc, ← specMap_functionFieldMap_fromSpecStalk fp, Spec.map_comp,
      Category.assoc, ← Category.assoc (Spec.map (inv fp.functionFieldMap)), ← Spec.map_comp,
      IsIso.hom_inv_id, Spec.map_id, Category.id_comp, specMap_functionFieldMap_fromSpecStalk])

private theorem quasiCompact_graphPoint (hp : IsBirational fp) : QuasiCompact (graphPoint fm hp) :=
  quasiCompact_of_isField (Field.toIsField _) _

private theorem quasiSeparated_graphPoint (hp : IsBirational fp) :
    QuasiSeparated (graphPoint fm hp) :=
  QuasiSeparated.of_quasiSeparatedSpace _

attribute [local instance] quasiCompact_graphPoint quasiSeparated_graphPoint

private theorem graphPoint_snd (hp : IsBirational fp) :
    graphPoint fm hp ≫ Limits.pullback.snd fp fm = M.fromSpecStalk (genericPoint M) :=
  Limits.pullback.lift_snd _ _ _

/-- The projection of the normalized graph to `X⁻` is birational. -/
private theorem isBirational_toMinus (hp : IsBirational fp) :
    IsBirational ((graphPoint fm hp).fromNormalization ≫ Limits.pullback.snd fp fm) := by
  set g := (graphPoint fm hp).fromNormalization ≫ Limits.pullback.snd fp fm
  have := isDominant_fromSpecStalk_genericPoint M
  let j := (graphPoint fm hp).toNormalization
  have hj : j ≫ g = M.fromSpecStalk (genericPoint M) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, graphPoint_snd]
  have : IsDominant (j ≫ g) := by rw [hj]; infer_instance
  have : IsDominant g := IsDominant.of_comp j _
  refine isBirational_of_surjective_functionFieldMap _ fun w => ?_
  have hbij : Function.Bijective (functionFieldMap (j ≫ g)) := by
    rw! (castMode := .all) [hj]
    exact bijective_functionFieldMap_fromSpecStalk_genericPoint M
  obtain ⟨a, ha⟩ := hbij.2 (functionFieldMap j w)
  rw [functionFieldMap_comp_apply] at ha
  exact ⟨a, (functionFieldMap j).injective ha⟩

/-- Over `ℂ`, the normalized graph is finite over `X⁻ ×_Z X⁺`. -/
private theorem isFinite_fromNormalization_graphPoint (hp : IsBirational fp)
    (s : M ⟶ Spec (.of ℂ)) [LocallyOfFiniteType s] [LocallyOfFiniteType fp] :
    IsFinite (graphPoint fm hp).fromNormalization := by
  have hP : IsNagataScheme (Limits.pullback fp fm) :=
    isNagataScheme_of_locallyOfFiniteType (Limits.pullback.snd fp fm ≫ s)
      (isNagataScheme_spec_of_isNagataRing _ IsNagataRing.of_field)
  have : Finite (Spec M.functionField) :=
    inferInstanceAs (Finite (PrimeSpectrum M.functionField))
  refine isFinite_fromNormalization (graphPoint fm hp) hP
    (fun U _ => have : Finite U := Subtype.finite
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents) fun x => ?_
  let φ := graphPoint fm hp
  let := (φ.residueFieldMap x.1).hom.toAlgebra
  have hsurj : Function.Surjective (φ.residueFieldMap x.1).hom := by
    have h := surjective_residueFieldMap_of_surjectiveOnStalks
      (M.fromSpecStalk (genericPoint M)) x.1
    rw [Scheme.Hom.residueFieldMap_congr (graphPoint_snd (fm := fm) hp).symm,
      Scheme.residueFieldMap_comp] at h
    exact fun z => ⟨_, (h z).choose_spec⟩
  have : Algebra.EssFiniteType (Limits.pullback fp fm |>.residueField (φ x.1))
      ((Spec M.functionField).residueField x.1) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
  exact IntermediateField.fg_top _ _

end NormalizedGraph

/-! ### Birational morphisms -/

section Birational

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsNoetherian X]

/-- A separated birational morphism of finite type onto a Noetherian integral scheme is a
birational morphism in the sense of rational maps. -/
private theorem isBirationalMorphism_of_isBirational (f : Y ⟶ X) [IsSeparated f]
    [LocallyOfFiniteType f] (hf : IsBirational f) : IsBirationalMorphism f := by
  have := hf.isDominant
  obtain ⟨V, hV, hiso⟩ := exists_isIso_restrict_of_mem_genericPoints f hf (genericPoint X)
    (Stacks.Chow.genericPoint_mem_genericPoints X)
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ V) V
    ⟨genericPoint Y, show f (genericPoint Y) ∈ V by
      rwa [MMP.Positivity.map_genericPoint_eq_of_isDominant]⟩ ⟨_, hV⟩ le_rfl ?_
  simpa [Scheme.Hom.resLE] using hiso

/-- Under a separated birational morphism of finite type onto a Noetherian integral scheme, the
generic point is the only point over the generic point. -/
private theorem preimage_genericPoints (f : Y ⟶ X) [IsSeparated f] [LocallyOfFiniteType f]
    (hf : IsBirational f) : f ⁻¹' genericPoints X = genericPoints Y := by
  have := hf.isDominant
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hy
    obtain ⟨V, hV, hiso⟩ := exists_isIso_restrict_of_mem_genericPoints f hf (genericPoint X)
      (Stacks.Chow.genericPoint_mem_genericPoints X)
    have hmem : f y ∈ biregularLocus f := le_biregularLocus (f := f) (V := V) hiso (hy ▸ hV)
    rw [← coheight_eq_zero_iff_eq_genericPoint,
      ← MMP.Positivity.coheight_map_of_mem_biregularLocus f hmem, hy,
      coheight_eq_zero_iff_eq_genericPoint]
  · rintro rfl
    exact MMP.Positivity.map_genericPoint_eq_of_isDominant f

end Birational

/-- A normal integral scheme proper over a normal variety is a normal variety. -/
private theorem isNormalVariety_comp {X Y : Scheme.{0}} [IsIntegral Y] [IsNormal Y]
    {s : X ⟶ Spec (.of ℂ)} (hs : IsNormalVariety ℂ s) (f : Y ⟶ X) [IsProper f] :
    IsNormalVariety ℂ (f ≫ s) := by
  obtain ⟨-, h1, h2, h3⟩ := (MMP.Mori.isVariety_iff ℂ s).mp hs.1
  exact ⟨(MMP.Mori.isVariety_iff ℂ (f ≫ s)).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    inferInstance⟩

private theorem functionFieldMap_congr_apply {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {f g : X ⟶ Y} [IsDominant f] [IsDominant g] (h : f = g) (a : Y.functionField) :
    functionFieldMap f a = functionFieldMap g a := by
  subst h; rfl

/-- The divisor `E` of `X⁻` is realized by a proper divisor over `X⁺` (on the normalized closure
of the graph of `X⁻ ⇢ X⁺`), whose valuation corresponds to `ord_E` and whose centre lies over
`f⁻(η_E)`. -/
private theorem exists_divisorOver_comap_eq
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (E : MMP.Mori.PrimeDivisor Xm) :
    haveI := h.isNormalVariety_target.1.toIsIntegral
    haveI := h.isBirationalMorphism_minus.isDominant
    haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
    ∃ D : MMP.Mori.DivisorOver ℂ sXp, IsProper D.f ∧
      D.valuation.comap (functionFieldMap fp) =
        E.divisorialValuation.comap (functionFieldMap fm) ∧
      fp (D.f D.E.genericPoint) = fm E.genericPoint := by
  have : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  have : IsDominant fm := h.isBirationalMorphism_minus.isDominant
  have : IsDominant fp := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have : IsNoetherian Xm := {}
  have : IsNoetherian Xp := {}
  have : IsNoetherian Z := isNoetherian_target h
  have hbm := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    h.isBirationalMorphism_minus
  have hbp := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    h.isSmallMorphism_plus.isBirationalMorphism
  have : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  have : IsProper fp := h.isSmallMorphism_plus.isProper
  have hvm := h.isNormalVariety_minus
  have hvp := h.isNormalVariety_plus
  have : LocallyOfFiniteType sXm := ((MMP.Mori.isVariety_iff ℂ sXm).mp hvm.1).2.2.1
  have : IsFinite (graphPoint fm hbp).fromNormalization :=
    isFinite_fromNormalization_graphPoint hbp sXm
  have : IsNormal (graphPoint fm hbp).normalization :=
    isNormal_normalization_of_isField (Field.toIsField _) _
  set u := (graphPoint fm hbp).fromNormalization ≫ Limits.pullback.snd fp fm with hu_def
  set v := (graphPoint fm hbp).fromNormalization ≫ Limits.pullback.fst fp fm with hv_def
  have huv : v ≫ fp = u ≫ fm := by
    simp only [hu_def, hv_def, Category.assoc, Limits.pullback.condition]
  have : IsProper u := by rw [hu_def]; infer_instance
  have : IsProper v := by rw [hv_def]; infer_instance
  have hu : IsBirational u := isBirational_toMinus hbp
  have hv : IsBirational v := isBirational_of_comp_of_isBirational v fp
    (by rw [huv]; exact hu.comp hbm) hbp (preimage_genericPoints fp hbp)
  have := hu.isDominant
  have := hv.isDominant
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
    E.coheight_genericPoint
  obtain ⟨U, hEU, hUiso⟩ := exists_isIso_restrict_of_isDiscreteValuationRing u hu E.genericPoint
  obtain ⟨x, hx⟩ : E.genericPoint ∈ Set.range u := by
    rw [← u.isClosedMap.isClosed_range.closure_eq, u.denseRange.closure_range]; trivial
  have hxb : u x ∈ biregularLocus u := le_biregularLocus (f := u) (V := U) hUiso (hx ▸ hEU)
  have hx1 : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus u hxb, hx]
    exact E.coheight_genericPoint
  have hE' : MMP.Mori.PrimeDivisor.genericPoint
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1) = x :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hx1
  let Dm : MMP.Mori.DivisorOver ℂ sXm :=
    ⟨_, u, isNormalVariety_comp hvm u, isBirationalMorphism_of_isBirational u hu,
      AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1⟩
  let D : MMP.Mori.DivisorOver ℂ sXp :=
    ⟨_, v, isNormalVariety_comp hvp v, isBirationalMorphism_of_isBirational v hv,
      AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1⟩
  have hDm := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hvm Dm E
    (by change u _ = _; rw [hE', hx])
  have : IsLocallyNoetherian (graphPoint fm hbp).normalization := Dm.isLocallyNoetherian
  refine ⟨D, ‹IsProper v›, ?_, ?_⟩
  · ext g
    have hg := congrArg (fun w => w (functionFieldMap fm g)) hDm
    change MMP.Mori.PrimeDivisor.divisorialValuation
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1)
      (functionFieldMap v (functionFieldMap fp g)) = _
    change MMP.Mori.PrimeDivisor.divisorialValuation
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1)
      (functionFieldMap u (functionFieldMap fm g)) =
      E.divisorialValuation (functionFieldMap (𝟙 Xm) (functionFieldMap fm g)) at hg
    rw [MMP.Mori.functionFieldMap_id_apply] at hg
    refine Eq.trans (congrArg _ ?_) hg
    rw [← functionFieldMap_comp_apply, ← functionFieldMap_comp_apply]
    exact functionFieldMap_congr_apply huv _
  · change fp (v _) = _
    rw [hE', ← Scheme.Hom.comp_apply, huv, Scheme.Hom.comp_apply, hx]

omit [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] in
/-- A small morphism does not lower coheight two to coheight at most one: it is an open immersion
near every point of coheight at most one. -/
private theorem two_le_coheight_of_two_le_coheight_map {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {fp : Xp ⟶ Z} (hp : IsSmallMorphism sXp sZ fp) (x : Xp)
    (hx : 2 ≤ Order.coheight (fp x)) : 2 ≤ Order.coheight x := by
  by_cases hE : x ∈ exceptionalSet fp
  · exact MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hp.two_le_codimension hE
  · rw [mem_exceptionalSet, not_not] at hE
    rwa [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp hE]

end MMP.Fourfold.Internal.IndexcNotSmallLosesDivisor

namespace MMP.Fourfold.IsThreefoldStepDiagram

open MMP.Fourfold.Internal.IndexcNotSmallLosesDivisor in
/-- In a threefold step diagram `X⁻ → Z ← X⁺` in which `f⁻` is not small, there is a prime
divisor `E` of `X⁻` whose valuation `ord_E`, transported to `k(X⁺)` (the valuation `v` of
`k(X⁺)` with the same restriction to `k(Z)`), is exceptional over `X⁺`. -/
@[mmp "lem_mmp_indexc_not_small_loses_divisor"]
public theorem exists_primeDivisor_isExceptionalValuation_of_not_isSmallMorphism
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hm : ¬ IsSmallMorphism sXm sZ fm) :
    haveI := h.isNormalVariety_target.1.toIsIntegral
    haveI := h.isBirationalMorphism_minus.isDominant
    haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
    ∃ (E : MMP.Mori.PrimeDivisor Xm) (v : Valuation Xp.functionField (WithZero (Multiplicative ℤ))),
      v.comap (functionFieldMap fp) = E.divisorialValuation.comap (functionFieldMap fm) ∧
        MMP.Intersection.IsExceptionalValuation ℂ sXp v := by
  obtain ⟨E, hE⟩ := exists_primeDivisor_two_le_coheight_map h hm
  obtain ⟨D, hD, hv, hc⟩ := exists_divisorOver_comap_eq h E
  refine ⟨E, D.valuation, hv, D, hD, rfl, ?_⟩
  rw [MMP.Positivity.DivisorOver.codimension_center]
  exact two_le_coheight_of_two_le_coheight_map h.isSmallMorphism_plus _ (hc ▸ hE)

end MMP.Fourfold.IsThreefoldStepDiagram

end

/-!
## Borel–Moore homology and cycle ranks are invariant under isomorphism

An isomorphism `φ : X ≅ Y` of schemes over `ℂ` realizes to a homeomorphism `X^an ≃ₜ Y^an`
of complex realizations, so the proper push-forward
`φ_* : H^BM_k(X, ℚ) → H^BM_k(Y, ℚ)` is an isomorphism for every `k`. It carries the
fundamental class `[A]` of every irreducible closed subvariety `A ⊆ X` of dimension `r` to the
fundamental class `[φ(A)]` of its image. Hence `φ_*` maps the cycle span `Cyc_r(X)` onto
`Cyc_r(Y)`, and the cycle ranks agree: `ρ_r(X) = ρ_r(Y)`.

### Main results

* `MMP.Analytic.cycleRank_eq_of_iso`: `φ_*` is bijective in every degree, sends `[A]` to
  `[φ(A)]`, maps `Cyc_r(X)` onto `Cyc_r(Y)`, and `ρ_r(X) = ρ_r(Y)`.

### Implementation notes

The induced isomorphism is the Borel–Moore push-forward
`MMP.borelMooreHomology.pushforward` along the realized map
`MMP.Analytic.ComplexPoints.analyticMap φ.hom`, which is proper because it is a homeomorphism
with inverse the realization of `φ.inv`. A subvariety `A` is given by its generic point `x`, of
delta-dimension `r`, and `φ(A)` by the point `φ x`. The statement holds for
all complex schemes in Fulton's sense (`MMP.IsComplexScheme`), the setting in
which the fundamental classes are defined, not only for varieties.

### References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

section

open CategoryTheory AlgebraicGeometry MMP MMP.Analytic

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [IsComplexScheme X] [IsComplexScheme Y]

namespace MMP.Analytic.Internal.IndexdCycleRankIsomorphism

/-- The push-forward along a map with a two-sided inverse is bijective, with inverse the
push-forward along the inverse. -/
private lemma pushforward_bijective_of_inverse {A B : TopCat.{0}} {f : A ⟶ B} (g : B ⟶ A)
    (hfg : f ≫ g = 𝟙 A) (hgf : g ≫ f = 𝟙 B) (hf : IsProperMap f) (j : ℤ) :
    Function.Bijective (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f hf j) := by
  have hg : IsProperMap g := (TopCat.homeoOfIso ⟨g, f, hgf, hfg⟩).isProperMap
  refine Function.bijective_iff_has_inverse.mpr
    ⟨borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) g hg j, fun a ↦ ?_, fun b ↦ ?_⟩
  · exact (borelMooreHomology.pushforward_comp_apply ℚ f g hf hg (hg.comp hf) j a).trans
      (borelMooreHomology.pushforward_id_apply' ℚ _ _ hfg j a)
  · exact (borelMooreHomology.pushforward_comp_apply ℚ g f hg hf (hf.comp hg) j b).trans
      (borelMooreHomology.pushforward_id_apply' ℚ _ _ hgf j b)

/-- An isomorphism of complex schemes carries the fundamental class `[closure {x}]` to
`[closure {φ x}]`: the cycle class of a point commutes with proper push-forward, with residue
degree one along an isomorphism, and the realization `X^an ≃ X(ℂ)` commutes with `φ`. -/
private lemma pushforward_fundamentalClass (φ : X ≅ Y)
    (hφ : φ.hom ≫ (Y ↘ Spec (.of ℂ)) = X ↘ Spec (.of ℂ))
    (hp : IsProperMap (ComplexPoints.analyticMap φ.hom hφ)) (r : ℕ) (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = r)
    (hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Y ↘ Spec (.of ℂ)) (φ.hom.base x) = r) :
    borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (ComplexPoints.analyticMap φ.hom hφ) hp
        (2 * r : ℕ) (fundamentalClass x hx) = fundamentalClass (φ.hom.base x) hy := by
  have : φ.hom.IsOver (Spec (.of ℂ)) := ⟨hφ⟩
  have key := MMP.Chow.pushforward_pointCycleClass ℚ φ.hom x hx
  rw [MMP.Chow.pointCycleClassOrZero, dite_cond_eq_true (eq_true hy),
    Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion, Nat.cast_one, one_smul] at key
  rw [fundamentalClass_eq, fundamentalClass_eq, ← key,
    borelMooreHomology.pushforward_comp_apply (R := ℚ) (hfg := hp.comp
      ComplexPoints.homeomorphUnderlyingSpace.symm.isProperMap),
    borelMooreHomology.pushforward_comp_apply (R := ℚ) (hfg :=
      ComplexPoints.homeomorphUnderlyingSpace.symm.isProperMap.comp
        (UnderlyingSpace.isProperMap_map (K := ℂ) φ.hom))]
  exact borelMooreHomology.pushforward_apply_congr ℚ (by ext; rfl) _ _ _ _

omit [IsComplexScheme X] [IsComplexScheme Y] in
/-- An isomorphism over `ℂ` preserves the delta-dimension of points. -/
private lemma relativeDimension_iso (φ : X ≅ Y)
    (hφ : φ.hom ≫ (Y ↘ Spec (.of ℂ)) = X ↘ Spec (.of ℂ)) (x : X) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (Y ↘ Spec (.of ℂ)) (φ.hom.base x) =
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) x := by
  conv_rhs => rw [← hφ]
  exact (Stacks.Chow.relativeDimension_comp_isOpenImmersion _ _ _ _).symm

end MMP.Analytic.Internal.IndexdCycleRankIsomorphism

namespace MMP.Analytic

open MMP.Analytic.Internal.IndexdCycleRankIsomorphism in
/-- An isomorphism `φ : X ≅ Y` of complex schemes over `ℂ` induces, by proper push-forward
along its realization `X^an → Y^an`, an isomorphism `H^BM_k(X, ℚ) → H^BM_k(Y, ℚ)` in every
degree `k`, sending the fundamental class `[A]` of each `r`-dimensional subvariety
`A = closure {x}` to `[φ(A)] = [closure {φ x}]`; it maps the cycle span `cycleSpan X r` onto
`cycleSpan Y r`, and `cycleRank X r = cycleRank Y r`. -/
@[mmp "lem_mmp_indexd_cycle_rank_isomorphism"]
public theorem cycleRank_eq_of_iso (φ : X ≅ Y)
    (hφ : φ.hom ≫ (Y ↘ Spec (.of ℂ)) = X ↘ Spec (.of ℂ)) :
    let hp : IsProperMap (ComplexPoints.analyticMap φ.hom hφ) :=
      (Homeomorph.mk
        ⟨ComplexPoints.realize φ.hom hφ,
          ComplexPoints.realize φ.inv (by rw [← hφ, Iso.inv_hom_id_assoc]),
          fun x ↦ ComplexPoints.ext (by simp), fun y ↦ ComplexPoints.ext (by simp)⟩
        (ComplexPoints.continuous_realize φ.hom hφ)
        (ComplexPoints.continuous_realize φ.inv
          (by rw [← hφ, Iso.inv_hom_id_assoc]))).isProperMap
    (∀ k : ℕ, Function.Bijective
        (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
          (ComplexPoints.analyticMap φ.hom hφ) hp k)) ∧
      (∀ (r : ℕ) (x : X)
          (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (X ↘ Spec (.of ℂ)) x = r)
          (hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (Y ↘ Spec (.of ℂ)) (φ.hom.base x) = r),
        borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
            (ComplexPoints.analyticMap φ.hom hφ) hp (2 * r : ℕ) (fundamentalClass x hx) =
          fundamentalClass (φ.hom.base x) hy) ∧
      (∀ r : ℕ, (cycleSpan X r).map
          (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
            (ComplexPoints.analyticMap φ.hom hφ) hp (2 * r : ℕ)).hom = cycleSpan Y r) ∧
      ∀ r : ℕ, cycleRank X r = cycleRank Y r := by
  intro hp
  have hφ' : φ.inv ≫ (X ↘ Spec (.of ℂ)) = Y ↘ Spec (.of ℂ) := by
    rw [← hφ, Iso.inv_hom_id_assoc]
  have hbij (j : ℤ) := pushforward_bijective_of_inverse (ComplexPoints.analyticMap φ.inv hφ')
    (by ext x; change (x.hom ≫ _) ≫ _ = x.hom; simp)
    (by ext x; change (x.hom ≫ _) ≫ _ = x.hom; simp) hp j
  -- the push-forward, typed as a map of the Borel–Moore groups `cycleSpan` lives in
  let f (r : ℕ) : MMP.Analytic.borelMooreHomology (X ↘ Spec (.of ℂ)) (2 * r) →ₗ[ℚ]
      MMP.Analytic.borelMooreHomology (Y ↘ Spec (.of ℂ)) (2 * r) :=
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (ComplexPoints.analyticMap φ.hom hφ) hp (2 * r : ℕ)).hom
  have hspan (r : ℕ) : (cycleSpan X r).map (f r) = cycleSpan Y r := by
    rw [cycleSpan, cycleSpan, Submodule.map_span, ← Set.range_comp]
    congr 1
    ext c
    refine ⟨fun ⟨⟨x, hx⟩, hA⟩ ↦ ⟨⟨φ.hom.base x, (relativeDimension_iso φ hφ x).trans hx⟩,
      (pushforward_fundamentalClass φ hφ hp r x hx _).symm.trans hA⟩, ?_⟩
    rintro ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x, φ.hom.base x = y := ⟨φ.inv.base y, by simp⟩
    exact ⟨⟨x, (relativeDimension_iso φ hφ x).symm.trans hy⟩,
      pushforward_fundamentalClass φ hφ hp r x _ hy⟩
  refine ⟨fun k ↦ hbij k, pushforward_fundamentalClass φ hφ hp, hspan, fun r ↦ ?_⟩
  rw [cycleRank, cycleRank, ← hspan r]
  exact (Submodule.equivMapOfInjective (f r) (hbij _).1 _).finrank_eq

end MMP.Analytic

end

/-!
## A positive-dimensional variety contains a curve

Let `X` be a variety over a field `k` with `0 < dim X`. Then `X` contains an integral closed
subscheme of dimension one: take a chain of irreducible closed subsets of maximal (finite) length
`r ≥ 1`. Its second-smallest member is irreducible of dimension exactly one, and its generic
point `x` gives the integral closed subscheme `{x}⁻`.

### Main results

* `MMP.Mori.exists_topologicalKrullDim_curveSubschemeAt_eq_one`: a variety `X` over `k` with
  `0 < topologicalKrullDim X` has a point `x` with
  `topologicalKrullDim (MMP.Mori.curveSubschemeAt x) = 1`.

### Implementation notes

An integral closed subscheme of `X` is recorded by its generic point `x`. The subscheme is
`MMP.Mori.curveSubschemeAt x`, the reduced induced structure on the closure `{x}⁻`, and this is
how `MMP.Mori.IsProperCurve` records curves.
-/

section

universe u

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace MMP.Mori

namespace MMP.Mori.Internal.PositiveDimensionalVarietyContainsCurve

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Under an inducing map, the preimage of a preirreducible set contained in the range is
preirreducible. -/
private lemma isPreirreducible_preimage_of_subset_range {f : Y → X} (hf : IsInducing f)
    {V : Set X} (hV : IsPreirreducible V) (hVf : V ⊆ Set.range f) :
    IsPreirreducible (f ⁻¹' V) := by
  intro U₁ U₂ hU₁ hU₂ ⟨y₁, hy₁V, hy₁U⟩ ⟨y₂, hy₂V, hy₂U⟩
  obtain ⟨W₁, hW₁, rfl⟩ := hf.isOpen_iff.mp hU₁
  obtain ⟨W₂, hW₂, rfl⟩ := hf.isOpen_iff.mp hU₂
  obtain ⟨_, hzV, hz₁, hz₂⟩ := hV W₁ W₂ hW₁ hW₂ ⟨_, hy₁V, hy₁U⟩ ⟨_, hy₂V, hy₂U⟩
  obtain ⟨y, rfl⟩ := hVf hzV
  exact ⟨y, hzV, hz₁, hz₂⟩

/-- For a closed embedding `f : Y → X` with image the irreducible closed set `c`, the irreducible
closed subsets of `Y` are order isomorphic, via closure of the image, to those of `X` below `c`. -/
private noncomputable def orderIsoIicOfIsClosedEmbedding {f : Y → X} (hf : IsClosedEmbedding f)
    (c : IrreducibleCloseds X) (hc : Set.range f = c) :
    IrreducibleCloseds Y ≃o Set.Iic c where
  toFun T := ⟨.map f hf.continuous T,
    closure_minimal ((Set.image_subset_range _ _).trans hc.le) c.isClosed⟩
  invFun V :=
    { carrier := f ⁻¹' V
      isIrreducible' := by
        have hV : (V : Set X) ⊆ Set.range f := hc ▸ V.2
        refine ⟨?_, isPreirreducible_preimage_of_subset_range hf.isInducing
          V.1.isIrreducible.isPreirreducible hV⟩
        obtain ⟨x, hx⟩ := V.1.isIrreducible.nonempty
        obtain ⟨y, rfl⟩ := hV hx
        exact ⟨y, hx⟩
      isClosed' := V.1.isClosed.preimage hf.continuous }
  left_inv T := IrreducibleCloseds.ext <| by
    simp [← hf.isInducing.closure_eq_preimage_closure_image, T.isClosed.closure_eq]
  right_inv V := Subtype.ext <| IrreducibleCloseds.ext <| by
    change closure (f '' (f ⁻¹' V)) = V
    rw [Set.image_preimage_eq_of_subset (hc ▸ V.2), V.1.isClosed.closure_eq]
  map_rel_iff' {A B} := by
    refine ⟨fun h => ?_, fun h => IrreducibleCloseds.map_mono hf.continuous h⟩
    change (A : Set Y) ⊆ B
    rw [← A.isClosed.closure_eq, ← B.isClosed.closure_eq,
      hf.isInducing.closure_eq_preimage_closure_image,
      hf.isInducing.closure_eq_preimage_closure_image (B : Set Y)]
    exact Set.preimage_mono h

/-- The dimension of a closed embedded space is the height of its image among the irreducible
closed subsets. -/
private lemma topologicalKrullDim_eq_height {f : Y → X} (hf : IsClosedEmbedding f)
    {c : IrreducibleCloseds X} (hc : Set.range f = c) :
    topologicalKrullDim Y = Order.height c := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (orderIsoIicOfIsClosedEmbedding hf c hc),
    Order.height_eq_krullDim_Iic]

end Topology

/-- A well-founded order of positive dimension has an element of height one. -/
private lemma exists_height_eq_one {α : Type*} [PartialOrder α] [WellFoundedLT α]
    (h : 0 < Order.krullDim α) : ∃ c : α, Order.height c = 1 := by
  obtain ⟨a, b, hab⟩ := Order.krullDim_pos_iff.mp h
  obtain ⟨c, hc, hmin⟩ := wellFounded_lt.has_min {y : α | 1 ≤ Order.height y}
    ⟨b, by simpa [ENat.one_le_iff_ne_zero] using not_isMin_of_lt hab⟩
  have : Minimal (fun y => ((1 : ℕ) : ℕ∞) ≤ Order.height y) c :=
    minimal_iff_forall_lt.mpr ⟨hc, fun y hyc hy => hmin y hy hyc⟩
  exact ⟨c, Order.height_eq_coe_iff_minimal_le_height.mpr this⟩

end MMP.Mori.Internal.PositiveDimensionalVarietyContainsCurve

namespace MMP.Mori

open MMP.Mori.Internal.PositiveDimensionalVarietyContainsCurve in
/-- A variety over a field of positive dimension contains an integral closed subscheme of
dimension one: the closure `{x}⁻` of some point `x`, with its reduced induced structure. -/
@[mmp "lem_mmp_positive_dimensional_variety_contains_curve"]
public theorem exists_topologicalKrullDim_curveSubschemeAt_eq_one {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsVariety k sX)
    (hdim : 0 < topologicalKrullDim X) :
    ∃ x : X, topologicalKrullDim (curveSubschemeAt x) = 1 := by
  have : QuasiCompact sX := hX.toQuasiCompact
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  have : WellFoundedLT (IrreducibleCloseds X) :=
    StrictMono.wellFoundedLT (f := fun s : IrreducibleCloseds X => (⟨s, s.isClosed⟩ : Closeds X))
      fun _ _ h => h
  obtain ⟨c, hc⟩ := exists_height_eq_one hdim
  refine ⟨c.isIrreducible.genericPoint, ?_⟩
  rw [topologicalKrullDim_eq_height
    (IsClosedImmersion.isClosedEmbedding (curveSubschemeAtι _)), hc]
  · rfl
  simp only [curveSubschemeAtι, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    c.isIrreducible.isGenericPoint_genericPoint_closure.def, c.isClosed.closure_eq]

end MMP.Mori

end
