/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.CurveMultiplicity
public import MMP.AlgebraicGeometry.Curves.RationalFunctionDegree
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.RingTheory.ElementMultiplicity
public import MMP.AlgebraicGeometry.Resolution.Surface.SemilocalRing
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# The degree of a line bundle on a curve is well defined (Kollár 1.20)

For a line bundle `L` on a curve `C` and a rational section `s ∈ L_η`, the local multiplicity
`e_p(s)` does not depend on the generator of `L_p` used to compute it; on a projective curve it
is nonzero at only finitely many closed points, and the degree `deg_C(L, s) = ∑_p e_p(s)` does
not depend on `s ≠ 0` (two sections differ by a rational function, of degree `0` by Kollár
1.20.5).

## Main results

* `MMP.Resolution.eMultAt_eq_sectionMult`
* `MMP.Resolution.finite_sectionMult_ne_zero`
* `MMP.Resolution.degreeWRT_eq`

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.20, (1.20.6)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace MMP.Resolution

/-! ### Auxiliary lemmas -/

section Aux

variable {k : Type u} [Field k] {C : Scheme.{u}}

private theorem semilocalRing_isFractionRing_finiteColength_of_affine [IsIntegral C]
    (sC : C ⟶ Spec (.of k)) [LocallyOfFiniteType sC]
    (hdim : topologicalKrullDim C = 1) (P : Finset C) (hP : P.Nonempty)
    (U : C.Opens) (hU : IsAffineOpen U) (hPU : (P : Set C) ⊆ U) :
    IsFractionRing (semilocalRing P) C.functionField ∧
      letI := semilocalRingAlgebra sC P
      IsFiniteColength k (semilocalRing P) := by
  classical
  have hPU' : ∀ p ∈ P, p ∈ U := fun p hp => hPU hp
  have : Nonempty U := ⟨⟨_, hPU' _ hP.choose_spec⟩⟩
  have hfr : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  let q : C → Ideal Γ(C, U) := fun p =>
    if h : p ∈ U then (hU.primeIdealOf ⟨p, h⟩).asIdeal else ⊤
  have hqp : ∀ p (h : p ∈ U), q p = (hU.primeIdealOf ⟨p, h⟩).asIdeal := fun p h =>
    dif_pos h
  have hq : ∀ p ∈ P, (q p).IsPrime := fun p hp => hqp p (hPU' p hp) ▸ inferInstance
  have hloc := fun p (hp : p ∈ P) =>
    mem_range_algebraMap_stalk_iff hU (hPU' p hp) (hqp p (hPU' p hp))
  have hR : ∀ x : C.functionField, x ∈ semilocalRing P ↔ ∀ p ∈ P, ∃ a s : Γ(C, U), s ∉ q p ∧
      x * algebraMap Γ(C, U) C.functionField s = algebraMap Γ(C, U) C.functionField a := fun x => by
    simpa only [semilocalRing, Subring.mem_iInf] using forall₂_congr fun p hp => hloc p hp x
  let : Algebra k Γ(C, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appLE ⊤ U (by simp)).hom.toAlgebra
  have hft : Algebra.FiniteType k Γ(C, U) := by
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact (sC.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp h2
  have := krullDimLE_one_of_isAffineOpen hdim.le hU
  refine ⟨Semilocal.isFractionRing P q hq _ hR hP, ?_⟩
  let := semilocalRingAlgebra sC P
  refine fun r hr => Semilocal.finite_quotient_span_singleton P q hq _ hR k (fun c => ?_) hP r hr
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop ≫ C.presheaf.germ ⊤ _ _).hom c =
    (((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appLE ⊤ U _) ≫ C.germToFunctionField U).hom c
  congr 2
  simp only [Scheme.Hom.appLE, Scheme.germToFunctionField, Category.assoc,
    TopCat.Presheaf.germ_res]
  rfl

/-- The semi-local ring of a single point of a curve has fraction field `k(C)` and finite
colength. -/
private theorem semilocalRing_singleton_properties (sC : C ⟶ Spec (.of k)) [MMP.Mori.IsCurve k sC]
    (p : C) :
    IsFractionRing (semilocalRing {p}) C.functionField ∧
      letI := semilocalRingAlgebra sC {p}
      IsFiniteColength k (semilocalRing {p}) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  exact semilocalRing_isFractionRing_finiteColength_of_affine sC
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := sC)) {p}
    (Finset.singleton_nonempty p) U hU (by simpa using hpU)

private theorem eMultAt_singleton_mul (sC : C ⟶ Spec (.of k)) [MMP.Mori.IsCurve k sC] (p : C)
    {f g : C.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    eMultAt sC {p} (f * g) = eMultAt sC {p} f + eMultAt sC {p} g := by
  obtain ⟨hfr, hfc⟩ := semilocalRing_singleton_properties sC p
  let := semilocalRingAlgebra sC {p}
  unfold eMultAt
  exact Kollar.eMultFrac_mul k C.functionField hfc (Ne.isUnit hf) (Ne.isUnit hg)

private lemma eMult_eq_zero_of_isUnit {R : Type*} [CommRing R] [Algebra k R] {r : R}
    (hr : IsUnit r) : eMult k r = 0 := by
  unfold eMult
  rw [Ideal.span_singleton_eq_top.2 hr]
  exact Module.finrank_zero_of_subsingleton

private lemma eMultFrac_algebraMap_of_isUnit {R K : Type*} [CommRing R] [Algebra k R] [CommRing K]
    [Algebra R K] [IsFractionRing R K] (hR : IsFiniteColength k R) {r : R} (hr : IsUnit r) :
    eMultFrac k K (algebraMap R K r) (R := R) = 0 := by
  rw [(Kollar.eMultFrac_eq_of_eq_mul k K hR (s₁ := r) (s₂ := 1) hr.mem_nonZeroDivisors
    isUnit_one.mem_nonZeroDivisors (by simp)).2, eMult_eq_zero_of_isUnit hr,
    eMult_eq_zero_of_isUnit isUnit_one]
  rfl

private lemma isUnit_mk_of_inv_mem {K : Type*} [Field K] (S : Subring K) {x : K} (hx : x ∈ S)
    (hx' : x⁻¹ ∈ S) (h0 : x ≠ 0) : IsUnit (⟨x, hx⟩ : S) :=
  IsUnit.of_mul_eq_one (⟨x⁻¹, hx'⟩ : S) (Subtype.ext (mul_inv_cancel₀ h0))

private theorem eMultAt_singleton_algebraMap_of_isUnit (sC : C ⟶ Spec (.of k))
    [MMP.Mori.IsCurve k sC]
    (p : C) {u : C.presheaf.stalk p} (hu : IsUnit u) :
    eMultAt sC {p} (algebraMap (C.presheaf.stalk p) C.functionField u) = 0 := by
  have hmem : ∀ v : C.presheaf.stalk p,
      algebraMap (C.presheaf.stalk p) C.functionField v ∈ semilocalRing {p} := by
    intro v
    simp only [semilocalRing, Subring.mem_iInf, Finset.mem_singleton]
    rintro q rfl
    exact ⟨v, rfl⟩
  have hu' := hu.map (algebraMap (C.presheaf.stalk p) C.functionField)
  have h0 : algebraMap (C.presheaf.stalk p) C.functionField u ≠ 0 := hu'.ne_zero
  have hinv : (algebraMap (C.presheaf.stalk p) C.functionField u)⁻¹ ∈ semilocalRing {p} := by
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have : (algebraMap (C.presheaf.stalk p) C.functionField u)⁻¹ =
        algebraMap (C.presheaf.stalk p) C.functionField v := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← RingHom.map_mul, hv, RingHom.map_one]
    exact this ▸ hmem v
  obtain ⟨hfr, hfc⟩ := semilocalRing_singleton_properties sC p
  let := semilocalRingAlgebra sC {p}
  unfold eMultAt
  exact eMultFrac_algebraMap_of_isUnit hfc
    (isUnit_mk_of_inv_mem (semilocalRing {p}) (hmem u) hinv h0) (K := C.functionField)

end Aux

private theorem two_le_krullDim_of_lt {P : Type*} [Preorder P] {a b c : P} (hab : a < b)
    (hbc : b < c) :
    (2 : WithBot ℕ∞) ≤ Order.krullDim P := by
  let s : LTSeries P := ⟨2, ![a, b, c], fun i => by fin_cases i <;> simpa⟩
  exact Order.LTSeries.length_le_krullDim s

private theorem finite_closedPoints_of_isClosed {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] [IrreducibleSpace X] (hdim : topologicalKrullDim X = 1) {Z : Set X}
    (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) : {x | IsClosed ({x} : Set X) ∧ x ∈ Z}.Finite := by
  classical
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine (hSf.image fun t =>
    if h : t ∈ S then (hSi t h).genericPoint else Classical.arbitrary X).subset ?_
  rintro x ⟨hx, t, htS, hxt⟩
  refine ⟨t, htS, ?_⟩
  simp only [htS, dite_true]
  have hw := (hSi t htS).isGenericPoint_genericPoint_closure
  rw [(hSc t htS).closure_eq] at hw
  set w := (hSi t htS).genericPoint
  by_contra hne
  have htU : t ≠ Set.univ := fun h =>
    hZne (Set.eq_univ_of_univ_subset (h ▸ Set.subset_sUnion_of_mem htS))
  let A : IrreducibleCloseds X := ⟨{x}, isIrreducible_singleton, hx⟩
  let B : IrreducibleCloseds X := ⟨t, hSi t htS, hSc t htS⟩
  have hAB : A < B := by
    refine lt_of_le_of_ne (fun y hy => ?_) fun h => hne ?_
    · change y ∈ ({x} : Set X) at hy
      rw [hy]
      exact hxt
    · change w ∈ (A : Set X)
      rw [h]
      exact hw.mem
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hBT : B < T := lt_of_le_of_ne (fun y _ => Set.mem_univ y) fun h =>
    htU (by simpa [B, T] using congrArg (fun s : IrreducibleCloseds X => (s : Set X)) h)
  have := two_le_krullDim_of_lt hAB hBT
  rw [← topologicalKrullDim, hdim] at this
  exact absurd this (by decide)

section Triv

variable {X : Scheme.{u}} (M : X.Modules) {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V)

private theorem smul_germ_basis_eq_zero {x : X} (hxV : x ∈ V) :
    letI := stalkModule M x
    ∀ r : X.presheaf.stalk x,
      r • (M.presheaf.germ V x hxV).hom (Stacks.NonvanishingOpen.basis t) = 0 → r = 0 := by
  intro r hr
  obtain ⟨W, hxW, c, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  have hxVW : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  set c' : Γ(X, V ⊓ W) := X.presheaf.map (homOfLE inf_le_right).op c with hc'
  set b' : Γ(M, V ⊓ W) := M.presheaf.map (homOfLE inf_le_left).op
    (Stacks.NonvanishingOpen.basis t) with hb'
  have hgerm : (M.presheaf.germ (V ⊓ W) x hxVW).hom (c' • b') =
      (M.presheaf.germ (V ⊓ W) x hxVW).hom 0 := by
    rw [Stacks.ModuleStalk.germ_smul, hc', hb', TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply, map_zero]
    exact hr
  obtain ⟨W', hxW', i₁, i₂, he⟩ :=
    TopCat.Presheaf.germ_eq M.presheaf x hxVW hxVW _ _ hgerm
  have hi : i₁ = i₂ := Subsingleton.elim _ _
  subst hi
  have hzero : X.presheaf.map i₁.op c' = 0 := by
    have h1 := congrArg (Stacks.NonvanishingOpen.triv t (i₁ ≫ homOfLE inf_le_left)) he
    have h0 : Stacks.NonvanishingOpen.triv t (i₁ ≫ homOfLE inf_le_left)
        ((M.presheaf.map i₁.op) 0) = 0 := by
      rw [map_zero]
      exact map_zero (t.θ _ _)
    rw [h0] at h1
    rw [← h1, Scheme.Modules.map_smul, Stacks.NonvanishingOpen.triv_smul, hb',
      ← M.presheaf.map_comp_apply, ← op_comp, Stacks.NonvanishingOpen.triv_res_basis, mul_one]
  have : (X.presheaf.germ W x hxW).hom c =
      (X.presheaf.germ W' x hxW').hom (X.presheaf.map i₁.op c') := by
    rw [TopCat.Presheaf.germ_res_apply, hc', TopCat.Presheaf.germ_res_apply]
  rw [this, hzero, map_zero]

private theorem exists_eq_smul_germ_basis {x : X} (hxV : x ∈ V) :
    letI := stalkModule M x
    ∀ z : M.presheaf.stalk x, ∃ r : X.presheaf.stalk x,
      z = r • (M.presheaf.germ V x hxV).hom (Stacks.NonvanishingOpen.basis t) :=
  fun z => Stacks.SectionProduct.exists_smul_germ_basis t hxV z

end Triv

section Stalks

variable {C : Scheme.{u}} [IsIntegral C] (L : C.Modules)

private theorem toGenericStalk_smul (p : C) (a : C.presheaf.stalk p) (σ : L.presheaf.stalk p) :
    letI := stalkModule L p
    letI := genericStalkModule L
    toGenericStalk L p (a • σ) =
      algebraMap (C.presheaf.stalk p) C.functionField a • toGenericStalk L p σ :=
  Stacks.ModuleStalkSpecialization.stalkSpecializes_smul L _ a σ

private theorem genericPoint_mem_of_mem {V : C.Opens} {p : C} (hp : p ∈ V) :
    genericPoint C ∈ V :=
  ((genericPoint_spec C).mem_open_set_iff V.isOpen).2 ⟨p, Set.mem_univ _, hp⟩

private theorem toGenericStalk_germ {V : C.Opens} {p : C} (hp : p ∈ V) (m : Γ(L, V)) :
    toGenericStalk L p ((L.presheaf.germ V p hp).hom m) =
      (L.presheaf.germ V (genericPoint C) (genericPoint_mem_of_mem hp)).hom m :=
  Stacks.ModuleStalkSpecialization.germ_stalkSpecializes_apply L hp _ m

variable [Stacks.Ample.IsInvertibleModule C L]

/-- For a generator `τ` of `L_p`, `τ ≠ 0` in `L_η` and every element of `L_η` is a multiple of
`τ`. -/
private theorem toGenericStalk_generator {p : C} {τ : L.presheaf.stalk p}
    (hτ : IsStalkGenerator L p τ) :
    letI := genericStalkModule L
    toGenericStalk L p τ ≠ 0 ∧
      ∀ s : L.presheaf.stalk (genericPoint C), ∃ φ : C.functionField,
        s = φ • toGenericStalk L p τ := by
  let := stalkModule L p
  let := genericStalkModule L
  obtain ⟨V, hpV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at L p
  have hη := genericPoint_mem_of_mem hpV
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1
    (hτ ▸ Submodule.mem_top (x := (L.presheaf.germ V p hpV).hom (Stacks.NonvanishingOpen.basis t)))
  have hgη : (L.presheaf.germ V (genericPoint C) hη).hom (Stacks.NonvanishingOpen.basis t) =
      algebraMap (C.presheaf.stalk p) C.functionField a • toGenericStalk L p τ := by
    rw [← toGenericStalk_germ L hpV, ← ha, toGenericStalk_smul]
  refine ⟨fun h0 => ?_, fun s => ?_⟩
  · rw [h0, smul_zero] at hgη
    have := smul_germ_basis_eq_zero L t hη 1 (by rw [hgη]; exact smul_zero _)
    exact one_ne_zero this
  · obtain ⟨r, hr⟩ := exists_eq_smul_germ_basis L t hη s
    refine ⟨r * algebraMap (C.presheaf.stalk p) C.functionField a, ?_⟩
    rw [mul_smul, ← hgη]
    exact hr

omit [IsIntegral C] in
/-- Two generators of `L_p` differ by a unit of `𝒪_{C,p}`. -/
private theorem exists_isUnit_smul_eq {p : C} {σ τ : L.presheaf.stalk p}
    (hσ : IsStalkGenerator L p σ) (hτ : IsStalkGenerator L p τ) :
    letI := stalkModule L p
    ∃ c : C.presheaf.stalk p, IsUnit c ∧ σ = c • τ := by
  let := stalkModule L p
  obtain ⟨V, hpV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at L p
  set g := (L.presheaf.germ V p hpV).hom (Stacks.NonvanishingOpen.basis t)
  have key : ∀ ρ : L.presheaf.stalk p, IsStalkGenerator L p ρ →
      ∃ a : C.presheaf.stalk p, IsUnit a ∧ ρ = a • g := by
    intro ρ hρ
    obtain ⟨a, ha⟩ := exists_eq_smul_germ_basis L t hpV ρ
    obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.1 (hρ ▸ Submodule.mem_top (x := g))
    refine ⟨a, IsUnit.of_mul_eq_one x ?_, ha⟩
    have : (x * a - 1) • g = 0 := by
      rw [sub_smul, mul_smul, ← ha, hx, one_smul, sub_self]
    rw [mul_comm]
    exact sub_eq_zero.1 (smul_germ_basis_eq_zero L t hpV _ this)
  obtain ⟨a, ha, rfl⟩ := key σ hσ
  obtain ⟨b, hb, rfl⟩ := key τ hτ
  refine ⟨a * ↑hb.unit⁻¹, ha.mul (Units.isUnit _), ?_⟩
  rw [mul_smul, smul_smul (↑hb.unit⁻¹ : C.presheaf.stalk p) b, IsUnit.val_inv_mul, one_smul]

omit [IsIntegral C] [Stacks.Ample.IsInvertibleModule C L] in
/-- The germ of the basis section of a trivialization generates the stalk. -/
private theorem isStalkGenerator_germ_basis {V : C.Opens}
    (t : Stacks.SheafDescent.Trivialization C.presheaf L.val V) {p : C} (hpV : p ∈ V) :
    IsStalkGenerator L p ((L.presheaf.germ V p hpV).hom (Stacks.NonvanishingOpen.basis t)) := by
  let := stalkModule L p
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨r, hr⟩ := exists_eq_smul_germ_basis L t hpV z
  exact Submodule.mem_span_singleton.2 ⟨r, hr.symm⟩

omit [IsIntegral C] in
private theorem exists_isStalkGenerator (p : C) :
    ∃ τ, IsStalkGenerator L p τ := by
  obtain ⟨V, hpV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at L p
  exact ⟨_, isStalkGenerator_germ_basis L t hpV⟩

end Stalks

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)

/-- **Kollár 1.20, p. 19: "we can identify the `𝒪_{p,C}`-module `L` with `𝒪_{p,C}`".** Let `L` be
a line bundle on a curve `C`, `s ∈ L_η`, `p` a point (closed, in the source), `τ` any generator of
`L_p` and `s = ψ τ` in `L_η` with `ψ ∈ k(C)^×`. Then `e_p(ψ) = e_p(s)`. Here
`e_p(ψ) = eMultAt sC {p} ψ` is Kollár's local multiplicity `e_R(ψ)` computed in the local ring
`R = 𝒪_{p,C}` (the semi-local ring `semilocalRing {p}`, through which `eMultAt` depends on `p`);
at a closed point it equals
`ord_p(ψ) · [κ(p) : k]` (`MMP.Resolution.eMultAt_singleton_eq`). -/
@[mmp "lem_kr1a_section_multiplicity_independent_of_generator"]
theorem eMultAt_eq_sectionMult [MMP.Mori.IsCurve k sC] [Stacks.Ample.IsInvertibleModule C L]
    {p : C} (s : L.presheaf.stalk (genericPoint C))
    (τ : L.presheaf.stalk p) (hτ : IsStalkGenerator L p τ) (ψ : C.functionField) (hψ : ψ ≠ 0)
    (hs : letI := genericStalkModule L; s = ψ • toGenericStalk L p τ) :
    eMultAt sC {p} ψ = sectionMult sC L s p := by
  let := stalkModule L p
  let := genericStalkModule L
  have hex : ∃ σ, IsStalkGenerator L p σ := ⟨τ, hτ⟩
  have hσ := hex.choose_spec
  obtain ⟨c, hc, hcσ⟩ := exists_isUnit_smul_eq L hσ hτ
  have hφex : ∃ φ : C.functionField, s = φ • toGenericStalk L p hex.choose :=
    (toGenericStalk_generator L hσ).2 s
  have hφ := hφex.choose_spec
  have hratio : sectionRatio L s p = hφex.choose := by
    unfold sectionRatio
    simp only [hex, hφex, ↓reduceDIte]
  have heq : hφex.choose * algebraMap (C.presheaf.stalk p) C.functionField c = ψ := by
    have h1 : s = (hφex.choose * algebraMap (C.presheaf.stalk p) C.functionField c) •
        toGenericStalk L p τ := by
      rw [mul_smul, ← toGenericStalk_smul, ← hcσ]
      exact hφ
    have h2 := h1.symm.trans hs
    by_contra hne
    have h3 : (hφex.choose * algebraMap (C.presheaf.stalk p) C.functionField c - ψ) •
        toGenericStalk L p τ = 0 := by
      rw [sub_smul, h2, sub_self]
    apply (toGenericStalk_generator L hτ).1
    rw [← inv_smul_smul₀ (sub_ne_zero.2 hne) (toGenericStalk L p τ), h3, smul_zero]
  have hc0 : algebraMap (C.presheaf.stalk p) C.functionField c ≠ 0 :=
    (hc.map (algebraMap (C.presheaf.stalk p) C.functionField)).ne_zero
  have hφ0 : hφex.choose ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at heq
    exact hψ heq.symm
  unfold sectionMult
  rw [hratio, ← heq, eMultAt_singleton_mul sC p hφ0 hc0,
    eMultAt_singleton_algebraMap_of_isUnit sC p hc, add_zero]

/-- **Kollár 1.20, p. 19, tacit: the sum (1.20.6) is finite.** For a line bundle `L` on a
projective curve `C` and `s ∈ L_η ∖ {0}`, the set of closed points `p` with `e_p(s) ≠ 0` is
finite. -/
@[mmp "lem_kr1a_section_multiplicity_finite_support"]
theorem finite_sectionMult_ne_zero [MMP.Mori.IsCurve k sC] [MMP.Mori.IsProjectiveVariety k sC]
    [Stacks.Ample.IsInvertibleModule C L] (s : L.presheaf.stalk (genericPoint C)) (hs : s ≠ 0) :
    {p : C | IsClosed ({p} : Set C) ∧ sectionMult sC L s p ≠ 0}.Finite := by
  let := genericStalkModule L
  obtain ⟨V, hηV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at L (genericPoint C)
  obtain ⟨ψ, hψ⟩ := exists_eq_smul_germ_basis L t hηV s
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    exact hs (by rw [hψ, zero_smul])
  obtain ⟨F, -, hF0, -⟩ := exists_finset_sum_eMultAt_eq_zero sC ψ hψ0
  have hVne : (V : Set C)ᶜ ≠ Set.univ := fun h => by
    have : genericPoint C ∈ (V : Set C)ᶜ := h ▸ Set.mem_univ _
    exact this hηV
  have : LocallyOfFiniteType sC := inferInstance
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have : IsNoetherian C := {}
  have hfin := finite_closedPoints_of_isClosed (X := C)
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := sC))
    V.isOpen.isClosed_compl hVne
  refine ((F.finite_toSet).union hfin).subset ?_
  rintro p ⟨hp, hne⟩
  by_cases hpV : p ∈ V
  · left
    by_contra hpF
    exact hne ((eMultAt_eq_sectionMult sC L s _ (isStalkGenerator_germ_basis L t hpV) ψ hψ0
      (by rwa [toGenericStalk_germ])).symm.trans (hF0 p hp hpF))
  · exact Or.inr ⟨hp, hpV⟩

/-- Multiplying a rational section by a nonzero rational function `h` adds `e_p(h)` to its
multiplicity at `p`. -/
theorem sectionMult_smul [MMP.Mori.IsCurve k sC] [Stacks.Ample.IsInvertibleModule C L]
    {s : L.presheaf.stalk (genericPoint C)} (hs : s ≠ 0) {h : C.functionField} (hh : h ≠ 0)
    (p : C) : letI := genericStalkModule L
    sectionMult sC L (h • s) p = eMultAt sC {p} h + sectionMult sC L s p := by
  let := genericStalkModule L
  obtain ⟨τ, hτ⟩ := exists_isStalkGenerator L p
  obtain ⟨φ, hφ⟩ := (toGenericStalk_generator L hτ).2 s
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    exact hs (by rw [hφ, zero_smul])
  rw [← eMultAt_eq_sectionMult sC L s τ hτ φ hφ0 hφ,
    ← eMultAt_eq_sectionMult sC L (h • s) τ hτ (h * φ) (mul_ne_zero hh hφ0)
      (by rw [hφ, smul_smul]),
    eMultAt_singleton_mul sC p hh hφ0]

/-- **Kollár 1.20, p. 19: "so `deg_C L` is well defined".** For a line bundle `L` on a projective
curve `C` and `s₁, s₂ ∈ L_η ∖ {0}`, `deg_C(L, s₁) = deg_C(L, s₂)`. -/
@[mmp "lem_kr1a_degree_of_line_bundle_independent_of_section"]
theorem degreeWRT_eq [MMP.Mori.IsCurve k sC] [MMP.Mori.IsProjectiveVariety k sC]
    [Stacks.Ample.IsInvertibleModule C L] {s₁ s₂ : L.presheaf.stalk (genericPoint C)}
    (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0) : degreeWRT sC L s₁ = degreeWRT sC L s₂ := by
  classical
  let := genericStalkModule L
  obtain ⟨V, hηV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at L (genericPoint C)
  obtain ⟨a₁, ha₁⟩ := exists_eq_smul_germ_basis L t hηV s₁
  obtain ⟨a₂, ha₂⟩ := exists_eq_smul_germ_basis L t hηV s₂
  have ha₁0 : a₁ ≠ 0 := by
    rintro rfl
    exact hs₁ (by rw [ha₁, zero_smul])
  have ha₂0 : a₂ ≠ 0 := by
    rintro rfl
    exact hs₂ (by rw [ha₂, zero_smul])
  set h : C.functionField := a₂ * a₁⁻¹ with hh
  have hh0 : h ≠ 0 := mul_ne_zero ha₂0 (inv_ne_zero ha₁0)
  have hs : s₂ = h • s₁ := by
    rw [ha₁, smul_smul, hh, mul_assoc, inv_mul_cancel₀ ha₁0, mul_one]
    exact ha₂
  have hloc : ∀ p : C, sectionMult sC L s₂ p = eMultAt sC {p} h + sectionMult sC L s₁ p :=
    fun p => by
      rw [hs]
      exact sectionMult_smul sC L hs₁ hh0 p
  have hf₁ := finite_sectionMult_ne_zero sC L s₁ hs₁
  have hf₂ := finite_sectionMult_ne_zero sC L s₂ hs₂
  obtain ⟨F, hFc, hF0, hFsum⟩ := exists_finset_sum_eMultAt_eq_zero sC h hh0
  unfold degreeWRT
  simp only [hf₁, hf₂, ↓reduceDIte]
  set T := hf₁.toFinset ∪ hf₂.toFinset ∪ F with hT
  have hTc : ∀ p ∈ T, IsClosed ({p} : Set C) := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · rcases Finset.mem_union.1 hp with hp | hp
      · exact ((Set.Finite.mem_toFinset _).1 hp).1
      · exact ((Set.Finite.mem_toFinset _).1 hp).1
    · exact hFc p hp
  have e₁ : ∑ p ∈ hf₁.toFinset, sectionMult sC L s₁ p = ∑ p ∈ T, sectionMult sC L s₁ p := by
    refine Finset.sum_subset (fun p hp => Finset.mem_union_left _ (Finset.mem_union_left _ hp))
      fun p hpT hp => ?_
    by_contra hne
    exact hp ((Set.Finite.mem_toFinset _).2 ⟨hTc p hpT, hne⟩)
  have e₂ : ∑ p ∈ hf₂.toFinset, sectionMult sC L s₂ p = ∑ p ∈ T, sectionMult sC L s₂ p := by
    refine Finset.sum_subset (fun p hp => Finset.mem_union_left _ (Finset.mem_union_right _ hp))
      fun p hpT hp => ?_
    by_contra hne
    exact hp ((Set.Finite.mem_toFinset _).2 ⟨hTc p hpT, hne⟩)
  have e₃ : ∑ p ∈ T, eMultAt sC {p} h = 0 := by
    rw [← hFsum]
    refine (Finset.sum_subset (fun p hp => Finset.mem_union_right _ hp) fun p hpT hp => ?_).symm
    exact hF0 p (hTc p hpT) hp
  rw [e₁, e₂, Finset.sum_congr rfl fun p _ => hloc p, Finset.sum_add_distrib, e₃,
    zero_add]

end MMP.Resolution
