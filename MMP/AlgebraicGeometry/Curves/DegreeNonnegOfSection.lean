module
public import MMP.AlgebraicGeometry.Curves.LineBundleDegree

/-!
# A line bundle with a non-zero global section has non-negative degree

Let `C` be a projective curve over a field `k` and `L` a line bundle on `C`. If `L` has a
non-zero global section `s ∈ H⁰(C, L)`, then `deg_C L ≥ 0`.

The germ `s_η` of `s` at the generic point is non-zero, because a section of an invertible module
on an integral scheme whose generic germ vanishes is zero. At a point `p`, the germ of a
trivializing basis section is a generator `σ` of `L_p`, and `s_p = a σ` with `a ∈ 𝒪_{p,C}`. So
`s_η = a σ_η` and `e_p(s_η) = e_p(a) = dim_k 𝒪_{p,C} / a 𝒪_{p,C} ≥ 0`. Since the degree does not
depend on the chosen generic section, `deg_C L = Σ_p e_p(s_η) ≥ 0`.

## Main results

* `MMP.Resolution.degree_nonneg_of_ne_zero`: `0 ≤ deg_C L` when `H⁰(C, L) ≠ 0`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.20, p. 19
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace MMP.Resolution

section Semilocal

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- The semi-local ring of a finite nonempty set of points inside an affine open of a curve has
fraction field `k(C)` and finite colength. -/
private theorem semilocalRing_isFractionRing_finiteColength_of_affine [IsIntegral C]
    (sC : C ⟶ Spec (.of k)) [LocallyOfFiniteType sC]
    (hdim : topologicalKrullDim C = 1) (P : Finset C) (hP : P.Nonempty)
    (U : C.Opens) (hU : IsAffineOpen U) (hPU : (P : Set C) ⊆ U) :
    IsFractionRing (semilocalRing P) C.functionField ∧
      letI := semilocalRingAlgebra sC P
      IsFiniteColength k (semilocalRing P) := by
  classical
  have : Nonempty U := hP.elim fun p₀ hp₀ => ⟨⟨p₀, hPU hp₀⟩⟩
  have hfr : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  let q : C → Ideal Γ(C, U) := fun p =>
    if h : p ∈ U then (hU.primeIdealOf ⟨p, h⟩).asIdeal else ⊤
  have hqp : ∀ p (h : p ∈ U), q p = (hU.primeIdealOf ⟨p, h⟩).asIdeal := fun p h =>
    dif_pos h
  have hq : ∀ p ∈ P, (q p).IsPrime := fun p hp => hqp p (hPU hp) ▸ inferInstance
  have hloc := fun p (hp : p ∈ P) =>
    mem_range_algebraMap_stalk_iff hU (hPU hp) (hqp p (hPU hp))
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

/-- The local ring `𝒪_{p,C}` of a point of a curve, as the semi-local ring of `{p}`, has fraction
field `k(C)` and finite colength. -/
private theorem semilocalRing_singleton_isFractionRing_finiteColength (sC : C ⟶ Spec (.of k))
    [MMP.Mori.IsCurve k sC] (p : C) :
    IsFractionRing (semilocalRing {p}) C.functionField ∧
      letI := semilocalRingAlgebra sC {p}
      IsFiniteColength k (semilocalRing {p}) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  exact semilocalRing_isFractionRing_finiteColength_of_affine sC
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := sC)) {p}
    (Finset.singleton_nonempty p) U hU (by simpa using hpU)

/-- **Kollár 1.20 with `s₂ = 1`.** In a `k`-algebra `R` of finite colength with fraction field
`K`, an element `r` with non-zero image in `K` has `e_R(r) = dim_k R / rR ≥ 0`. -/
private theorem eMultFrac_algebraMap_nonneg {R K : Type*} [CommRing R] [Algebra k R]
    [CommRing K] [IsDomain K] [Algebra R K] [IsFractionRing R K] (hR : IsFiniteColength k R)
    {r : R} (hr : algebraMap R K r ≠ 0) : 0 ≤ eMultFrac k K (algebraMap R K r) (R := R) := by
  have := (IsFractionRing.injective R K).isDomain (algebraMap R K)
  rw [(Kollar.eMultFrac_eq_of_eq_mul k K hR (s₁ := r) (s₂ := 1)
    (mem_nonZeroDivisors_of_ne_zero (by rintro rfl; simp at hr)) (one_mem _) (by simp)).2]
  simp [eMult, Module.finrank_zero_of_subsingleton]

/-- A non-zero regular function `a ∈ 𝒪_{p,C}` has `e_p(a) ≥ 0`. -/
private theorem eMultAt_singleton_algebraMap_nonneg (sC : C ⟶ Spec (.of k))
    [MMP.Mori.IsCurve k sC] (p : C) (a : C.presheaf.stalk p)
    (ha : algebraMap (C.presheaf.stalk p) C.functionField a ≠ 0) :
    0 ≤ eMultAt sC {p} (algebraMap (C.presheaf.stalk p) C.functionField a) := by
  have hmem : algebraMap (C.presheaf.stalk p) C.functionField a ∈ semilocalRing {p} := by
    simp only [semilocalRing, Subring.mem_iInf, Finset.mem_singleton]
    rintro q rfl
    exact ⟨a, rfl⟩
  obtain ⟨hfr, hfc⟩ := semilocalRing_singleton_isFractionRing_finiteColength sC p
  let := semilocalRingAlgebra sC {p}
  have e : algebraMap (C.presheaf.stalk p) C.functionField a =
      algebraMap (semilocalRing {p}) C.functionField ⟨_, hmem⟩ := rfl
  unfold eMultAt
  rw [e] at ha ⊢
  exact eMultFrac_algebraMap_nonneg hfc ha

end Semilocal

section Torsion

variable {X : Scheme.{u}} (M : X.Modules) {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V)

/-- The germ of the basis section of a trivialization is torsion-free: `r • b_x = 0` forces
`r = 0`. -/
private theorem eq_zero_of_smul_germ_basis_eq_zero {x : X} (hxV : x ∈ V) :
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
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
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

end Torsion

section Generic

variable {C : Scheme.{u}} [IsIntegral C] (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L]

/-- A non-zero global section of an invertible module on an integral scheme has non-zero germ at
the generic point. -/
private theorem germ_genericPoint_ne_zero (s : L.presheaf.obj (op ⊤)) (hs : s ≠ 0) :
    (L.presheaf.germ ⊤ (genericPoint C) trivial).hom s ≠ 0 := by
  intro h0
  apply hs
  refine TopCat.Presheaf.section_ext ⟨L.presheaf, L.isSheaf⟩ ⊤ s 0 fun x hx => ?_
  obtain ⟨V, hxV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at L x
  have hηV : genericPoint C ∈ V :=
    ((genericPoint_spec C).mem_open_set_iff V.isOpen).2 ⟨x, Set.mem_univ _, hxV⟩
  have hη := Stacks.SectionProduct.Γgerm_eq_smul_germ_basis t s hηV
  have hf : Stacks.NonvanishingOpen.trivTop t s = 0 := by
    apply germ_injective_of_isIntegral C (genericPoint C) hηV
    rw [map_zero]
    refine eq_zero_of_smul_germ_basis_eq_zero L t hηV _ ?_
    rw [← hη]
    exact h0
  have hx' := Stacks.SectionProduct.Γgerm_eq_smul_germ_basis t s hxV
  rw [hf, map_zero, zero_smul] at hx'
  rw [map_zero]
  exact hx'

end Generic

/-- **The local multiplicities of a global section are non-negative.** If `s ∈ H⁰(C, L)` has
non-zero generic germ `s_η`, then `e_p(s_η) ≥ 0` at every point `p`: writing `s_p = a σ` with `σ`
the germ of a trivializing basis section, `e_p(s_η) = e_p(a) ≥ 0`. -/
private theorem sectionMult_germ_genericPoint_nonneg {k : Type u} [Field k] {C : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) (L : C.Modules) [MMP.Mori.IsCurve k sC]
    [Stacks.Ample.IsInvertibleModule C L] (s : L.presheaf.obj (op ⊤))
    (hs : (L.presheaf.germ ⊤ (genericPoint C) trivial).hom s ≠ 0) (p : C) :
    0 ≤ sectionMult sC L ((L.presheaf.germ ⊤ (genericPoint C) trivial).hom s) p := by
  let := stalkModule L p
  let := genericStalkModule L
  obtain ⟨V, hpV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at L p
  set τ := (L.presheaf.germ V p hpV).hom (Stacks.NonvanishingOpen.basis t)
  have hτ : IsStalkGenerator L p τ := eq_top_iff.2 fun z _ =>
    Submodule.mem_span_singleton.2
      ((Stacks.SectionProduct.exists_smul_germ_basis t hpV z).imp fun _ hr => hr.symm)
  set a := (C.presheaf.germ V p hpV).hom (Stacks.NonvanishingOpen.trivTop t s)
  have hsη : (L.presheaf.germ ⊤ (genericPoint C) trivial).hom s =
      algebraMap (C.presheaf.stalk p) C.functionField a • toGenericStalk L p τ := by
    have e : toGenericStalk L p ((L.presheaf.Γgerm p).hom s) =
        (L.presheaf.germ ⊤ (genericPoint C) trivial).hom s :=
      Stacks.ModuleStalkSpecialization.germ_stalkSpecializes_apply L (U := ⊤) (x := p) trivial _ s
    rw [← e, Stacks.SectionProduct.Γgerm_eq_smul_germ_basis t s hpV]
    exact Stacks.ModuleStalkSpecialization.stalkSpecializes_smul L _ a τ
  have ha0 : algebraMap (C.presheaf.stalk p) C.functionField a ≠ 0 := fun h =>
    hs (by rw [hsη, h, zero_smul])
  rw [← eMultAt_eq_sectionMult sC L _ τ hτ _ ha0 hsη]
  exact eMultAt_singleton_algebraMap_nonneg sC p a ha0

/-- **Kollár 1.20, p. 19.** On a projective curve `C` over a field `k`, a line bundle `L` with a
non-zero global section has non-negative degree `0 ≤ deg_C L`. -/
@[mmp "lem_kr1a_degree_nonneg_of_section"]
public theorem degree_nonneg_of_ne_zero {k : Type u} [Field k] {C : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) (L : C.Modules) [MMP.Mori.IsCurve k sC]
    [MMP.Mori.IsProjectiveVariety k sC] [Stacks.Ample.IsInvertibleModule C L]
    (s : L.presheaf.obj (op ⊤)) (hs : s ≠ 0) : 0 ≤ degree sC L := by
  have hsη := germ_genericPoint_ne_zero L s hs
  have hex : ∃ s' : L.presheaf.stalk (genericPoint C), s' ≠ 0 := ⟨_, hsη⟩
  rw [degree, dif_pos hex, degreeWRT_eq sC L hex.choose_spec hsη, degreeWRT,
    dif_pos (finite_sectionMult_ne_zero sC L _ hsη)]
  exact Finset.sum_nonneg fun p _ => sectionMult_germ_genericPoint_nonneg sC L s hsη p

end MMP.Resolution

end
