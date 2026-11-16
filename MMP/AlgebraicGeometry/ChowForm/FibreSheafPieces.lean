module

public import MMP.AlgebraicGeometry.ChowForm.KoszulSheafData
public import MMP.RingTheory.Regular.KoszulTwo
public import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.FibreSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteOverFieldStalks
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection.Induction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse

/-!
# Sheaves and Koszul gluing on the fibres of a proper flat family

Local algebra on a scheme of dimension at most one, affine charts on pairs of linear forms,
cohomology and base change on the fibres of a proper flat family over an affine open of the base,
and the gluing of local solutions of the Koszul complex of a pair of linear forms with
coefficients in sheaves of modules.

## Main results

* `degree_eq_finsum_length`: the degree of an invertible sheaf on a proper curve is the sum, over
  the points of the curve, of the local lengths of the zero scheme of a section.
* `fibre_cohomology_of_basis`: if the sections over an affine open `V` of the base are free of
  rank `r` and the higher cohomology over `π⁻¹ V` vanishes, the same holds on every fibre over `V`.
* `finrank_diff_fibre`: on a fibre of dimension at most one, the drop of `h⁰` under the twist by
  `H` is the degree of `H` on the fundamental cycle of the fibre.
* `coeffMul_koszul_injective_and_exact`: the Koszul complex in coefficients of the pair `(∑ᵢ cᵢ uᵢ, ∑ᵢ cᵢ vᵢ)` with
  `c_{j₀} = 1` is injective on the left and exact in the middle.
* `coeff_glue`: on a quasi-compact open, the coefficient Koszul complex of sections is exact in the
  middle when it is so on every stalk.

## References

* [J. Kollár, *Rational curves on algebraic varieties*][Kollar1996], I.3
-/

@[expose] public section

universe u

namespace MMP.Chow.DeterminantCurveForm

open CategoryTheory AlgebraicGeometry

section FibreStalkAlgebra

open Opposite

/-- If a global section `σ` of an invertible sheaf `M` on a locally Noetherian scheme does not
vanish at any associated point, multiplying the germ of `σ` at `y` by elements of the local ring
is injective. -/
theorem injective_smul_germ_of_forall_assoc {X : Scheme.{u}} [IsLocallyNoetherian X] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (σ : Γ(M, ⊤))
    (h : ∀ x ∈ Stacks.Divisors.schemeAssociatedPoints X, x ∈ Stacks.Ample.nonvanishingLocus M σ)
    (y : X) :
    Function.Injective fun r : X.presheaf.stalk y => r • (M.presheaf.Γgerm y).hom σ := by
  let s : SheafOfModules.sections M := (Stacks.NonvanishingSpelling.sectionsEquiv X M).symm σ
  have hs : s.eval (op ⊤) = σ := by
    show M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op σ = σ
    rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id, M.presheaf.map_id]
    rfl
  haveI hinvM : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    ‹Stacks.Ample.IsInvertibleModule X M›
  have hreg := (Stacks.Divisors.isRegularSection_iff_forall_associatedPoint_notMem_maximalSmul M s).2
    (fun x hx => by rw [hs]; exact h x hx)
  have hinj := Stacks.AlgebraicGeometry.EmbeddedPoints.injective_stalkFunctor_map
    (Stacks.Divisors.smulHom M s) hreg y
  have hinj' : Function.Injective (Stacks.ModuleStalk.mapFun (Stacks.Divisors.smulHom M s) y) := hinj
  have := hinj'.comp (Stacks.Divisors.unitStalkLinearEquiv y).injective
  have e : (Stacks.ModuleStalk.mapFun (Stacks.Divisors.smulHom M s) y ∘
      (Stacks.Divisors.unitStalkLinearEquiv y)) = fun r => r • (M.presheaf.Γgerm y).hom σ := by
    funext r
    rw [Function.comp_apply, Stacks.Divisors.mapFun_smulHom_unitStalkLinearEquiv, hs]
  rwa [e] at this

/-- If `e` does not vanish at `y`, the coordinate of the germ of `σ` in the stalk basis given by
`e` is a unit if and only if `σ` does not vanish at `y`. -/
theorem isUnit_coord_iff {X : Scheme.{u}} (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]
    (σ e : Γ(M, ⊤)) {y : X} (he : y ∈ Stacks.Ample.nonvanishingLocus M e) :
    IsUnit ((Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus M e he).coord
      ((M.presheaf.Γgerm y).hom σ)) ↔ y ∈ Stacks.Ample.nonvanishingLocus M σ := by
  have hb := Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus M e he
  set c := hb.coord ((M.presheaf.Γgerm y).hom σ) with hc
  have hσ : (M.presheaf.Γgerm y).hom σ = c • (M.presheaf.Γgerm y).hom e :=
    (hb.smul_coord _).symm
  rw [Stacks.Ample.mem_nonvanishingLocus_iff, hσ, Stacks.ModuleStalk.smul_mem_maximalSmul_iff]
  have : (M.presheaf.Γgerm y).hom e ∉ Stacks.ModuleStalk.maximalSmul M y :=
    (Stacks.Ample.mem_nonvanishingLocus_iff M e y).1 he
  tauto

/-- If `σ` does not vanish at any associated point and `e` does not vanish at `y`, the coordinate
of the germ of `σ` in the stalk basis given by `e` is a non-zero-divisor of the local ring. -/
theorem coord_mem_nonZeroDivisors {X : Scheme.{u}} [IsLocallyNoetherian X] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (σ e : Γ(M, ⊤))
    (h : ∀ x ∈ Stacks.Divisors.schemeAssociatedPoints X, x ∈ Stacks.Ample.nonvanishingLocus M σ)
    {y : X} (he : y ∈ Stacks.Ample.nonvanishingLocus M e) :
    (Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus M e he).coord
      ((M.presheaf.Γgerm y).hom σ) ∈ nonZeroDivisors (X.presheaf.stalk y) := by
  have hb := Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus M e he
  set c := hb.coord ((M.presheaf.Γgerm y).hom σ) with hc
  have hσ : (M.presheaf.Γgerm y).hom σ = c • (M.presheaf.Γgerm y).hom e :=
    (hb.smul_coord _).symm
  have key : ∀ r : X.presheaf.stalk y, r * c = 0 → r = 0 := by
    intro r hr
    apply injective_smul_germ_of_forall_assoc M σ h y
    show r • (M.presheaf.Γgerm y).hom σ = (0 : X.presheaf.stalk y) • (M.presheaf.Γgerm y).hom σ
    rw [hσ, smul_smul, hr, zero_smul, zero_smul]
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun r hr => key r (by rwa [mul_comm]), key⟩

/-- On a locally Noetherian scheme of dimension at most one, the quotient of a local ring by a
non-zero-divisor has finite length. -/
theorem length_quotient_span_ne_top {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (y : X) {c : X.presheaf.stalk y}
    (hc : c ∈ nonZeroDivisors (X.presheaf.stalk y)) :
    Module.length (X.presheaf.stalk y) (X.presheaf.stalk y ⧸ Ideal.span {c}) ≠ ⊤ := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk y) := by
    rw [Ring.krullDimLE_iff]
    exact (le_iSup (fun z : X => ringKrullDim (X.presheaf.stalk z)) y).trans
      (by rw [← topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]; exact hdim)
  exact Module.length_ne_top_iff.2 (isFiniteLength_quotient_span_singleton (R := X.presheaf.stalk y) hc)

/-- The quotient `R ⧸ (c)` has length zero if and only if `c` is a unit. -/
theorem length_quotient_span_eq_zero_iff {R : Type*} [CommRing R] (c : R) :
    Module.length R (R ⧸ Ideal.span {c}) = 0 ↔ IsUnit c := by
  rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]

open TopologicalSpace in
/-- In a space of Krull dimension at most one, a point which is not the generic point of the
irreducible component through it is closed. -/
theorem isClosed_singleton_of_ne_genericPoint' {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] (hdim : topologicalKrullDim X ≤ 1) (z : X)
    (hz : z ≠ (isIrreducible_irreducibleComponent (x := z)).genericPoint) : IsClosed {z} := by
  set η := (isIrreducible_irreducibleComponent (x := z)).genericPoint
  have hη : IsGenericPoint η (irreducibleComponent z) :=
    isIrreducible_irreducibleComponent.isGenericPoint_genericPoint isClosed_irreducibleComponent
  let cl : X → IrreducibleCloseds X := fun x =>
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  by_contra hcl
  obtain ⟨w, hw, hwz⟩ : ∃ w ∈ closure ({z} : Set X), w ≠ z := by
    by_contra! h
    exact hcl (closure_subset_iff_isClosed.mp fun w hw => h w hw)
  have hzw : z ⤳ w := specializes_iff_mem_closure.mpr hw
  have hηz : η ⤳ z := hη.specializes mem_irreducibleComponent
  have h1 : cl w < cl z := by
    refine lt_of_le_of_ne (fun y hy => ?_) fun h => hwz ?_
    · exact specializes_iff_mem_closure.mp (hzw.trans (specializes_iff_mem_closure.mpr hy))
    · have h' : closure ({w} : Set X) = closure {z} := congrArg SetLike.coe h
      exact (hzw.antisymm (specializes_iff_mem_closure.mpr (h' ▸ subset_closure rfl))).eq.symm
  have h2 : cl z < cl η := by
    refine lt_of_le_of_ne (fun y hy => ?_) fun h => hz ?_
    · exact specializes_iff_mem_closure.mp (hηz.trans (specializes_iff_mem_closure.mpr hy))
    · have h' : closure ({z} : Set X) = closure {η} := congrArg SetLike.coe h
      exact (hηz.antisymm (specializes_iff_mem_closure.mpr (h' ▸ subset_closure rfl))).eq.symm
  let p : LTSeries (IrreducibleCloseds X) :=
    ((RelSeries.singleton _ (cl w)).snoc (cl z) h1).snoc (cl η)
      (by simp only [RelSeries.last_snoc]; exact h2)
  have hp : (p.length : WithBot ℕ∞) ≤ 1 := (Order.LTSeries.length_le_krullDim p).trans hdim
  have : p.length = 2 := rfl
  rw [this] at hp
  exact absurd hp (by decide)

open TopologicalSpace in
/-- On a Noetherian scheme, a closed subset consisting of closed points is finite. -/
theorem finite_of_isClosed_of_forall_isClosed {X : Scheme.{u}} [IsNoetherian X]
    {Z : Set X} (hZ : IsClosed Z) (hcl : ∀ z ∈ Z, IsClosed ({z} : Set X)) : Z.Finite := by
  obtain ⟨S, hS, hZS⟩ := NoetherianSpace.exists_finset_irreducible (⟨Z, hZ⟩ : Closeds X)
  have hZeq : Z = ⋃ k ∈ S, (k : Set X) := by
    have h : ((⟨Z, hZ⟩ : Closeds X) : Set X) = ((S.sup id : Closeds X) : Set X) :=
      congrArg (fun C : Closeds X => (C : Set X)) hZS
    rwa [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at h
  rw [hZeq]
  refine S.finite_toSet.biUnion fun k hk => ?_
  have hirr := hS ⟨k, hk⟩
  have hgen := hirr.isGenericPoint_genericPoint k.isClosed
  have hkZ : (k : Set X) ⊆ Z := hZeq ▸ Set.subset_biUnion_of_mem (u := fun k : Closeds X =>
    (k : Set X)) hk
  have hg := hcl _ (hkZ hgen.mem)
  refine (Set.finite_singleton hirr.genericPoint).subset fun y hy => ?_
  have hy' : y ∈ closure ({hirr.genericPoint} : Set X) := by rwa [hgen.def]
  rwa [hg.closure_eq] at hy'

/-- On a Noetherian scheme of dimension at most one, a closed subset containing no associated
point consists of finitely many closed points. -/
theorem finite_isClosed_of_disjoint_assoc {X : Scheme.{u}} [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hAss : ∀ z ∈ Z, z ∉ Stacks.Divisors.schemeAssociatedPoints X) :
    Z.Finite ∧ ∀ z ∈ Z, IsClosed ({z} : Set X) := by
  haveI : IsLocallyNoetherian X := ‹IsNoetherian X›.toIsLocallyNoetherian
  have hcl : ∀ z ∈ Z, IsClosed ({z} : Set X) := by
    intro z hz
    apply isClosed_singleton_of_ne_genericPoint' hdim z
    intro h
    apply hAss z hz
    have hg := mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent X
      (irreducibleComponent_mem_irreducibleComponents z)
      (isIrreducible_irreducibleComponent.isGenericPoint_genericPoint
        (isClosed_irreducibleComponent (x := z)))
    rwa [← h] at hg
  exact ⟨finite_of_isClosed_of_forall_isClosed hZ hcl, hcl⟩

end FibreStalkAlgebra

section FibreLocalLengths

open Opposite TopologicalSpace

/-- The stalk of the zero ideal sheaf is the zero ideal. -/
theorem stalk_bot_eq {X : Scheme.{u}} (y : X) : IdealSheafData.stalk (⊥ : X.IdealSheafData) y = ⊥ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  rw [IdealSheafData.stalk_eq_map_germ _ y ⟨U, hU⟩ hyU]
  exact Ideal.map_bot

/-- On a locally Noetherian scheme of dimension at most one, for a non-zero-divisor `c` of the
local ring at `y` which is not a unit, the length of `𝒪_{X,y} ⧸ (c)` is the sum, over the generic
points `η` of the irreducible components through `y`, of the length of `𝒪_{X,y} ⧸ ((c) + I_η)`
times the length of `𝒪_{X,η}`, where `I_η` is the ideal sheaf of the closure of `η`. -/
theorem length_quotient_eq_finsum_components {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (y : X) {c : X.presheaf.stalk y}
    (hc : c ∈ nonZeroDivisors (X.presheaf.stalk y)) (hcu : ¬ IsUnit c) :
    Module.length (X.presheaf.stalk y) (X.presheaf.stalk y ⧸ Ideal.span {c}) =
      ∑ᶠ η ∈ Stacks.Chow.componentGenericPointsThrough (⊥ : X.IdealSheafData) y,
        Module.length (X.presheaf.stalk y) (X.presheaf.stalk y ⧸
          (Ideal.span {c} ⊔ IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({η} : Set X))) y)) *
        Module.length (X.presheaf.stalk η) (X.presheaf.stalk η) := by
  have hdimR : ringKrullDim (X.presheaf.stalk y) = 1 := by
    have h1 : ringKrullDim (X.presheaf.stalk y) ≤ 1 :=
      (le_iSup (fun z : X => ringKrullDim (X.presheaf.stalk z)) y).trans
        (by rw [← topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]; exact hdim)
    have hc' : c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := hcu
    have h2 :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hc hc'
    haveI : Nontrivial (X.presheaf.stalk y ⧸ Ideal.span {c}) :=
      Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
    have h3 : 0 ≤ ringKrullDim (X.presheaf.stalk y ⧸ Ideal.span {c}) :=
      ringKrullDim_nonneg_of_nontrivial
    apply le_antisymm h1
    rw [← h2]
    calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
      _ ≤ _ := by gcongr
  have hreg : IsSMulRegular (X.presheaf.stalk y ⧸ (⊥ : Ideal (X.presheaf.stalk y))) c := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul] at hab
    rw [Ideal.Quotient.eq, Ideal.mem_bot] at hab ⊢
    have h0 : (a - b) * c = 0 := by rwa [sub_mul, mul_comm a, mul_comm b]
    exact (mem_nonZeroDivisors_iff.mp hc).2 _ h0
  have hdim' : ringKrullDim (X.presheaf.stalk y ⧸ (⊥ : Ideal (X.presheaf.stalk y))) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (X.presheaf.stalk y)), hdimR]
  have h02 := AlgebraicGeometry.length_quotient_span_sup_eq_sum_minimalPrimes c ⊥ hreg hdim'
  rw [sup_bot_eq] at h02
  rw [h02]
  refine finsum_mem_eq_of_bijOn (X.fromSpecStalk y) ?_ ?_
  · have := Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes (⊥ : X.IdealSheafData) y
    rwa [stalk_bot_eq] at this
  · intro q _
    congr 1
    · rw [Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk]
    · obtain ⟨y', hy'⟩ : ∃ y' : (⊥ : X.IdealSheafData).subscheme,
          (⊥ : X.IdealSheafData).subschemeι y' = X.fromSpecStalk y q :=
        ((ConcreteCategory.bijective_of_isIso (⊥ : X.IdealSheafData).subschemeι.base).2 _)
      have h := Stacks.Chow.length_localizedModule_quotient_idealStalk_eq_length_stalk
        (⊥ : X.IdealSheafData) q y' hy'.symm
      rw [stalk_bot_eq] at h
      rw [h, ← hy']
      haveI hι : IsIso (⊥ : X.IdealSheafData).subschemeι :=
        Scheme.instIsIsoSubschemeιBotIdealSheafData
      haveI hoι : IsOpenImmersion (⊥ : X.IdealSheafData).subschemeι :=
        @IsOpenImmersion.of_isIso _ _ _ hι
      haveI : IsIso ((⊥ : X.IdealSheafData).subschemeι.stalkMap y') :=
        @IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ _ hoι y'
      exact (Module.length_eq_of_ringEquiv
        (asIso ((⊥ : X.IdealSheafData).subschemeι.stalkMap y')).commRingCatIsoToRingEquiv).symm

/-- If `e` does not vanish at `y`, the stalk at `y` of the ideal sheaf of the zero scheme of `s`
is generated by the coordinate of the germ of `s` in the stalk basis given by `e`. -/
theorem stalk_zeroScheme_eq_span_coord {X : Scheme.{u}} (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (s e : Γ(M, ⊤)) {y : X}
    (he : y ∈ Stacks.Ample.nonvanishingLocus M e) :
    haveI : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
      ‹Stacks.Ample.IsInvertibleModule X M›
    IdealSheafData.stalk (zeroScheme X M s) y =
      Ideal.span {((Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus M e
        he).coord ((M.presheaf.Γgerm y).hom s))} := by
  haveI : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    ‹Stacks.Ample.IsInvertibleModule X M›
  have hb := Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus M e he
  obtain ⟨V, hyV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at M y
  obtain ⟨-, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen
  have hUV' : U ≤ V := hUV
  set a : Γ(X, U) := Stacks.NonvanishingOpen.triv t (homOfLE hUV')
    (M.presheaf.map (homOfLE le_top).op s) with ha
  have hideal : (zeroScheme X M s).ideal ⟨U, hU⟩ = Ideal.span {a} :=
    zeroScheme_ideal_of_trivialization X M s ⟨U, hU⟩ (t.θ U (homOfLE hUV')) a rfl
  set b := (M.presheaf.germ V y hyV).hom (Stacks.NonvanishingOpen.basis t) with hbdef
  have hs : (M.presheaf.Γgerm y).hom s = (X.presheaf.germ U y hyU).hom a • b := by
    have e1 := Stacks.SectionProduct.eq_triv_smul_res_basis t (homOfLE hUV')
      (M.presheaf.map (homOfLE le_top).op s)
    have h1 : (M.presheaf.Γgerm y).hom s =
        (M.presheaf.germ U y hyU).hom (M.presheaf.map (homOfLE le_top).op s) :=
      (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE le_top) y hyU s).symm
    rw [h1, e1, Scheme.Modules.germ_smul, TopCat.Presheaf.germ_res_apply]
  obtain ⟨c, hc⟩ := Stacks.SectionProduct.exists_smul_germ_basis t hyV ((M.presheaf.Γgerm y).hom e)
  have hcb : hb.coord b * c = 1 := by
    have h1 : hb.coord ((M.presheaf.Γgerm y).hom e) = 1 := by
      have := hb.coord_smul 1
      rwa [one_smul] at this
    have h2 : hb.coord (c • b) = 1 := by rwa [hbdef, ← hc]
    rw [map_smul, smul_eq_mul] at h2
    rwa [mul_comm]
  rw [IdealSheafData.stalk_eq_map_germ _ y ⟨U, hU⟩ hyU, hideal, Ideal.map_span,
    Set.image_singleton, hs, map_smul, smul_eq_mul]
  exact (Ideal.span_singleton_mul_right_unit (IsUnit.of_mul_eq_one _ hcb) _).symm

/-- If `R → A` is surjective with kernel `J`, the length of `A` over itself is the length of
`R ⧸ J` over `R`. -/
theorem length_self_eq_length_quotient' {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hs : Function.Surjective (algebraMap R A)) (J : Ideal R)
    (hJ : RingHom.ker (algebraMap R A) = J) :
    Module.length A A = Module.length R (R ⧸ J) := by
  rw [← Module.length_eq_of_surjective (S := R) (M := A) hs]
  have h : J = LinearMap.ker (Algebra.linearMap R A) := by
    rw [← hJ]; ext x; simp [RingHom.mem_ker]
  exact ((Submodule.quotEquivOfEq _ _ h).trans
    (LinearMap.quotKerEquivOfSurjective (Algebra.linearMap R A) hs)).length_eq.symm

/-- The length of the local ring at `z` of the closed subscheme cut out by `I` is the length of
`𝒪_{C,z} ⧸ I_z`. -/
theorem length_stalk_subscheme' {C : Scheme.{u}} (I : C.IdealSheafData) (z : I.subscheme) :
    Module.length (I.subscheme.presheaf.stalk z) (I.subscheme.presheaf.stalk z) =
      Module.length (C.presheaf.stalk (I.subschemeι z))
        (C.presheaf.stalk (I.subschemeι z) ⧸ IdealSheafData.stalk I (I.subschemeι z)) :=
  letI : Algebra _ _ := (I.subschemeι.stalkMap z).hom.toAlgebra
  length_self_eq_length_quotient' (I.subschemeι.stalkMap_surjective z) _
    (Stacks.Chow.ker_stalkMap_subschemeι_eq_stalk I z)

/-- Every residue field of a finite scheme over an algebraically closed field `k` has dimension
one over `k`. -/
theorem finrank_residueField_eq_one_of_isFinite {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsFinite g] (y : Y) :
    letI : Algebra k (Y.presheaf.stalk y) :=
      ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
    Module.finrank k (IsLocalRing.ResidueField (Y.presheaf.stalk y)) = 1 := by
  letI : Algebra k (Y.presheaf.stalk y) :=
    ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
  haveI : Module.Finite k (Y.presheaf.stalk y) := finite_stalk_of_isFinite_over_field k g y
  haveI : Module.Finite k (IsLocalRing.ResidueField (Y.presheaf.stalk y)) :=
    Module.Finite.of_surjective
      ((IsScalarTower.toAlgHom k (Y.presheaf.stalk y)
        (IsLocalRing.ResidueField (Y.presheaf.stalk y))).toLinearMap)
      IsLocalRing.residue_surjective
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := IsLocalRing.ResidueField (Y.presheaf.stalk y))
  rw [← (AlgEquiv.ofBijective (Algebra.ofId k _) hb).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-- For a global section `s` of an invertible sheaf `M` which does not vanish at the generic point
of a proper curve `C`, the degree of `M` on `C` is the sum, over the points `y` of `C`, of the
length of `𝒪_{X,y} ⧸ (I_C + I_{Z(s)})_y`. -/
theorem degree_eq_finsum_length {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (C : MMP.Mori.ProperCurve sX) (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (s : Γ(M, ⊤))
    (hs : C.point ∈ Stacks.Ample.nonvanishingLocus M s) :
    haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M :=
      ‹Stacks.Ample.IsInvertibleModule X M›
    haveI : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
      ‹Stacks.Ample.IsInvertibleModule X M›
    C.degree k M = ∑ᶠ y ∈ closure ({C.point} : Set X),
      ((Module.length (X.presheaf.stalk y) (X.presheaf.stalk y ⧸
        (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({C.point} : Set X))) y ⊔
          IdealSheafData.stalk (Stacks.Divisors.zeroScheme X M s) y))).toNat : ℤ) := by
  classical
  haveI hMp : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M :=
    ‹Stacks.Ample.IsInvertibleModule X M›
  haveI hMs : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    ‹Stacks.Ample.IsInvertibleModule X M›
  haveI : IsIntegral C.scheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X)) with hI
  set L := (Scheme.Modules.pullback C.ι).obj M with hL
  haveI hLinv : Stacks.Ample.IsInvertibleModule C.scheme L :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback C.ι M
  haveI hLs : SheafOfModules.IsInvertible C.scheme.sheaf.obj C.scheme.ringCatSheaf.property L :=
    hLinv
  set σ := pullbackGlobalSections C.ι M s with hσdef
  let sσ : SheafOfModules.sections L := (Stacks.NonvanishingSpelling.sectionsEquiv C.scheme L).symm σ
  have hsσ : sσ.eval (op ⊤) = σ := by
    show L.presheaf.map (homOfLE (le_top : (⊤ : C.scheme.Opens) ≤ ⊤)).op σ = σ
    rw [show (homOfLE (le_top : (⊤ : C.scheme.Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id,
      L.presheaf.map_id]
    rfl
  have hσ0 : σ ≠ 0 := by
    intro h0
    obtain ⟨w, hw⟩ : C.point ∈ Set.range C.ι := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact subset_closure rfl
    have h1 : w ∈ C.ι ⁻¹' Stacks.Ample.nonvanishingLocus M s := by
      rw [Set.mem_preimage, hw]; exact hs
    rw [Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections, ← hσdef,
      h0, Stacks.Ample.nonvanishingLocus_zero] at h1
    exact h1
  have hreg := isRegularSection_of_eval_top_ne_zero L sσ (by rw [hsσ]; exact hσ0)
  have hdeg : C.degree k M = invertibleCurveDegree k (C.ι ≫ sX) C.dim_le L := rfl
  rw [hdeg, invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_unit_zeroScheme k
    (C.ι ≫ sX) C.dim_le L sσ hreg]
  have hEC := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection C.scheme L sσ).2 hreg
  rw [hsσ] at hEC ⊢
  set Zs := Stacks.Divisors.zeroScheme C.scheme L σ with hZs
  haveI := hEC
  haveI : IsFinite (Zs.subschemeι ≫ C.ι ≫ sX) := isFinite_divisorSubscheme k (C.ι ≫ sX) C.dim_le Zs
  haveI : Finite Zs.subscheme := finite_of_isFinite_over_field k (Zs.subschemeι ≫ C.ι ≫ sX)
  letI : Fintype Zs.subscheme := Fintype.ofFinite _
  rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections,
    finrank_globalSections_eq_finsum_finrank_stalk k (Zs.subschemeι ≫ C.ι ≫ sX)]
  simp only [finrank_stalk_eq_length_mul_finrank_residueField k (Zs.subschemeι ≫ C.ι ≫ sX),
    finrank_residueField_eq_one_of_isFinite (Zs.subschemeι ≫ C.ι ≫ sX), mul_one]
  set Z := Stacks.Divisors.zeroScheme X M s with hZ
  have hZcomap : Zs = Z.comap C.ι := Stacks.Divisors.zeroScheme_pullback C.ι M s
  set g : X → ℤ := fun y => ((Module.length (X.presheaf.stalk y) (X.presheaf.stalk y ⧸
    (IdealSheafData.stalk I y ⊔ IdealSheafData.stalk Z y))).toNat : ℤ) with hg
  have key : ∀ z : Zs.subscheme,
      ((Module.length (Zs.subscheme.presheaf.stalk z) (Zs.subscheme.presheaf.stalk z)).toNat : ℤ) =
        g (C.ι (Zs.subschemeι z)) := by
    intro z
    set w := Zs.subschemeι z with hw
    have h1 := length_stalk_subscheme' Zs z
    rw [← hw] at h1
    have h2 : IdealSheafData.stalk Zs w = IdealSheafData.stalk (Z.comap C.ι) w :=
      congrArg (fun J => IdealSheafData.stalk J w) hZcomap
    rw [h2, Stacks.Chow.length_stalk_quotient_comap_eq C.ι Z w,
      Stacks.Chow.ker_stalkMap_subschemeι_eq_stalk I w] at h1
    rw [h1]
  have hinj : Function.Injective (fun z : Zs.subscheme => C.ι (Zs.subschemeι z)) :=
    (C.ι.isClosedEmbedding.injective).comp Zs.subschemeι.isClosedEmbedding.injective
  have hvan : closure ({C.point} : Set X) ∩ Function.support g =
      Set.range (fun z : Zs.subscheme => C.ι (Zs.subschemeι z)) ∩ Function.support g := by
    have hrangeι : Set.range C.ι = closure ({C.point} : Set X) := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    ext y
    refine ⟨fun ⟨hyC, hgy⟩ => ⟨?_, hgy⟩, fun ⟨⟨z, hz⟩, hgy⟩ => ⟨?_, hgy⟩⟩
    · have hne : (IdealSheafData.stalk I y ⊔ IdealSheafData.stalk Z y) ≠ ⊤ := by
        intro htop
        apply hgy
        have h0 : Module.length (X.presheaf.stalk y) (X.presheaf.stalk y ⧸
            (IdealSheafData.stalk I y ⊔ IdealSheafData.stalk Z y)) = 0 := by
          rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff]
          exact htop
        show ((Module.length (X.presheaf.stalk y) (X.presheaf.stalk y ⧸
            (IdealSheafData.stalk I y ⊔ IdealSheafData.stalk Z y))).toNat : ℤ) = 0
        rw [h0]
        rfl
      have hZy : IdealSheafData.stalk Z y ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
        le_trans le_sup_right (IsLocalRing.le_maximalIdeal hne)
      have hysupp : y ∈ (Z.support : Set X) := by
        have := (Stacks.Chow.le_iff_fromSpecStalk_mem_support Z y
          (IsLocalRing.closedPoint (X.presheaf.stalk y))).1 hZy
        rwa [Scheme.fromSpecStalk_closedPoint] at this
      rw [← hrangeι] at hyC
      obtain ⟨w, rfl⟩ := hyC
      have hw : w ∈ (Zs.support : Set C.scheme) := by
        rw [hZcomap, Scheme.IdealSheafData.support_comap]
        exact hysupp
      rw [← Scheme.IdealSheafData.range_subschemeι] at hw
      obtain ⟨z, rfl⟩ := hw
      exact ⟨z, rfl⟩
    · rw [← hz, ← hrangeι]
      exact ⟨_, rfl⟩
  have final : ((∑ᶠ z : Zs.subscheme,
      (Module.length (Zs.subscheme.presheaf.stalk z) (Zs.subscheme.presheaf.stalk z)).toNat : ℕ) :
        ℤ) = ∑ᶠ y ∈ closure ({C.point} : Set X), g y := by
    rw [finsum_mem_inter_support_eq g _ _ hvan, finsum_mem_range hinj, Nat.cast_finsum]
    exact finsum_congr key
  exact final

end FibreLocalLengths

open MMP CategoryTheory Limits AlgebraicGeometry Stacks.AlgebraicGeometry.ProjPolyChart MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Chart

variable {k : Type*} [Field k] {n : ℕ} {T : Type*} [CommRing T]

/-- The `i`-th coordinate of the chart substitution at `j` along `e`: `X (e i)` for `i ≠ j`, and
`-∑_{l ≠ j} s l * X (e l)` for `i = j`. -/
noncomputable def chartAux (e : Fin n → Fin n ⊕ Fin n) (j : Fin n) (s : Fin n → T) (i : Fin n) :
    MvPolynomial (Fin n ⊕ Fin n) T :=
  if i = j then -∑ l ∈ Finset.univ.erase j, C (s l) * X (e l) else X (e i)

/-- The chart substitution at `j` on both families of variables, given by `chartAux`. -/
noncomputable def chartSub (j : Fin n) (s : Fin n → T) :
    Fin n ⊕ Fin n → MvPolynomial (Fin n ⊕ Fin n) T
  | Sum.inl i => chartAux Sum.inl j s i
  | Sum.inr i => chartAux Sum.inr j s i

/-- The ring homomorphism which is `κ` on coefficients and substitutes `chartSub j s` for the
variables. -/
noncomputable def chartMap (κ : k →+* T) (j : Fin n) (s : Fin n → T) :
    MvPolynomial (Fin n ⊕ Fin n) k →+* MvPolynomial (Fin n ⊕ Fin n) T :=
  eval₂Hom (C.comp κ) (chartSub j s)

/-- `chartMap` commutes with a change `τ` of the coefficient ring. -/
theorem map_chartMap {T' : Type*} [CommRing T'] (τ : T →+* T') (κ : k →+* T) (j : Fin n)
    (s : Fin n → T) :
    (map τ).comp (chartMap κ j s) = chartMap (τ.comp κ) j (τ ∘ s) := by
  refine ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [chartMap]
  · rcases i with i | i <;> by_cases h : i = j <;>
      simp [chartMap, chartSub, chartAux, h, map_sum]

/-- The `i`-th coordinate of the chart substitution at `j` on a point `w`: `w (e i)` for `i ≠ j`,
and `-∑_{l ≠ j} c l * w (e l)` for `i = j`. -/
noncomputable def chartPtAux (e : Fin n → Fin n ⊕ Fin n) (j : Fin n) (c : Fin n → k)
    (w : Fin n ⊕ Fin n → k) (i : Fin n) : k :=
  if i = j then -∑ l ∈ Finset.univ.erase j, c l * w (e l) else w (e i)

/-- The chart substitution at `j` on a point, given by `chartPtAux` on both families of
coordinates. -/
noncomputable def chartPt (j : Fin n) (c : Fin n → k) (w : Fin n ⊕ Fin n → k) :
    Fin n ⊕ Fin n → k
  | Sum.inl i => chartPtAux Sum.inl j c w i
  | Sum.inr i => chartPtAux Sum.inr j c w i

/-- Evaluating at `w` the reduction along `E` of `chartMap κ j s f` is evaluating `f` at
`chartPt j c w`, where `c` is the reduction of `s`. -/
theorem eval_map_chartMap (κ : k →+* T) (E : T →+* k) (hE : ∀ r, E (κ r) = r) (j : Fin n)
    (s : Fin n → T) (c : Fin n → k) (hs : ∀ l, E (s l) = c l) (w : Fin n ⊕ Fin n → k)
    (f : MvPolynomial (Fin n ⊕ Fin n) k) :
    eval w (map E (chartMap κ j s f)) = eval (chartPt j c w) f := by
  have : (eval w).comp ((map E).comp (chartMap κ j s)) = eval (chartPt j c w) := by
    refine ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [chartMap, hE]
    · rcases i with i | i <;> by_cases h : i = j <;>
        simp [chartMap, chartSub, chartAux, chartPt, chartPtAux, h, hs, map_sum]
  exact RingHom.congr_fun this f

/-- If `q j ≠ 0` and both families of coordinates of `w` are orthogonal to `q`, then `w` is fixed
by the chart substitution at `j` with parameters `q l / q j`. -/
theorem chartPt_of_orth (j : Fin n) (q : Fin n → k) (hqj : q j ≠ 0) (w : Fin n ⊕ Fin n → k)
    (hu : ∑ l, w (Sum.inl l) * q l = 0) (hv : ∑ l, w (Sum.inr l) * q l = 0) :
    chartPt j (fun l => q l / q j) w = w := by
  have key : ∀ (e : Fin n → Fin n ⊕ Fin n), ∑ l, w (e l) * q l = 0 →
      chartPtAux e j (fun l => q l / q j) w j = w (e j) := by
    intro e he
    have h1 := Finset.add_sum_erase Finset.univ (fun l => w (e l) * q l) (Finset.mem_univ j)
    rw [he] at h1
    simp only [chartPtAux, if_true]
    have h2 : ∑ l ∈ Finset.univ.erase j, q l / q j * w (e l) =
        (∑ l ∈ Finset.univ.erase j, w (e l) * q l) / q j := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [h2]
    have : ∑ l ∈ Finset.univ.erase j, w (e l) * q l = - (w (e j) * q j) := by linear_combination h1
    rw [this]; field_simp
  ext (i | i)
  · by_cases h : i = j
    · subst h; exact key Sum.inl hu
    · simp [chartPt, chartPtAux, h]
  · by_cases h : i = j
    · subst h; exact key Sum.inr hv
    · simp [chartPt, chartPtAux, h]

/-- If `q j ≠ 0`, both families of coordinates of the chart substitution at `j` with parameters
`q l / q j` are orthogonal to `q`. -/
theorem chartPt_orth (j : Fin n) (q : Fin n → k) (hqj : q j ≠ 0) (w : Fin n ⊕ Fin n → k) :
    (∑ l, chartPt j (fun l => q l / q j) w (Sum.inl l) * q l = 0) ∧
    (∑ l, chartPt j (fun l => q l / q j) w (Sum.inr l) * q l = 0) := by
  have key : ∀ (e : Fin n → Fin n ⊕ Fin n),
      ∑ l, chartPtAux e j (fun l => q l / q j) w l * q l = 0 := by
    intro e
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [chartPtAux, if_true]
    have : ∑ l ∈ Finset.univ.erase j, (if l = j then (-∑ l ∈ Finset.univ.erase j, q l / q j * w (e l)) else w (e l)) * q l
        = ∑ l ∈ Finset.univ.erase j, w (e l) * q l := by
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [if_neg (Finset.ne_of_mem_erase hl)]
    rw [this]
    have h2 : ∑ l ∈ Finset.univ.erase j, q l / q j * w (e l) =
        (∑ l ∈ Finset.univ.erase j, w (e l) * q l) / q j := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [h2]; field_simp; ring
  exact ⟨key Sum.inl, key Sum.inr⟩

section Compare

variable {F : Type*} [Field F]

/-- The `j`-th coordinate of the chart substitution at `j` is `-∑_{l ≠ j} s l * X (e l)`. -/
theorem chartAux_self (j : Fin n) (s : Fin n → F) (e : Fin n → Fin n ⊕ Fin n) :
    chartAux e j s j = -∑ l ∈ Finset.univ.erase j, C (s l) * X (e l) := by
  simp [chartAux]

/-- For `i ≠ j`, the `i`-th coordinate of the chart substitution at `j` is `X (e i)`. -/
theorem chartAux_ne (j : Fin n) (s : Fin n → F) (e : Fin n → Fin n ⊕ Fin n) {i : Fin n}
    (h : i ≠ j) : chartAux e j s i = X (e i) := by
  simp [chartAux, h]

/-- If `x j ≠ 0`, the chart substitution at `j` with parameters `x i / x j` kills the linear form
`∑ l, x l * X (e l)`. -/
theorem eval₂Hom_chartSub_sum_C_mul_X_eq_zero (j : Fin n) (x : Fin n → F) (hxj : x j ≠ 0)
    (e : Fin n → Fin n ⊕ Fin n)
    (he : ∀ l, chartSub j (fun i => x i * (x j)⁻¹) (e l) =
      chartAux e j (fun i => x i * (x j)⁻¹) l) :
    eval₂Hom C (chartSub j (fun i => x i * (x j)⁻¹))
      (∑ l, C (x l) * X (e l) : MvPolynomial (Fin n ⊕ Fin n) F) = 0 := by
  rw [map_sum]
  simp only [map_mul, eval₂Hom_C, eval₂Hom_X', he]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), chartAux_self]
  have h1 : ∀ l ∈ Finset.univ.erase j,
      C (x l) * chartAux e j (fun i => x i * (x j)⁻¹) l = C (x l) * X (e l) := by
    intro l hl; rw [chartAux_ne _ _ _ (Finset.ne_of_mem_erase hl)]
  rw [Finset.sum_congr rfl h1, mul_neg, Finset.mul_sum]
  have : ∀ m ∈ Finset.univ.erase j, C (x j) * (C (x m * (x j)⁻¹) * X (e m) : MvPolynomial (Fin n ⊕ Fin n) F)
      = C (x m) * X (e m) := by
    intro m _
    rw [← mul_assoc, ← C_mul]
    congr 2
    field_simp
  rw [Finset.sum_congr rfl this]
  ring

/-- For `j ≠ j0` with `x j0 ≠ 0` and `x j ≠ 0`, applying the chart substitution at `j` (parameters
`x i / x j`) to the chart substitution at `j0` (parameters `x i / x j0`) of the variable `X (e i)`
gives the chart substitution at `j` of `X (e i)`. -/
theorem eval₂Hom_chartSub_chartSub (j0 j : Fin n) (x : Fin n → F) (hj : j ≠ j0)
    (h0 : x j0 ≠ 0) (h1 : x j ≠ 0) (e : Fin n → Fin n ⊕ Fin n)
    (he0 : ∀ l, chartSub j0 (fun i => x i * (x j0)⁻¹) (e l) =
      chartAux e j0 (fun i => x i * (x j0)⁻¹) l)
    (he : ∀ l, chartSub j (fun i => x i * (x j)⁻¹) (e l) =
      chartAux e j (fun i => x i * (x j)⁻¹) l)
    (i : Fin n) :
    eval₂Hom C (chartSub j (fun i => x i * (x j)⁻¹))
      (chartSub j0 (fun i => x i * (x j0)⁻¹) (e i)) =
      chartSub j (fun i => x i * (x j)⁻¹) (e i) := by
  rw [he0]
  by_cases hi : i = j0
  · subst hi
    have hLin := eval₂Hom_chartSub_sum_C_mul_X_eq_zero j x h1 e he
    rw [chartAux_self, he, chartAux_ne _ _ _ hj.symm]
    have hXi : eval₂Hom C (chartSub j (fun i => x i * (x j)⁻¹))
        (X (e i) : MvPolynomial (Fin n ⊕ Fin n) F) = X (e i) := by
      rw [eval₂Hom_X', he, chartAux_ne _ _ _ hj.symm]
    have hsplit : ∑ l, (C (x l) * X (e l) : MvPolynomial (Fin n ⊕ Fin n) F) =
        C (x i) * X (e i) + ∑ l ∈ Finset.univ.erase i, C (x l) * X (e l) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    rw [hsplit, map_add, map_mul, eval₂Hom_C, hXi] at hLin
    have hfac : ∑ l ∈ Finset.univ.erase i, (C (x l * (x i)⁻¹) * X (e l) : MvPolynomial (Fin n ⊕ Fin n) F) =
        C (x i)⁻¹ * ∑ l ∈ Finset.univ.erase i, C (x l) * X (e l) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, ← C_mul, mul_comm (x l)]
    rw [hfac, map_neg, map_mul, eval₂Hom_C]
    have h2 : eval₂Hom C (chartSub j (fun i => x i * (x j)⁻¹))
        (∑ l ∈ Finset.univ.erase i, (C (x l) * X (e l) : MvPolynomial (Fin n ⊕ Fin n) F)) =
        - (C (x i) * X (e i)) := eq_neg_of_add_eq_zero_right hLin
    rw [h2, mul_neg, neg_neg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ h0, C_1, one_mul]
  · rw [chartAux_ne _ _ _ hi, eval₂Hom_X', he]

/-- For `j ≠ j0` with `x j0 ≠ 0` and `x j ≠ 0`, the chart map at `j0` (parameters `x i / x j0`)
followed by the chart substitution at `j` (parameters `x i / x j`) is the chart map at `j`. -/
theorem eval₂Hom_chartSub_comp_chartMap (κ : k →+* F) (j0 j : Fin n) (x : Fin n → F)
    (hj : j ≠ j0) (h0 : x j0 ≠ 0) (h1 : x j ≠ 0) :
    (eval₂Hom C (chartSub j (fun i => x i * (x j)⁻¹))).comp
      (chartMap κ j0 (fun i => x i * (x j0)⁻¹)) = chartMap κ j (fun i => x i * (x j)⁻¹) := by
  refine ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [chartMap]
  · rcases i with i | i
    · simpa [chartMap] using
        eval₂Hom_chartSub_chartSub j0 j x hj h0 h1 Sum.inl (fun l => rfl) (fun l => rfl) i
    · simpa [chartMap] using
        eval₂Hom_chartSub_chartSub j0 j x hj h0 h1 Sum.inr (fun l => rfl) (fun l => rfl) i

end Compare

end Chart

section SheafPieces

open Opposite

attribute [local instance 10000] HasDerivedCategory.standard

/-- If `M` is free of rank `r` over `A` and `N` is a base change of `M` to the field `B`, then
`N` has dimension `r` over `B`. -/
theorem finrank_eq_of_isBaseChange {A B M N : Type*} [CommRing A] [Field B]
    {_ : Algebra A B} [AddCommGroup M] {_ : Module A M} [AddCommGroup N]
    {_ : Module A N} {_ : Module B N} {_ : IsScalarTower A B N} {φ : M →ₗ[A] N}
    (hφ : IsBaseChange B φ) {r : ℕ} (ℓ : M ≃ₗ[A] (Fin r → A)) : Module.finrank B N = r := by
  have := (hφ.equiv.symm.trans ((LinearEquiv.baseChange A B _ _ ℓ).trans
    (TensorProduct.piScalarRight A B B (Fin r)))).finrank_eq
  rw [this, Module.finrank_fin_fun]

/-- The identification of the global sections of the pullback of `L` to `π⁻¹ V` with the
sections of `L` over `π⁻¹ V`. -/
noncomputable def restrSec {Y T : Scheme.{u}} (π : Y ⟶ T) (V : T.Opens) (L : Y.Modules) :
    Γ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L, ⊤) →+ Γ(L, π ⁻¹ᵁ V) :=
  (L.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (π ⁻¹ᵁ V)).symm).op).hom.comp
    (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L)
      ⊤).hom

/-- `restrSec` is bijective. -/
theorem restrSec_bijective {Y T : Scheme.{u}} (π : Y ⟶ T) (V : T.Opens) (L : Y.Modules) :
    Function.Bijective (restrSec π V L) :=
  (ConcreteCategory.bijective_of_isIso
    (L.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (π ⁻¹ᵁ V)).symm).op)).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L) ⊤))

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections
  AlgebraicGeometry.ProperFlatFibreEulerCharacteristic in
/-- `restrSec` as a linear map over `Γ(T, V)`. -/
noncomputable def restrSecₗ {Y T : Scheme.{u}} (π : Y ⟶ T) {V : T.Opens} (hV : IsAffineOpen V)
    (L : Y.Modules) :
    letI := Stacks.Cech.sectionsModule ((π ∣_ V) ≫ hV.isoSpec.hom)
      ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L) ⊤
    Γ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L, ⊤) ≃ₗ[Γ(T, V)]
      Γ((Scheme.Modules.pushforward π).obj L, V) :=
  letI := Stacks.Cech.sectionsModule ((π ∣_ V) ≫ hV.isoSpec.hom)
    ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L) ⊤
  LinearEquiv.ofBijective (M₂ := Γ((Scheme.Modules.pushforward π).obj L, V))
    { toFun := fun x => restrSec π V L x
      map_add' := fun x y => map_add (restrSec π V L) x y
      map_smul' := fun a x => by
        change L.presheaf.map _
          (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L)
            ⊤ ((Stacks.Cech.baseRingHom ((π ∣_ V) ≫ hV.isoSpec.hom) ⊤).hom a • x)) = _
        rw [Scheme.Modules.Hom.app_smul]
        change (L.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (π ⁻¹ᵁ V)).symm).op)
          ((((π ⁻¹ᵁ V).ι.appIso ⊤).inv
              ((Stacks.Cech.baseRingHom ((π ∣_ V) ≫ hV.isoSpec.hom) ⊤).hom a) •
            (show Γ(L, (π ⁻¹ᵁ V).ι ''ᵁ ⊤) from Scheme.Modules.Hom.app
              ((Scheme.Modules.restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).inv.app L) ⊤ x) :
              Γ(L, (π ⁻¹ᵁ V).ι ''ᵁ ⊤))) = _
        rw [Scheme.Modules.map_smul, map_baseRingHom_morphismRestrict π hV a]
        rfl }
    (restrSec_bijective π V L)

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections AlgebraicGeometry
  AlgebraicGeometry.ProperFlatFibreEulerCharacteristic in
/-- **The cohomology of a fibre, when the sections over an affine open of the base are free.** -/
theorem fibre_cohomology_of_basis {Y T : Scheme.{u}} (π : Y ⟶ T) {V : T.Opens}
    (hV : IsAffineOpen V) [IsProper π] [Flat π] (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L)
    (hvan : ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)))
    {r : ℕ} (b : Module.Basis (Fin r) Γ(T, V) Γ((Scheme.Modules.pushforward π).obj L, V))
    (t : T) (ht : t ∈ V) :
    (∀ p : ℕ, 0 < p → Subsingleton (cohomologyOverField (T.residueField t)
      (π.fiberToSpecResidueField t) ((Scheme.Modules.pullback (π.fiberι t)).obj L) p)) ∧
    Module.finrank (T.residueField t) (cohomologyOverField (T.residueField t)
      (π.fiberToSpecResidueField t) ((Scheme.Modules.pullback (π.fiberι t)).obj L) 0) = r := by
  set ι := (π ⁻¹ᵁ V).ι
  set F := (Scheme.Modules.pullback ι).obj L
  set f := (π ∣_ V) ≫ hV.isoSpec.hom
  have hF : Stacks.SheafOfModules.IsInvertible (π ⁻¹ᵁ V).toScheme.presheaf
      (π ⁻¹ᵁ V).toScheme.ringCatSheaf.2 F :=
    Stacks.RingedSpace.modulePullback_isInvertible_of ι.toLRSHom.toShHom L hL
  haveI : F.IsQuasicoherent := Stacks.Picard.isQuasicoherent_of_isInvertible F hF
  haveI : Flat f := inferInstance
  obtain ⟨-, hflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible f F hF
  have hsq := isPullback_fiberιOfMem π hV t ht
  obtain ⟨hvan', hbc⟩ :=
    Stacks.AlgebraicGeometry.ProperFlatGlobalSections.cohomologyBaseChange_of_vanishing
      f F hflat hvan (residueOfMem t ht).hom hsq
  letI := Stacks.Cech.sectionsModule f F ⊤
  let eΓ : Γ(F, ⊤) ≃ₗ[Γ(T, V)] (Fin r → Γ(T, V)) := (restrSecₗ π hV L).trans b.equivFun
  let eG : (Scheme.Modules.pullback (π.fiberι t)).obj L ≅
      (Scheme.Modules.pullback (fiberιOfMem π t ht)).obj F :=
    (Scheme.Modules.pullbackCongr (fiberιOfMem_ι π t ht)).symm.app L ≪≫
      ((Scheme.Modules.pullbackComp (fiberιOfMem π t ht) ι).app L).symm
  constructor
  · intro p hp
    have h := ModuleCat.subsingleton_of_isZero
      ((@ModuleCat.isZero_of_subsingleton _ _ _ (hvan' p hp)).of_iso
        (((AlgebraicGeometry.moduleGlobalSections (π.fiber t)).rightDerived p).mapIso eG))
    exact h
  · rw [(cohomologyOverFieldZeroLinearIso (T.residueField t) (π.fiberToSpecResidueField t)
      _).toLinearEquiv.finrank_eq, ((restrictScalarsOverBase (T.residueField t)
        (π.fiberToSpecResidueField t)).mapIso
        ((SheafOfModules.evaluation (π.fiber t).ringCatSheaf (op ⊤)).mapIso eG)).toLinearEquiv.finrank_eq]
    exact finrank_eq_of_isBaseChange hbc eΓ

/-- For affine opens `W ≤ V`, the inclusion of `W` into `V` corresponds under `isoSpec` to the
morphism of spectra induced by the restriction `Γ(T, V) ⟶ Γ(T, W)`. -/
theorem homOfLE_isoSpec {T : Scheme.{u}} {V W : T.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (h : W ≤ V) :
    T.homOfLE h ≫ hV.isoSpec.hom = hW.isoSpec.hom ≫ Spec.map (T.presheaf.map (homOfLE h).op) := by
  rw [← cancel_mono hV.isoSpec.inv, ← cancel_mono V.ι]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, IsAffineOpen.isoSpec_inv_ι]
  rw [Scheme.homOfLE_ι]
  have := IsAffineOpen.SpecMap_appLE_fromSpec (𝟙 T) hV hW (by simpa using h)
  have e : Scheme.Hom.appLE (𝟙 T) V W (by simpa using h) = T.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE]
    rfl
  rw [e] at this
  rw [this, ← IsAffineOpen.isoSpec_inv_ι hW]
  simp

/-- For opens `W ≤ V` of the base, the square formed by the restrictions of `π` over `W` and `V`
and the two inclusions is a pullback. -/
theorem isPullback_homOfLE_morphismRestrict {Y T : Scheme.{u}} (π : Y ⟶ T) {V W : T.Opens}
    (h : W ≤ V) :
    IsPullback (Y.homOfLE (show π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V from fun y hy => h hy)) (π ∣_ W) (π ∣_ V)
      (T.homOfLE h) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict π V).flip
  · simpa using (isPullback_morphismRestrict π W).flip
  · rw [← cancel_mono V.ι]
    simp

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections AlgebraicGeometry
  AlgebraicGeometry.ProperFlatFibreEulerCharacteristic in
/-- Vanishing of higher cohomology over an affine open passes to a smaller affine open. -/
theorem vanishing_of_le {Y T : Scheme.{u}} (π : Y ⟶ T) [IsProper π] [Flat π] {V W : T.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V) (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L)
    (hvan : ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))) :
    ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ W)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj L)) := by
  set ι := (π ⁻¹ᵁ V).ι
  set F := (Scheme.Modules.pullback ι).obj L
  set f := (π ∣_ V) ≫ hV.isoSpec.hom
  have hF : Stacks.SheafOfModules.IsInvertible (π ⁻¹ᵁ V).toScheme.presheaf
      (π ⁻¹ᵁ V).toScheme.ringCatSheaf.2 F :=
    Stacks.RingedSpace.modulePullback_isInvertible_of ι.toLRSHom.toShHom L hL
  haveI : F.IsQuasicoherent := Stacks.Picard.isQuasicoherent_of_isInvertible F hF
  haveI : Flat f := inferInstance
  obtain ⟨-, hflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible f F hF
  have hsq : IsPullback (Y.homOfLE (show π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V from fun y hy => h hy))
      ((π ∣_ W) ≫ hW.isoSpec.hom) f (Spec.map (CommRingCat.ofHom (T.presheaf.map (homOfLE h).op).hom)) :=
    (isPullback_homOfLE_morphismRestrict π h).of_iso (Iso.refl _) (Iso.refl _)
      hW.isoSpec hV.isoSpec (by simp) (by simp) (by simp [f]) (homOfLE_isoSpec hV hW h)
  obtain ⟨hvan', -⟩ :=
    Stacks.AlgebraicGeometry.ProperFlatGlobalSections.cohomologyBaseChange_of_vanishing
      f F hflat hvan (T.presheaf.map (homOfLE h).op).hom hsq
  intro p hp
  let e : (Scheme.Modules.pullback (Y.homOfLE (show π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V from fun y hy => h hy))).obj F ≅
      (Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj L :=
    ((Scheme.Modules.pullbackComp (Y.homOfLE (show π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V from fun y hy => h hy))
      ι).app L) ≪≫
      (Scheme.Modules.pullbackCongr (Scheme.homOfLE_ι _ _)).app L
  exact ModuleCat.subsingleton_of_isZero
    ((@ModuleCat.isZero_of_subsingleton _ _ _ (hvan' p hp)).of_iso
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ W)).rightDerived p).mapIso e).symm)

open Stacks.Ample Stacks.RelativeVeryAmple in
/-- **Uniform Serre vanishing for the pulled back twists over an affine open of the base.** -/
theorem exists_vanishing_twists {𝒞 S : Scheme.{u}} (π : 𝒞 ⟶ S) [IsProper π]
    (H A : 𝒞.Modules) [IsInvertibleModule 𝒞 H] [IsInvertibleModule 𝒞 A]
    (hA : Stacks.RelativeAmple.IsRelativelyAmple π A) {V : S.Opens} (hV : IsAffineOpen V)
    [IsNoetherianRing Γ(S, V)] {ι : Type*} [Finite ι] (m : ι → ℤ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ j : ι, ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj (MMP.Chow.twistMod H A n (m j)))) := by
  set X := (π ⁻¹ᵁ V).toScheme
  let f : X ⟶ Spec (.of Γ(S, V)) := (π ∣_ V) ≫ hV.isoSpec.hom
  haveI : IsProper f := inferInstance
  let L' : X.Modules := (Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj A
  haveI : IsInvertibleModule X L' :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (π ⁻¹ᵁ V).ι A
  have hL' : IsAmple X L' := Stacks.RelativeAmple.IsRelativelyAmple.isAmple_preimage π A hA V hV
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let F : ι → X.Modules := fun j => (Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj (tensorPowModule 𝒞 H (m j))
  haveI : ∀ j, IsInvertibleModule X (F j) := fun j =>
    haveI : IsInvertibleModule 𝒞 (tensorPowModule 𝒞 H (m j)) :=
      isInvertibleModule_tensorPowModule 𝒞 H (m j)
    Stacks.InvertiblePullback.isInvertibleModule_pullback (π ⁻¹ᵁ V).ι (tensorPowModule 𝒞 H (m j))
  haveI : ∀ j, (F j).IsCoherent := fun j => Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X (F j)
  obtain ⟨n₀, hn₀⟩ := MMP.Chow.exists_forall_subsingleton_rightDerived_moduleGlobalSections f L' hL' F
  refine ⟨n₀, fun n hn j p hp => ?_⟩
  let e : (Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj (MMP.Chow.twistMod H A n (m j)) ≅
      tensorModules X (F j) (tensorPowModule X L' (n : ℤ)) :=
    pullbackTensorModulesIso (π ⁻¹ᵁ V).ι (tensorPowModule 𝒞 H (m j)) (tensorPowModule 𝒞 A (n : ℤ)) ≪≫
      tensorModulesMapIso X (Iso.refl _) (pullbackTensorPowModuleIso (π ⁻¹ᵁ V).ι A n)
  exact ModuleCat.subsingleton_of_isZero
    ((@ModuleCat.isZero_of_subsingleton _ _ _ (hn₀ n hn j p hp)).of_iso
      (((AlgebraicGeometry.moduleGlobalSections X).rightDerived p).mapIso e))

open Stacks.Ample Stacks.RelativeVeryAmple in
/-- `(H^m ⊗ A^n) ⊗ H ≅ H^(m+1) ⊗ A^n`. -/
noncomputable def twistModSuccIso {X : Scheme.{u}} (H A : X.Modules) [IsInvertibleModule X H]
    [IsInvertibleModule X A] (n : ℕ) (m : ℤ) :
    tensorModules X (MMP.Chow.twistMod H A n m) H ≅ MMP.Chow.twistMod H A n (m + 1) :=
  Stacks.TensorSheafSpellingIso.tensorModulesAssociator X (tensorPowModule X H m)
      (tensorPowModule X A n) H ≪≫
    tensorModulesMapIso X (Iso.refl _) (Stacks.SheafOfModules.tensorSheafBraiding X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _ _) ≪≫
    (Stacks.TensorSheafSpellingIso.tensorModulesAssociator X (tensorPowModule X H m) H
      (tensorPowModule X A n)).symm ≪≫
    tensorModulesMapIso X (tensorModulesMapIso X (Iso.refl _) (tensorPowModuleOneIso X H).symm ≪≫
      tensorPowModuleAddIso X H m 1 ) (Iso.refl _)

open Stacks.Ample Stacks.RelativeVeryAmple in
/-- The twist isomorphism on a fibre: `ρ^*(N_m) ⊗ E ≅ ρ^*(N_{m+1})`, where `E ≅ ρ^* H`. -/
noncomputable def fibreTwistIso {X' 𝒞 : Scheme.{u}} (ρ : X' ⟶ 𝒞) (H A : 𝒞.Modules)
    [IsInvertibleModule 𝒞 H] [IsInvertibleModule 𝒞 A] (n : ℕ) (m : ℤ) {E : X'.Modules}
    (eH : E ≅ (Scheme.Modules.pullback ρ).obj H) :
    tensorModules X' ((Scheme.Modules.pullback ρ).obj (MMP.Chow.twistMod H A n m)) E ≅
      (Scheme.Modules.pullback ρ).obj (MMP.Chow.twistMod H A n (m + 1)) :=
  tensorModulesMapIso X' (Iso.refl _) eH ≪≫
    (pullbackTensorModulesIso ρ (MMP.Chow.twistMod H A n m) H).symm ≪≫
    (Scheme.Modules.pullback ρ).mapIso (twistModSuccIso H A n m)

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections AlgebraicGeometry in
/-- If `fk` is `fκ` followed by the morphism of spectra induced by a bijection `c : k → κ`, the
cohomology of `F` has the same dimension over `k` as over `κ`. -/
theorem finrank_cohomologyOverField_eq {X : Scheme.{u}} {k κ : Type u} [Field k] [Field κ]
    (c : k →+* κ) (hc : Function.Bijective c) (fk : X ⟶ Spec (.of k)) (fκ : X ⟶ Spec (.of κ))
    (h : fk = fκ ≫ Spec.map (CommRingCat.ofHom c)) (F : X.Modules) (i : ℕ) :
    Module.finrank k (cohomologyOverField k fk F i) = Module.finrank κ (cohomologyOverField κ fκ F i) := by
  subst h
  have hring : ((Scheme.ΓSpecIso (.of k)).inv ≫ (fκ ≫ Spec.map (CommRingCat.ofHom c)).appLE ⊤ ⊤ (by simp)) =
      CommRingCat.ofHom c ≫ ((Scheme.ΓSpecIso (.of κ)).inv ≫ fκ.appLE ⊤ ⊤ (by simp)) := by
    simp [Scheme.Hom.appLE]
    rfl
  unfold cohomologyOverField
  rw [hring]
  unfold Module.finrank
  congr 1
  exact rank_eq_of_equiv_equiv c (AddEquiv.refl _) hc (fun r m => rfl)

open Stacks.Ample Stacks.RelativeVeryAmple MMP.Mori TopologicalSpace
  Stacks.AlgebraicGeometry.ProperFlatGlobalSections AlgebraicGeometry in
/-- **The drop of `h⁰` under the twist by `H` on a closed fibre is the degree of the fundamental
cycle.** -/
theorem finrank_diff_fibre {k : Type u} [Field k] {S 𝒞 Y' : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y' ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY]
    (π : 𝒞 ⟶ S) [IsProper π] (ψ : 𝒞 ⟶ Y') (hψ : π ≫ sS = ψ ≫ sY)
    (L : Y'.Modules) [SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatSheaf.2 L]
    (A : 𝒞.Modules) [IsInvertibleModule 𝒞 A] (n : ℕ) (m : ℤ) (x : S)
    (hdim : topologicalKrullDim (π.fiber x) ≤ 1)
    (c : k →+* S.residueField x) (hc : Function.Bijective c)
    (hsX : π.fiberι x ≫ π ≫ sS =
      π.fiberToSpecResidueField x ≫ Spec.map (CommRingCat.ofHom c))
    (hG : ∀ p : ℕ, 0 < p → Subsingleton (cohomologyOverField (S.residueField x)
      (π.fiberToSpecResidueField x)
      ((Scheme.Modules.pullback (π.fiberι x)).obj
        (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n m)) p))
    (hF : ∀ p : ℕ, 0 < p → Subsingleton (cohomologyOverField (S.residueField x)
      (π.fiberToSpecResidueField x)
      ((Scheme.Modules.pullback (π.fiberι x)).obj
        (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n (m + 1))) p)) :
    (Module.finrank (S.residueField x) (cohomologyOverField (S.residueField x)
      (π.fiberToSpecResidueField x) ((Scheme.Modules.pullback (π.fiberι x)).obj
        (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n (m + 1))) 0) : ℤ) -
    (Module.finrank (S.residueField x) (cohomologyOverField (S.residueField x)
      (π.fiberToSpecResidueField x) ((Scheme.Modules.pullback (π.fiberι x)).obj
        (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n m)) 0) : ℤ) =
    OneCycle.degree ℤ sY L
        (∑ᶠ C : {C : ProperCurve (π.fiberι x ≫ π ≫ sS) //
            closure ({C.point} : Set (π.fiber x)) ∈ irreducibleComponents (π.fiber x)},
          ((Module.length ((π.fiber x).presheaf.stalk C.1.point)
            ((π.fiber x).presheaf.stalk C.1.point)).toNat : ℤ) •
            cyclePushforwardOfPoint ℤ sY (π.fiberι x ≫ ψ) C.1.point) := by
  set ρ := π.fiberι x with hρ
  haveI hLinv : IsInvertibleModule Y' L := ‹_›
  haveI hHinv : IsInvertibleModule 𝒞 ((Scheme.Modules.pullback ψ).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback ψ L
  haveI hN : ∀ m' : ℤ, IsInvertibleModule 𝒞 (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n m') :=
    fun m' => Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules 𝒞
      (tensorPowModule 𝒞 ((Scheme.Modules.pullback ψ).obj L) m') (tensorPowModule 𝒞 A (n : ℤ))
  haveI hG1 : ∀ m' : ℤ, IsInvertibleModule (π.fiber x) ((Scheme.Modules.pullback ρ).obj
      (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n m')) := fun m' =>
    Stacks.InvertiblePullback.isInvertibleModule_pullback ρ
      (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n m')
  haveI : IsIso (CommRingCat.ofHom c) := (ConcreteCategory.isIso_iff_bijective _).2 hc
  haveI : IsProper (ρ ≫ π ≫ sS) := by
    rw [hsX]
    have hbig : IsPullback (π.fiberι x) (π.fiberToSpecResidueField x) π
        (S.fromSpecResidueField x) := IsPullback.of_hasPullback _ _
    haveI : IsProper (π.fiberToSpecResidueField x) :=
      MorphismProperty.of_isPullback (P := @IsProper) hbig ‹IsProper π›
    haveI : IsProper (Spec.map (CommRingCat.ofHom c)) := inferInstance
    exact MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  haveI : IsLocallyNoetherian (π.fiber x) :=
    LocallyOfFiniteType.isLocallyNoetherian (π.fiberToSpecResidueField x)
  haveI hC : ∀ m' : ℤ, ((Scheme.Modules.pullback ρ).obj
      (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n m')).IsCoherent := fun m' =>
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible (π.fiber x) _
  let eH : (Scheme.Modules.pullback (ρ ≫ ψ)).obj L ≅
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback ψ).obj L) :=
    ((Scheme.Modules.pullbackComp ρ ψ).app L).symm
  let e := fibreTwistIso ρ ((Scheme.Modules.pullback ψ).obj L) A n m eH
  haveI : IsInvertibleModule (π.fiber x) ((Scheme.Modules.pullback (ρ ≫ ψ)).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (ρ ≫ ψ) L
  haveI : (tensorModules (π.fiber x) ((Scheme.Modules.pullback ρ).obj
      (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n m))
      ((Scheme.Modules.pullback (ρ ≫ ψ)).obj L)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible (π.fiber x) _
  have hF' : ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField k (ρ ≫ π ≫ sS)
      ((Scheme.Modules.pullback ρ).obj
        (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n (m + 1))) i) :=
    fun i hi => hF i hi
  have hG' : ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField k (ρ ≫ π ≫ sS)
      ((Scheme.Modules.pullback ρ).obj
        (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n m)) i) :=
    fun i hi => hG i hi
  have key := MMP.Chow.finrank_sub_finrank_eq_degree_fundamentalCycle (sX := ρ ≫ π ≫ sS)
    (sY := sY) hdim (ρ ≫ ψ) (by rw [Category.assoc, ← hψ]) L
    ((Scheme.Modules.pullback ρ).obj
        (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n (m + 1)))
    ((Scheme.Modules.pullback ρ).obj
        (MMP.Chow.twistMod ((Scheme.Modules.pullback ψ).obj L) A n m)) e hF' hG'
  rwa [finrank_cohomologyOverField_eq c hc (ρ ≫ π ≫ sS) (π.fiberToSpecResidueField x) hsX,
    finrank_cohomologyOverField_eq c hc (ρ ≫ π ≫ sS) (π.fiberToSpecResidueField x) hsX] at key

open Stacks.Ample in
/-- If `(π, q) : 𝒞 ⟶ S ×_k Y` is a closed immersion for a projective `k`-scheme `Y`, then `𝒞`
carries an invertible sheaf which is ample relative to `π`. -/
theorem exists_relativelyAmple {S 𝒞 Y : Scheme.{u}} {k : Type u} [Field k]
    (sS : S ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (hY : IsProjectiveMorphism sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] :
    ∃ (A : 𝒞.Modules) (_ : IsInvertibleModule 𝒞 A), Stacks.RelativeAmple.IsRelativelyAmple π A := by
  obtain ⟨n, i, hi, hii⟩ := hY.baseChange sS
  have hπ : IsHQuasiProjective π := by
    refine ⟨n, pullback.lift π q hπq ≫ (pullbackSymmetry _ _).hom ≫ i, ?_, ?_, ?_⟩
    · have := hi
      infer_instance
    · have := hi
      infer_instance
    · rw [Category.assoc, Category.assoc, hii]
      simp
  obtain ⟨-, A, hA, hample⟩ := isQuasiProjective_of_isHQuasiProjective π hπ
  exact ⟨A, hA, hample⟩

open Opposite TopologicalSpace in
/-- A quasi-coherent finite locally free sheaf is, near every point `s`, free of a fixed rank `r`
over every affine open contained in that neighbourhood. -/
theorem exists_forall_basis_of_isFiniteLocallyFree {S : Scheme.{u}} (M : S.Modules)
    [M.IsQuasicoherent]
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := S.ringCatSheaf) M) (s : S) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ r : ℕ, ∀ V : S.Opens, IsAffineOpen V → V ≤ U →
      Nonempty (Module.Basis (Fin r) Γ(S, V) Γ(M, V)) := by
  obtain ⟨q, hq, hfin⟩ := h.exists_isFiniteLocallyFreeData
  have hcov : TopologicalSpace.IsOpenCover q.X :=
    (Opens.coversTop_iff S q.X).mp q.coversTop
  obtain ⟨i, hsi⟩ := hcov.exists_mem s
  obtain ⟨e⟩ := Scheme.Modules.nonempty_restrict_iso_free_of_isLocallyFreeData M q hq i
  haveI : Finite (q.generators i).I := hfin.isFiniteType i |>.finite
  obtain ⟨r, ⟨eq⟩⟩ : ∃ r : ℕ, Nonempty ((q.generators i).I ≃ Fin r) :=
    ⟨_, ⟨(Finite.equivFin _)⟩⟩
  refine ⟨q.X i, hsi, r, fun V hV hVU => ?_⟩
  have hr : Set.range hV.fromSpec.base ⊆ Set.range (Scheme.Opens.ι (q.X i)).base := by
    rw [← Scheme.Hom.coe_opensRange, hV.opensRange_fromSpec, Scheme.Opens.range_ι]
    exact fun y hy => hVU hy
  obtain ⟨e'⟩ := Stacks.Modules.nonempty_restrictIsoFree_of_range_subset (Scheme.Opens.ι (q.X i)) hV.fromSpec M
    (q.generators i).I hr e
  have hb := (tilde_fixed_free_iff_basis Γ(S, V) Γ(M, V)
    (q.generators i).I).mp ⟨Stacks.Modules.tildeIsoRestrictFromSpec M hV ≪≫ e'⟩
  exact hb.map fun b ↦ b.reindex eq

end SheafPieces

/-! ### Exactness of the fibre Koszul complex at an avoiding pair

The fibre of the family over a closed point carries the pull-backs of the twists and of the
multiplications by the sections `ℓ_a = ∑ aⱼ xⱼ`, `ℓ_b`. Where `ℓ_a` does not vanish, multiplication
by it is bijective on stalks; the two nonvanishing opens cover the fibre when `(a, b)` avoids it,
and gluing the local inverses gives exactness of the global sections; the fibre matrices are the
reductions of the matrices over the base by cohomology and base change. -/

section CoeffKoszul

/-! #### The Koszul complex of a universal pair, in coefficients

Polynomials in `u, v` with coefficients in a module are read as their families of coefficients
(`MMP.Chow.polyTensorEquiv`). Multiplication by `∑ᵢ cᵢ uᵢ` followed by a linear map `P` is then
`coeffMul`. When `c_{j₀} = 1` the pair `(∑ cᵢ uᵢ, ∑ cᵢ vᵢ)` is a regular sequence, so its Koszul
complex is exact in the middle and injective on the left (`coeffMul_koszul_injective_and_exact`). -/

open MvPolynomial TensorProduct

variable {R : Type*} [CommRing R] {N : ℕ}

/-- The coefficient form of multiplication by `∑ᵢ cᵢ Xᵢ` composed with `P`. -/
noncomputable def coeffMul (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1)) (c : Fin (N + 1) → R)
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (P : M →ₗ[R] M') :
    ((Fin (N + 1) ⊕ Fin (N + 1) →₀ ℕ) →₀ M) →ₗ[R] ((Fin (N + 1) ⊕ Fin (N + 1) →₀ ℕ) →₀ M') :=
  ∑ i, Finsupp.lmapDomain M' R (· + Finsupp.single (e i) 1) ∘ₗ
    Finsupp.mapRange.linearMap (c i • P)

/-- `coeffMul e c P` is the coefficient form of multiplication by `∑ᵢ cᵢ X (e i)` after the base
change of `P`. -/
theorem coeffMul_polyTensorEquiv (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1))
    (c : Fin (N + 1) → R) {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] (P : M →ₗ[R] M')
    (z : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) R ⊗[R] M) :
    coeffMul e c P (MMP.Chow.polyTensorEquiv z) =
      MMP.Chow.polyTensorEquiv ((∑ i, C (c i) * X (e i) : MvPolynomial _ R) •
        LinearMap.baseChange (MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) R) P z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, smul_add, hz, hz']
  | tmul p m =>
    induction p using MvPolynomial.induction_on' with
    | monomial u r =>
      rw [MMP.Chow.polyTensorEquiv_monomial_tmul, LinearMap.baseChange_tmul, Finset.sum_smul,
        map_sum]
      rw [coeffMul, LinearMap.sum_apply]
      simp only [LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_assoc, MvPolynomial.X, monomial_mul_monomial, C_mul_monomial,
        MMP.Chow.polyTensorEquiv_monomial_tmul]
      simp only [LinearMap.smul_apply, map_smul, one_mul, mul_one, smul_smul]
      rw [add_comm u, mul_comm]
    | add p q hp hq => simp only [add_tmul, map_add, smul_add, hp, hq]

/-- If `c j0 = 1`, the linear form `∑ᵢ cᵢ X (e i)` is `X (e j0)` plus the terms with `i ≠ j0`. -/
theorem sum_C_mul_X_eq (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1)) (c : Fin (N + 1) → R)
    (j0 : Fin (N + 1)) (hc : c j0 = 1) :
    (∑ i, C (c i) * X (e i) : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) R) =
      X (e j0) + ∑ i ∈ Finset.univ.erase j0, C (c i) * X (e i) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), hc, C_1, one_mul]

/-- If `c j0 = 1`, the pair `(∑ᵢ cᵢ uᵢ, ∑ᵢ cᵢ vᵢ)` is a weakly regular sequence on
`R[u, v] ⊗[R] M`. -/
theorem isWeaklyRegular_coeffPair (c : Fin (N + 1) → R) (j0 : Fin (N + 1)) (hc : c j0 = 1)
    (M : Type*) [AddCommGroup M] [Module R M] :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) R ⊗[R] M)
      [(∑ i, C (c i) * X (Sum.inl i) : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) R),
        ∑ i, C (c i) * X (Sum.inr i)] := by
  classical
  rw [sum_C_mul_X_eq Sum.inl c j0 hc, sum_C_mul_X_eq Sum.inr c j0 hc]
  refine MMP.Chow.isWeaklyRegular_X_add_X_add (by simp) _ _ ?_ ?_
  · intro θ hθ
    simp only [map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hθ _ (by simpa using Finset.ne_of_mem_erase hi) (by simp), ← C_eq_smul_one]
  · intro θ hθ
    simp only [map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hθ _ (by simp) (by simpa using Finset.ne_of_mem_erase hi), ← C_eq_smul_one]

/-- The base change of the linear map underlying a linear equivalence `F` agrees with the base
change of `F`. -/
theorem baseChange_toLinearMap_apply {A B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] (T : Type*) [CommRing T] [Algebra R T] (F : A ≃ₗ[R] B) (z : T ⊗[R] A) :
    LinearMap.baseChange T F.toLinearMap z = LinearEquiv.baseChange R T A B F z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a m => simp [LinearEquiv.baseChange]

/-- If `c j0 = 1` and `P`, `P'` are linear equivalences, the Koszul complex in coefficients of
the pair `(∑ᵢ cᵢ uᵢ, ∑ᵢ cᵢ vᵢ)` twisted by `P` and `P'` is injective on the left and exact in the
middle. -/
theorem coeffMul_koszul_injective_and_exact (j0 : Fin (N + 1)) (c : Fin (N + 1) → R) (hc : c j0 = 1)
    {M₂ M₁ M₀ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₀] [Module R M₀] (P : M₂ ≃ₗ[R] M₁) (P' : M₁ ≃ₗ[R] M₀) :
    (∀ w, coeffMul Sum.inl c P.toLinearMap w = 0 → coeffMul Sum.inr c P.toLinearMap w = 0 →
      w = 0) ∧
    (∀ s t, coeffMul Sum.inl c P'.toLinearMap s + coeffMul Sum.inr c P'.toLinearMap t = 0 →
      ∃ w, -(coeffMul Sum.inr c P.toLinearMap w) = s ∧ coeffMul Sum.inl c P.toLinearMap w = t) := by
  classical
  set T := MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) R
  set α : T := ∑ i, C (c i) * X (Sum.inl i)
  set β : T := ∑ i, C (c i) * X (Sum.inr i)
  have hreg := isWeaklyRegular_coeffPair c j0 hc M₂
  have hα : IsSMulRegular (T ⊗[R] M₂) α :=
    ((RingTheory.Sequence.isWeaklyRegular_cons_iff _ _ _).1 hreg).1
  let E₂ := (MMP.Chow.polyTensorEquiv (R := R) (M := M₂) (σ := Fin (N + 1) ⊕ Fin (N + 1)))
  let E₁ := (MMP.Chow.polyTensorEquiv (R := R) (M := M₁) (σ := Fin (N + 1) ⊕ Fin (N + 1)))
  let E₀ := (MMP.Chow.polyTensorEquiv (R := R) (M := M₀) (σ := Fin (N + 1) ⊕ Fin (N + 1)))
  let Q := LinearEquiv.baseChange R T M₂ M₁ P
  let Q' := LinearEquiv.baseChange R T M₁ M₀ P'
  have hQ : ∀ (a : T) z, Q (a • z) = a • Q z := fun a z => by
    simp [Q, LinearEquiv.baseChange]
  have hQ' : ∀ (a : T) z, Q' (a • z) = a • Q' z := fun a z => by
    simp [Q', LinearEquiv.baseChange]
  have k2 : ∀ (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1)) z,
      coeffMul e c P.toLinearMap (E₂ z) = E₁ ((∑ i, C (c i) * X (e i) : T) • Q z) := by
    intro e z
    rw [coeffMul_polyTensorEquiv, baseChange_toLinearMap_apply]
  have k1 : ∀ (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1)) z,
      coeffMul e c P'.toLinearMap (E₁ z) = E₀ ((∑ i, C (c i) * X (e i) : T) • Q' z) := by
    intro e z
    rw [coeffMul_polyTensorEquiv, baseChange_toLinearMap_apply]
  constructor
  · intro w h1 h2
    obtain ⟨z, rfl⟩ := E₂.surjective w
    rw [k2] at h1
    have h3 : Q (α • z) = 0 := by
      rw [hQ]; exact E₁.injective (by rw [h1, map_zero])
    have h4 : α • z = 0 := Q.injective (by rw [h3, map_zero])
    have h5 : z = 0 := hα (show α • z = α • 0 by rw [h4, smul_zero])
    rw [h5, map_zero]
  · intro s t hst
    obtain ⟨s', rfl⟩ := E₁.surjective s
    obtain ⟨t', rfl⟩ := E₁.surjective t
    obtain ⟨s'', rfl⟩ := Q.surjective s'
    obtain ⟨t'', rfl⟩ := Q.surjective t'
    rw [k1, k1, ← map_add, ← hQ', ← hQ', ← map_add, ← hQ, ← hQ, ← map_add] at hst
    have h0 : α • s'' + β • t'' = 0 := Q.injective (Q'.injective (E₀.injective
      (by rw [hst, map_zero, map_zero, map_zero])))
    have hmem : (s'', t'') ∈ LinearMap.ker (MMP.Chow.koszulTwoD₁ α β (T ⊗[R] M₂)) := by
      simpa using h0
    rw [MMP.Chow.ker_koszulTwoD₁_eq_range hreg] at hmem
    obtain ⟨z, hz⟩ := hmem
    simp only [MMP.Chow.koszulTwoD₂_apply, Prod.mk.injEq] at hz
    refine ⟨E₂ z, ?_, ?_⟩
    · rw [k2, ← hQ, ← map_neg, ← map_neg, ← neg_smul, ← hz.1]
      simp
    · rw [k2, ← hQ, hz.2]

end CoeffKoszul

section CoeffGlue

/-! #### Gluing coefficient families of sections

On an open `U` of a scheme, a family `ψᵢ` of morphisms which on each stalk is `cᵢ • P` with
`c_{j₀} = 1` and `P` bijective defines a Koszul complex in coefficients which is exact on stalks
(`coeffMul_koszul_injective_and_exact`); local lifts are unique and glue. -/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

variable {N : ℕ}

local notation "Mon" => (Fin (N + 1) ⊕ Fin (N + 1) →₀ ℕ)

/-- The coefficient form of `∑ᵢ X_{e i} • φᵢ` on families of coefficients. -/
noncomputable def coeffMapAdd (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1)) {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (φ : Fin (N + 1) → (A →+ B)) :
    (Mon →₀ A) →+ (Mon →₀ B) :=
  ∑ i, (Finsupp.mapDomain.addMonoidHom (· + Finsupp.single (e i) 1)).comp
    (Finsupp.mapRange.addMonoidHom (φ i))

/-- The value of `coeffMapAdd e φ` on a single coefficient `m` at the monomial `a`. -/
theorem coeffMapAdd_single (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1)) {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (φ : Fin (N + 1) → (A →+ B)) (a : Mon) (m : A) :
    coeffMapAdd e φ (Finsupp.single a m) =
      ∑ i, Finsupp.single (a + Finsupp.single (e i) 1) (φ i m) := by
  simp [coeffMapAdd, AddMonoidHom.finset_sum_apply, Finsupp.mapDomain_single]

/-- Applying additive maps `f` and `g` coefficientwise commutes with `coeffMapAdd` when
`g ∘ φᵢ = φ'ᵢ ∘ f` for every `i`. -/
theorem coeffMapAdd_mapRange (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1)) {A B A' B' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    (φ : Fin (N + 1) → (A →+ B)) (φ' : Fin (N + 1) → (A' →+ B')) (f : A →+ A') (g : B →+ B')
    (h : ∀ i m, g (φ i m) = φ' i (f m)) (w : Mon →₀ A) :
    Finsupp.mapRange.addMonoidHom g (coeffMapAdd e φ w) =
      coeffMapAdd e φ' (Finsupp.mapRange.addMonoidHom f w) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | single a m =>
    simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single, coeffMapAdd_single]
    rw [← Finsupp.mapRange.addMonoidHom_apply, map_sum]
    simp [h]

/-- `coeffMul e c P` is `coeffMapAdd` of the maps `cᵢ • P`. -/
theorem coeffMul_eq_coeffMapAdd {R : Type*} [CommRing R] (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1))
    (c : Fin (N + 1) → R) {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] (P : M →ₗ[R] M') (w : Mon →₀ M) :
    coeffMul e c P w = coeffMapAdd e (fun i => (c i • P).toAddMonoidHom) w := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | single a m =>
    rw [coeffMapAdd_single, coeffMul, LinearMap.sum_apply]
    simp [Finsupp.mapDomain_single]

/-- Germs of a family of sections. -/
noncomputable abbrev germF {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (y : X) (hy : y ∈ U) :
    (Mon →₀ Γ(M, U)) →+ (Mon →₀ M.presheaf.stalk y) :=
  Finsupp.mapRange.addMonoidHom (M.presheaf.germ U y hy).hom

/-- Restriction of a family of sections. -/
noncomputable abbrev resF {X : Scheme.{u}} (M : X.Modules) {U U' : X.Opens} (h : U' ≤ U) :
    (Mon →₀ Γ(M, U)) →+ (Mon →₀ Γ(M, U')) :=
  Finsupp.mapRange.addMonoidHom (M.presheaf.map (homOfLE h).op).hom

/-- Taking germs at `y` carries `coeffMapAdd` of a family of morphisms of sheaves on sections to
`coeffMapAdd` of the induced maps on stalks. -/
theorem germF_coeffMapAdd {X : Scheme.{u}} {M M' : X.Modules}
    (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1)) (φ : Fin (N + 1) → (M ⟶ M')) (U : X.Opens)
    (y : X) (hy : y ∈ U) (w : Mon →₀ Γ(M, U)) :
    germF M' U y hy (coeffMapAdd e (fun i => ((φ i).app U).hom) w) =
      coeffMapAdd e (fun i => (stalkLinearMap _ _ (φ i) y).toAddMonoidHom) (germF M U y hy w) :=
  coeffMapAdd_mapRange e _ _ _ _ (fun i m => (stalkLinearMap_germ _ _ (φ i) U y hy m).symm) w

/-- Restriction to a smaller open commutes with `coeffMapAdd` of a family of morphisms of
sheaves. -/
theorem resF_coeffMapAdd {X : Scheme.{u}} {M M' : X.Modules}
    (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1)) (φ : Fin (N + 1) → (M ⟶ M')) {U U' : X.Opens}
    (h : U' ≤ U) (w : Mon →₀ Γ(M, U)) :
    resF M' h (coeffMapAdd e (fun i => ((φ i).app U).hom) w) =
      coeffMapAdd e (fun i => ((φ i).app U').hom) (resF M h w) :=
  coeffMapAdd_mapRange e _ _ _ _ (fun i m =>
    (ConcreteCategory.congr_hom ((φ i).mapPresheaf.naturality (homOfLE h).op) m).symm) w

/-- If at every point of `U` the stalk maps of the `ψᵢ` are `cᵢ • P` with `c_{j₀} = 1` and `P`
bijective, a family of sections over `U` killed by both coefficient maps is zero. -/
theorem coeff_unique {X : Scheme.{u}} {M₂ M₁ : X.Modules} (ψ : Fin (N + 1) → (M₂ ⟶ M₁))
    (U : X.Opens)
    (hloc : ∀ y ∈ U, ∃ (j0 : Fin (N + 1)) (c : Fin (N + 1) → X.presheaf.stalk y), c j0 = 1 ∧
      ∃ P : M₂.presheaf.stalk y ≃ₗ[X.presheaf.stalk y] M₁.presheaf.stalk y,
        ∀ i z, stalkLinearMap _ _ (ψ i) y z = c i • P z)
    (w : Mon →₀ Γ(M₂, U)) (h1 : coeffMapAdd Sum.inl (fun i => ((ψ i).app U).hom) w = 0)
    (h2 : coeffMapAdd Sum.inr (fun i => ((ψ i).app U).hom) w = 0) : w = 0 := by
  ext e
  refine TopCat.Presheaf.section_ext ⟨M₂.presheaf, M₂.isSheaf⟩ U _ _ fun y hy => ?_
  obtain ⟨j0, c, hc, P, hP⟩ := hloc y hy
  have hmap : ∀ f : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1),
      coeffMapAdd f (fun i => (stalkLinearMap _ _ (ψ i) y).toAddMonoidHom) =
        coeffMapAdd f (fun i => (c i • P.toLinearMap).toAddMonoidHom) := fun f => by
    congr 1; funext i; ext z; exact hP i z
  have g1 := germF_coeffMapAdd Sum.inl ψ U y hy w
  have g2 := germF_coeffMapAdd Sum.inr ψ U y hy w
  rw [h1, map_zero, hmap, ← coeffMul_eq_coeffMapAdd] at g1
  rw [h2, map_zero, hmap, ← coeffMul_eq_coeffMapAdd] at g2
  have h0 :=
    (coeffMul_koszul_injective_and_exact j0 c hc P (LinearEquiv.refl _ _)).1 _ g1.symm g2.symm
  simpa using congrArg (fun f => f e) h0

/-- A point lying in each of finitely many opens lies in their intersection. -/
theorem mem_finset_inf_opens {X : Scheme.{u}} {ι : Type*} (U' : ι → X.Opens) (y : X)
    (t : Finset ι) (h : ∀ e ∈ t, y ∈ U' e) : y ∈ t.inf U' := by
  classical
  induction t using Finset.induction_on with
  | empty => trivial
  | insert a t ha ih =>
    rw [Finset.inf_insert]
    exact ⟨h a (Finset.mem_insert_self a t), ih fun e he => h e (Finset.mem_insert_of_mem he)⟩

/-- A family of sections with vanishing germs at `y` vanishes near `y`. -/
theorem exists_resF_eq_zero {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (y : X)
    (hy : y ∈ U) (d : Mon →₀ Γ(M, U)) (hd : germF M U y hy d = 0) :
    ∃ U' : X.Opens, y ∈ U' ∧ ∃ h : U' ≤ U, resF M h d = 0 := by
  classical
  have hz : ∀ e ∈ d.support, ∃ U' : X.Opens, y ∈ U' ∧ ∃ h : U' ≤ U,
      M.presheaf.map (homOfLE h).op (d e) = 0 := by
    intro e _
    have h1 : M.presheaf.germ U y hy (d e) = M.presheaf.germ U y hy 0 := by
      rw [map_zero]
      simpa using congrArg (fun f => f e) hd
    obtain ⟨W, hyW, i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq M.presheaf y hy hy (d e) 0 h1
    refine ⟨W, hyW, i₁.le, ?_⟩
    rw [show homOfLE i₁.le = i₁ from rfl, hW, map_zero]
  choose! U' hyU' hU' hres using hz
  refine ⟨U ⊓ d.support.inf U', ⟨hy, mem_finset_inf_opens U' y _ hyU'⟩, inf_le_left, ?_⟩
  ext e
  by_cases he : e ∈ d.support
  · have hle : U ⊓ d.support.inf U' ≤ U' e := inf_le_right.trans (Finset.inf_le he)
    have key : M.presheaf.map (homOfLE (inf_le_left : U ⊓ d.support.inf U' ≤ U)).op (d e) =
        M.presheaf.map (homOfLE hle).op (M.presheaf.map (homOfLE (hU' e he)).op (d e)) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply, Finsupp.coe_zero,
      Pi.zero_apply]
    rw [key, hres e he, map_zero]
  · rw [Finsupp.notMem_support_iff] at he
    simp [he]

/-- Restricting a family of sections twice is restricting it once. -/
theorem resF_resF {X : Scheme.{u}} (M : X.Modules) {U U' U'' : X.Opens} (h : U' ≤ U)
    (h' : U'' ≤ U') (w : Mon →₀ Γ(M, U)) :
    resF M h' (resF M h w) = resF M (h'.trans h) w := by
  ext e
  simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The germs of a restricted family of sections are the germs of the family. -/
theorem germF_resF {X : Scheme.{u}} (M : X.Modules) {U U' : X.Opens} (h : U' ≤ U) (y : X)
    (hy : y ∈ U') (w : Mon →₀ Γ(M, U)) :
    germF M U' y hy (resF M h w) = germF M U y (h hy) w := by
  ext e
  simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply]
  exact M.presheaf.germ_res_apply (homOfLE h) y hy (w e)

/-- **Local lifts.**  At a point where the stalks of the families are `cᵢ • P`, `cᵢ • P'`, a
solution of the coefficient Koszul equation exists near the point. -/
theorem coeff_local {X : Scheme.{u}} {M₂ M₁ M₀ : X.Modules} (ψ : Fin (N + 1) → (M₂ ⟶ M₁))
    (ψ' : Fin (N + 1) → (M₁ ⟶ M₀)) {V : X.Opens} (y : X) (hy : y ∈ V) (j0 : Fin (N + 1))
    (c : Fin (N + 1) → X.presheaf.stalk y) (hc : c j0 = 1)
    (P : M₂.presheaf.stalk y ≃ₗ[X.presheaf.stalk y] M₁.presheaf.stalk y)
    (P' : M₁.presheaf.stalk y ≃ₗ[X.presheaf.stalk y] M₀.presheaf.stalk y)
    (hP : ∀ i z, stalkLinearMap _ _ (ψ i) y z = c i • P z)
    (hP' : ∀ i z, stalkLinearMap _ _ (ψ' i) y z = c i • P' z) (s t : Mon →₀ Γ(M₁, V))
    (hst : coeffMapAdd Sum.inl (fun i => ((ψ' i).app V).hom) s +
      coeffMapAdd Sum.inr (fun i => ((ψ' i).app V).hom) t = 0) :
    ∃ U : X.Opens, y ∈ U ∧ ∃ h : U ≤ V, ∃ w : Mon →₀ Γ(M₂, U),
      -(coeffMapAdd Sum.inr (fun i => ((ψ i).app U).hom) w) = resF M₁ h s ∧
        coeffMapAdd Sum.inl (fun i => ((ψ i).app U).hom) w = resF M₁ h t := by
  classical
  have hmap : ∀ f : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1),
      coeffMapAdd f (fun i => (stalkLinearMap _ _ (ψ i) y).toAddMonoidHom) =
        coeffMapAdd f (fun i => (c i • P.toLinearMap).toAddMonoidHom) := fun f => by
    congr 1; funext i; ext z; exact hP i z
  have hmap' : ∀ f : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1),
      coeffMapAdd f (fun i => (stalkLinearMap _ _ (ψ' i) y).toAddMonoidHom) =
        coeffMapAdd f (fun i => (c i • P'.toLinearMap).toAddMonoidHom) := fun f => by
    congr 1; funext i; ext z; exact hP' i z
  have g := congrArg (germF M₀ V y hy) hst
  rw [map_add, germF_coeffMapAdd, germF_coeffMapAdd, hmap', hmap', ← coeffMul_eq_coeffMapAdd,
    ← coeffMul_eq_coeffMapAdd, map_zero] at g
  obtain ⟨w', hw1, hw2⟩ := (coeffMul_koszul_injective_and_exact j0 c hc P P').2 _ _ g
  have hrep : ∀ e, ∃ U' : X.Opens, ∃ hU : y ∈ U', ∃ m : Γ(M₂, U'),
      M₂.presheaf.germ U' y hU m = w' e := fun e => TopCat.Presheaf.germ_exist M₂.presheaf (w' e)
  choose U' hyU m hm using hrep
  set U₀ := V ⊓ w'.support.inf U' with hU₀
  have hy₀ : y ∈ U₀ := ⟨hy, mem_finset_inf_opens U' y _ fun e _ => hyU e⟩
  have hle : ∀ e ∈ w'.support, U₀ ≤ U' e := fun e he => inf_le_right.trans (Finset.inf_le he)
  let f₀ : Mon → Γ(M₂, U₀) := fun e =>
    if h : e ∈ w'.support then M₂.presheaf.map (homOfLE (hle e h)).op (m e) else 0
  have hf₀ : (Function.support f₀).Finite := by
    refine w'.support.finite_toSet.subset fun e he => ?_
    by_contra h
    apply he
    show f₀ e = 0
    simp only [f₀]
    rw [dif_neg (fun h' => h (Finset.mem_coe.2 h'))]
  let w₀ : Mon →₀ Γ(M₂, U₀) := Finsupp.ofSupportFinite f₀ hf₀
  have hw₀ : germF M₂ U₀ y hy₀ w₀ = w' := by
    ext e
    simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply, w₀,
      Finsupp.ofSupportFinite_coe, f₀]
    split_ifs with h
    · rw [M₂.presheaf.germ_res_apply, hm]
    · rw [map_zero]
      exact (Finsupp.notMem_support_iff.mp h).symm
  set d₁ := -(coeffMapAdd Sum.inr (fun i => ((ψ i).app U₀).hom) w₀) - resF M₁ inf_le_left s
  set d₂ := coeffMapAdd Sum.inl (fun i => ((ψ i).app U₀).hom) w₀ - resF M₁ inf_le_left t
  have hd₁ : germF M₁ U₀ y hy₀ d₁ = 0 := by
    rw [map_sub, map_neg, germF_coeffMapAdd, hmap, ← coeffMul_eq_coeffMapAdd, hw₀, germF_resF,
      hw1, sub_self]
  have hd₂ : germF M₁ U₀ y hy₀ d₂ = 0 := by
    rw [map_sub, germF_coeffMapAdd, hmap, ← coeffMul_eq_coeffMapAdd, hw₀, germF_resF, hw2,
      sub_self]
  obtain ⟨U₁, hy₁, h₁, hz₁⟩ := exists_resF_eq_zero M₁ y hy₀ d₁ hd₁
  obtain ⟨U₂, hy₂, h₂, hz₂⟩ := exists_resF_eq_zero M₁ y hy₀ d₂ hd₂
  refine ⟨U₁ ⊓ U₂, ⟨hy₁, hy₂⟩, (inf_le_left.trans h₁).trans inf_le_left,
    resF M₂ (inf_le_left.trans h₁) w₀, ?_, ?_⟩
  · have := congrArg (resF M₁ (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) hz₁
    rwa [map_zero, resF_resF, map_sub, map_neg, resF_coeffMapAdd, resF_resF,
      sub_eq_zero] at this
  · have := congrArg (resF M₁ (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) hz₂
    rwa [map_zero, resF_resF, map_sub, resF_coeffMapAdd, resF_resF, sub_eq_zero] at this

/-- **Gluing the local lifts.**  On a quasi-compact open `V`, if at every point of `V` the stalks
of the families are `cᵢ • P` and `cᵢ • P'` with `c_{j₀} = 1`, the coefficient Koszul complex of
sections over `V` is exact in the middle. -/
theorem coeff_glue {X : Scheme.{u}} {M₂ M₁ M₀ : X.Modules} (ψ : Fin (N + 1) → (M₂ ⟶ M₁))
    (ψ' : Fin (N + 1) → (M₁ ⟶ M₀)) (V : X.Opens) (hV : IsCompact (V : Set X))
    (hloc : ∀ y ∈ V, ∃ (j0 : Fin (N + 1)) (c : Fin (N + 1) → X.presheaf.stalk y), c j0 = 1 ∧
      ∃ (P : M₂.presheaf.stalk y ≃ₗ[X.presheaf.stalk y] M₁.presheaf.stalk y)
        (P' : M₁.presheaf.stalk y ≃ₗ[X.presheaf.stalk y] M₀.presheaf.stalk y),
        (∀ i z, stalkLinearMap _ _ (ψ i) y z = c i • P z) ∧
          ∀ i z, stalkLinearMap _ _ (ψ' i) y z = c i • P' z)
    (s t : Mon →₀ Γ(M₁, V))
    (hst : coeffMapAdd Sum.inl (fun i => ((ψ' i).app V).hom) s +
      coeffMapAdd Sum.inr (fun i => ((ψ' i).app V).hom) t = 0) :
    ∃ w : Mon →₀ Γ(M₂, V), -(coeffMapAdd Sum.inr (fun i => ((ψ i).app V).hom) w) = s ∧
      coeffMapAdd Sum.inl (fun i => ((ψ i).app V).hom) w = t := by
  classical
  have hloc1 : ∀ y : V, ∃ U : X.Opens, y.1 ∈ U ∧ ∃ h : U ≤ V, ∃ w : Mon →₀ Γ(M₂, U),
      -(coeffMapAdd Sum.inr (fun i => ((ψ i).app U).hom) w) = resF M₁ h s ∧
        coeffMapAdd Sum.inl (fun i => ((ψ i).app U).hom) w = resF M₁ h t := fun y => by
    obtain ⟨j0, c, hc, P, P', hP, hP'⟩ := hloc y.1 y.2
    exact coeff_local ψ ψ' y.1 y.2 j0 c hc P P' hP hP' s t hst
  choose U hyU hUV w hw1 hw2 using hloc1
  have huniq : ∀ (U' : X.Opens) (hU' : U' ≤ V) (z : Mon →₀ Γ(M₂, U')),
      coeffMapAdd Sum.inl (fun i => ((ψ i).app U').hom) z = 0 →
        coeffMapAdd Sum.inr (fun i => ((ψ i).app U').hom) z = 0 → z = 0 :=
    fun U' hU' z h1 h2 => coeff_unique ψ U' (fun y hy => by
      obtain ⟨j0, c, hc, P, P', hP, -⟩ := hloc y (hU' hy)
      exact ⟨j0, c, hc, P, hP⟩) z h1 h2
  have hcompat : ∀ y y' : V, resF M₂ (inf_le_left : U y ⊓ U y' ≤ U y) (w y) =
      resF M₂ (inf_le_right : U y ⊓ U y' ≤ U y') (w y') := by
    intro y y'
    rw [← sub_eq_zero]
    refine huniq _ (inf_le_left.trans (hUV y)) _ ?_ ?_
    · rw [map_sub, ← resF_coeffMapAdd, ← resF_coeffMapAdd, hw2, hw2, resF_resF, resF_resF,
        sub_self]
    · have e1 := congrArg (resF M₁ (inf_le_left : U y ⊓ U y' ≤ U y)) (hw1 y)
      have e2 := congrArg (resF M₁ (inf_le_right : U y ⊓ U y' ≤ U y')) (hw1 y')
      rw [map_neg, resF_coeffMapAdd, resF_resF] at e1 e2
      rw [map_sub, neg_eq_iff_eq_neg.mp e1, neg_eq_iff_eq_neg.mp e2, sub_self]
  have hcov : V ≤ iSup U := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyU ⟨y, hy⟩⟩
  have hglue : ∀ e : Mon, ∃ W : Γ(M₂, V),
      ∀ y : V, M₂.presheaf.map (homOfLE (hUV y)).op W = (w y) e := by
    intro e
    obtain ⟨W, hW, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := ⟨M₂.presheaf, M₂.isSheaf⟩) U V
      (fun y => homOfLE (hUV y)) hcov (fun y => (w y) e) (fun y y' => congrArg (fun f => f e) (hcompat y y'))
    exact ⟨W, hW⟩
  choose W hW using hglue
  obtain ⟨T, hT⟩ := hV.elim_finite_subcover (fun y : V => (U y : Set X)) (fun y => (U y).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyU ⟨y, hy⟩⟩)
  have hfin : (Function.support W).Finite := by
    refine (T.finite_toSet.biUnion fun y _ => (w y).support.finite_toSet).subset ?_
    intro e he
    by_contra hne
    simp only [Set.mem_iUnion, not_exists] at hne
    apply he
    refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨M₂.presheaf, M₂.isSheaf⟩)
      (fun y : T => U y.1) V (fun y => homOfLE (hUV y.1)) ?_ (W e) 0 fun y => ?_
    · intro x hx
      obtain ⟨y, hyx⟩ := Set.mem_iUnion.1 (hT hx)
      obtain ⟨hyT, hxy⟩ := Set.mem_iUnion.1 hyx
      exact Opens.mem_iSup.2 ⟨⟨y, hyT⟩, hxy⟩
    · rw [hW, map_zero]
      exact Finsupp.notMem_support_iff.mp fun h => hne y.1 y.2 h
  let Wf : Mon →₀ Γ(M₂, V) := Finsupp.ofSupportFinite W hfin
  have hres : ∀ y : V, resF M₂ (hUV y) Wf = w y := fun y => by
    ext e
    simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply, Wf,
      Finsupp.ofSupportFinite_coe]
    exact hW e y
  refine ⟨Wf, ?_, ?_⟩
  · ext e
    refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨M₁.presheaf, M₁.isSheaf⟩) U V
      (fun y => homOfLE (hUV y)) hcov _ _ fun y => ?_
    have := congrArg (fun f => f e) (hw1 y)
    rw [← hres y, ← resF_coeffMapAdd, ← map_neg] at this
    simpa using this
  · ext e
    refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨M₁.presheaf, M₁.isSheaf⟩) U V
      (fun y => homOfLE (hUV y)) hcov _ _ fun y => ?_
    have := congrArg (fun f => f e) (hw2 y)
    rw [← hres y, ← resF_coeffMapAdd] at this
    simpa using this

section Enc

open MvPolynomial

variable {R T : Type*} [CommRing R] [CommRing T] (ι : T ≃+* R)
  {M : Type*} [AddCommGroup M] [Module R M] {r : ℕ} (b : Module.Basis (Fin r) R M)

/-- For a vector `w` of polynomials, only finitely many monomials `a` give a nonzero
`∑ i, ι ((w i).coeff a) • b i`. -/
theorem enc_finite (w : Fin r → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) T) :
    (Function.support fun a : Mon => ∑ i, ι ((w i).coeff a) • b i).Finite := by
  classical
  refine (Set.finite_iUnion fun i => (w i).support.finite_toSet).subset fun a ha => ?_
  by_contra h
  simp only [Set.mem_iUnion, Finset.mem_coe, MvPolynomial.mem_support_iff, not_exists,
    not_not] at h
  exact ha (by simp [h])

/-- A vector of polynomials over `T`, read in the basis `b` as a family of coefficients in `M`. -/
noncomputable def enc : (Fin r → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) T) →+ (Mon →₀ M) where
  toFun w := Finsupp.ofSupportFinite _ (enc_finite ι b w)
  map_zero' := by ext a; simp [Finsupp.ofSupportFinite_coe]
  map_add' w w' := by
    ext a
    simp [Finsupp.ofSupportFinite_coe, MvPolynomial.coeff_add, add_smul, Finset.sum_add_distrib]

/-- The coefficient of `enc ι b w` at the monomial `a` is `∑ i, ι ((w i).coeff a) • b i`. -/
theorem enc_apply (w : Fin r → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) T) (a : Mon) :
    enc ι b w a = ∑ i, ι ((w i).coeff a) • b i := rfl

/-- `enc ι b` is injective. -/
theorem enc_injective : Function.Injective (enc (N := N) ι b) := by
  intro w w' h
  funext i
  ext a
  have := congrArg (fun f => b.repr (f a) i) h
  simp only [enc_apply, map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
    Finsupp.finset_sum_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact ι.injective this

/-- `enc ι b` is surjective. -/
theorem enc_surjective : Function.Surjective (enc (N := N) ι b) := by
  classical
  intro f
  refine ⟨fun i => ∑ a ∈ f.support, monomial a (ι.symm (b.repr (f a) i)), ?_⟩
  ext a
  rw [enc_apply]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq',
    Finsupp.mem_support_iff]
  split_ifs with h
  · simp only [RingEquiv.apply_symm_apply]
    exact b.sum_repr (f a)
  · push Not at h
    simp [h]

/-- `enc` of the monomial `t * u` in the `k`-th coordinate is the single coefficient
`ι t • b k` at `u`. -/
theorem enc_single (k : Fin r) (u : Mon) (t : T) :
    enc ι b (Pi.single k (monomial u t)) = Finsupp.single u (ι t • b k) := by
  classical
  ext a
  rw [enc_apply, Finset.sum_eq_single k]
  · simp only [Pi.single_eq_same, MvPolynomial.coeff_monomial, Finsupp.single_apply]
    split_ifs <;> simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

/-- `enc` of a vector of monomials with the common exponent `u` and coefficients `c i` is the
single coefficient `∑ i, ι (c i) • b i` at `u`. -/
theorem enc_monomial_vec (u : Mon) (c : Fin r → T) :
    enc ι b (fun i => monomial u (c i)) = Finsupp.single u (∑ i, ι (c i) • b i) := by
  classical
  ext a
  rw [enc_apply, Finsupp.single_apply]
  simp only [MvPolynomial.coeff_monomial]
  split_ifs <;> simp

/-- `enc` carries multiplication by the polynomial matrix `∑ⱼ X (e j) • [φⱼ]`, where `[φⱼ]` is the
matrix of `φⱼ` in the bases `b` and `b'`, to `coeffMapAdd e φ`. -/
theorem enc_mulVec {M' : Type*} [AddCommGroup M'] [Module R M'] {r' : ℕ}
    (b' : Module.Basis (Fin r') R M') (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1))
    (φ : Fin (N + 1) → (M →ₗ[R] M')) (w : Fin r → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) T) :
    enc ι b' ((∑ j, (X (e j) : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) T) •
      ((LinearMap.toMatrix b b' (φ j)).map ι.symm).map
        (C : T →+* MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) T)).mulVec w) =
      coeffMapAdd e (fun j => (φ j).toAddMonoidHom) (enc ι b w) := by
  classical
  let L := ∑ j, (X (e j) : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) T) •
      ((LinearMap.toMatrix b b' (φ j)).map ι.symm).map
        (C : T →+* MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) T)
  let Φ₁ : (Fin r → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) T) →+ (Mon →₀ M') :=
    (enc ι b').comp (Matrix.mulVecLin L).toAddMonoidHom
  let Φ₂ : (Fin r → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) T) →+ (Mon →₀ M') :=
    (coeffMapAdd e (fun j => (φ j).toAddMonoidHom)).comp (enc ι b)
  suffices h : Φ₁ = Φ₂ from DFunLike.congr_fun h w
  refine AddMonoidHom.functions_ext _ Φ₁ Φ₂ fun k p => ?_
  induction p using MvPolynomial.induction_on' with
  | monomial u t =>
    simp only [Φ₁, Φ₂, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      Matrix.mulVecLin_apply, enc_single, coeffMapAdd_single]
    have hL : L.mulVec (Pi.single k (monomial u t)) = ∑ j, fun i' =>
        monomial (u + Finsupp.single (e j) 1)
          (ι.symm (LinearMap.toMatrix b b' (φ j) i' k) * t) := by
      funext i'
      simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [Finset.sum_apply, L, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm (X (e j)), mul_assoc, MvPolynomial.X, monomial_mul, one_mul, C_mul_monomial,
        add_comm (Finsupp.single (e j) 1) u]
    rw [hL, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [enc_monomial_vec]
    congr 1
    simp only [map_mul, RingEquiv.apply_symm_apply, LinearMap.toMatrix_apply, map_smul]
    conv_rhs => rw [← b'.sum_repr (φ j (b k))]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [smul_smul, mul_comm]
  | add p p' hp hp' =>
    rw [Pi.single_add, map_add, map_add, hp, hp']

end Enc

end CoeffGlue

end MMP.Chow.DeterminantCurveForm
