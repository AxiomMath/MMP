module

public import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
public import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitSquare
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex

/-!
# The exponential obstruction and singular cohomology: the comparison

For a scheme `X` locally of finite type over `ℂ`, the logarithmic obstruction
`c_exp : Pic(X^an) → H²(X^an, ℤ)` is identified with the first Chern class of the underlying
topological line bundle. On the analytic side, evaluation of sections maps the exponential
sequence to `0 ⟶ ℤ ⟶ ℂ^M ⟶ ℂ^M / ℤ ⟶ 0`; on the topological side, the obstruction cocycle of a
complex line bundle is locally the coboundary of logarithms of the transition functions. The two
are compared through the isomorphism between constant-sheaf cohomology and singular cohomology on
a locally contractible metrizable space, obtained from the flasque resolution of `ℤ_M` by
sheafified singular cochains.

## Main definitions

* `quotSheaf`: the quotient `ℂ^M / ℤ_M` of all complex functions by the integers.
* `valueMap`: evaluation `𝒪_{X^an} ⟶ ℂ^{X(ℂ)}` of sections at points.
* `singCochainSheaves`: the complex of sheafified singular cochains `𝒮^•`.
* `Phi`: the comparison isomorphism `Ext²(ℤ_M, ℤ_M) ≃ H²_sing(M; ℤ)`.

## Main results

* `extClass_eq_extMk`: the extension class of the first step of an injective resolution is the
  class of the cocycle `-j`.
* `exists_obstructionCocycle_eq_coboundary`: on a trivializing open the obstruction cocycle is a
  coboundary.
* `exists_unitsLog`: evaluation of sections maps the exponential sequence to the quotient
  sequence `0 ⟶ ℤ ⟶ ℂ^M ⟶ ℂ^M / ℤ ⟶ 0`.
* `singCochainSheaves_exactAt`, `exact_constAugDeg0`, `mono_constAugDeg0`: on a locally
  contractible space `𝒮^•` is a resolution of the constant sheaf.
* `singCochainSheaves_isFlasque`: on a metrizable space the sheaves `𝒮^p` are flasque.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1
-/

@[expose] public section

namespace MMP.FourfoldProofs.LogObstructionProof

/-! ### The exponential obstruction is the first Chern class -/

section LogarithmFirstChern

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
  TopologicalSpace Filter _root_.Topology Bundle MMP.Analytic
  MMP.Analytic.ComplexPoints MMP.Analytic.Analytification

attribute [local instance] hasExt_of_enoughInjectives
  Stacks.Cohomology.Generators.picardGroupAddCommGroup
attribute [local implicit_reducible] TopCat.Sheaf

universe u

/-! ### The extension class of the first step of an injective resolution -/

section ExtClassResolution

open CochainComplex HomComplex DerivedCategory Pretriangulated

variable {C : Type*} [Category C] [Abelian C] [HasExt C]

/-- Let `I` be an injective resolution of `A` and `0 ⟶ A ⟶ I⁰ ⟶ Z ⟶ 0` a short exact sequence
whose first map is the augmentation, and let `j : Z ⟶ I¹` factor the first differential. Then the
extension class of the sequence is the class of the cocycle `-j`. -/
theorem extClass_eq_extMk {A Z : C} (I : InjectiveResolution A) (g : I.cocomplex.X 0 ⟶ Z)
    (w : ((HomologicalComplex.singleObjXSelf _ 0 A).inv ≫ I.ι.f 0) ≫ g = 0)
    (hS : (ShortComplex.mk ((HomologicalComplex.singleObjXSelf _ 0 A).inv ≫ I.ι.f 0) g w).ShortExact)
    (j : Z ⟶ I.cocomplex.X 1) (hj : g ≫ j = I.cocomplex.d 0 1) :
    hS.extClass = I.extMk (-j) 2 rfl (by
      have := hS.epi_g
      rw [← cancel_epi g, Preadditive.neg_comp, Preadditive.comp_neg, ← Category.assoc, hj]
      simp) := by
  have hj2 : j ≫ I.cocomplex.d 1 2 = 0 := by
    have := hS.epi_g
    rw [← cancel_epi g, ← Category.assoc, hj]
    simp
  let := HasDerivedCategory.standard C
  set S := ShortComplex.mk ((HomologicalComplex.singleObjXSelf _ 0 A).inv ≫ I.ι.f 0) g w
  set S' := S.map (HomologicalComplex.single C (ComplexShape.up ℤ) 0)
  set c := Cocycle.equivHomShift.symm (Cocycle.fromSingleMk ((-j) ≫
    (I.cochainComplexXIso ((1 : ℕ) : ℤ) 1 rfl).inv) (zero_add _) ((2 : ℕ) : ℤ) (by lia) (by
      simp only [Preadditive.neg_comp, Category.assoc, neg_eq_zero]
      rw [InjectiveResolution.cochainComplex_d _ _ _ 1 2 rfl rfl, Iso.inv_hom_id_assoc,
        reassoc_of% hj2, zero_comp]))
  let ι'' : S'.X₁ ⟶ I.cochainComplex := I.ι'
  let c'' : S'.X₃ ⟶ I.cochainComplex⟦(1 : ℤ)⟧ := c
  let δ' : mappingCone S'.f ⟶ S'.X₁⟦(1 : ℤ)⟧ := (mappingCone.triangle S'.f).mor₃
  let q' : mappingCone S'.f ⟶ S'.X₃ := mappingCone.descShortComplex S'
  have hδ₁ : (mappingCone.inl S'.f).v 0 (-1) (by lia) ≫ δ'.f (-1) =
      -(CochainComplex.shiftFunctorObjXIso S'.X₁ 1 (-1) 0 (by lia)).inv :=
    mappingCone.inl_v_triangle_mor₃_f _ _ _ _
  have hδ₂ : (mappingCone.inr S'.f).f 0 ≫ δ'.f 0 = 0 := mappingCone.inr_f_triangle_mor₃_f _ _
  have hq₁ : (mappingCone.inl S'.f).v 0 (-1) (by lia) ≫ q'.f (-1) = 0 :=
    mappingCone.inl_v_descShortComplex_f _ _ _ _
  have hq₂ : (mappingCone.inr S'.f).f 0 ≫ q'.f 0 = S'.g.f 0 :=
    mappingCone.inr_f_descShortComplex_f _ _
  have hι : ι''.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ I.ι.f 0 ≫
      (I.cochainComplexXIso _ _ (by simp)).inv := I.ι'_f_zero
  have e1 : (CochainComplex.shiftFunctorObjXIso I.cochainComplex 1 (-1) 0 (by lia)).inv = 𝟙 _ := rfl
  have e2 : (CochainComplex.shiftFunctorObjXIso S'.X₁ 1 (-1) 0 (by lia)).inv = 𝟙 _ := rfl
  have e3 : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv = 𝟙 _ := rfl
  have e4 : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv ≫ I.ι.f 0 :
      A ⟶ I.cocomplex.X 0) = (I.ι.f 0 : A ⟶ I.cocomplex.X 0) := by
    rw [e3]; exact Category.id_comp _
  have e5 : ∀ (h : I.cocomplex.X 0 ⟶ I.cochainComplex.X 0),
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv ≫ I.ι.f 0 ≫ h :
        A ⟶ I.cochainComplex.X 0) = (I.ι.f 0 ≫ h : A ⟶ I.cochainComplex.X 0) := fun h => by
    rw [← Category.assoc, e4]
  have hc : c''.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Z).hom ≫ (-j) ≫
      (I.cochainComplexXIso 1 1 rfl).inv := by
    simp [c'', c, Cocycle.equivHomShift, Cochain.rightShift_v _ 1 0 (zero_add 1) 0 0 (add_zero 0) 1
      (by lia), Cochain.fromSingleMk_v]
  have key : Q.map (δ' ≫ ι''⟦(1 : ℤ)⟧') = Q.map (q' ≫ c'') := by
    apply Q_map_eq_of_homotopy
    refine mappingCone.descHomotopy _ _ _ 0 (Cochain.fromSingleMk
      (-((I.cochainComplexXIso 0 0 rfl).inv ≫
        (I.cochainComplex.shiftFunctorObjXIso 1 (-1) 0 (by lia)).inv)) (zero_add (-1))) ?_ ?_
    · ext p q hpq
      by_cases hp : p = 0
      · subst hp
        obtain rfl : q = -1 := by lia
        simp only [Cochain.add_v, Cochain.comp_v _ _ (add_zero (-1)) 0 (-1) (-1) (by lia) (by lia),
          Cochain.comp_v _ _ (zero_add (-1)) 0 0 (-1) (by lia) (by lia), Cochain.zero_v,
          Cochain.fromSingleMk_v, Cochain.ofHom_v, HomologicalComplex.comp_f, δ_zero, zero_add,
          reassoc_of% hδ₁, reassoc_of% hq₁, zero_comp, add_zero, shiftFunctor_map_f']
        simp only [e1, e2, Category.comp_id, Preadditive.neg_comp, Preadditive.comp_neg,
          Category.id_comp, neg_inj]
        change ι''.f 0 = _
        simp only [S', S, ShortComplex.map_f, HomologicalComplex.single_map_f_self]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, hι, e5]
      · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
    · ext p
      by_cases hp : p = 0
      · subst hp
        simp only [Cochain.add_v]
        rw [δ_v (-1) 0 (by lia) _ 0 0 (by lia) (-1) 1 (by lia) (by lia)]
        simp only [Cochain.ofHom_v, HomologicalComplex.comp_f, reassoc_of% hδ₂, reassoc_of% hq₂,
          zero_comp, Cochain.fromSingleMk_v]
        simp only [hc, e1, shiftFunctor_obj_d', HomologicalComplex.single_obj_d, zero_comp, smul_zero,
          add_zero, Int.negOnePow_one, Units.neg_smul, one_smul]
        have hd : I.cochainComplex.d (-1 + 1) (0 + 1) = (I.cochainComplexXIso 0 0 rfl).hom ≫
            I.cocomplex.d 0 1 ≫ (I.cochainComplexXIso 1 1 rfl).inv :=
          I.cochainComplex_d _ _ 0 1 (by simp) (by simp)
        have h0 : S'.X₂.d 0 1 = 0 :=
          (HomologicalComplex.isZero_single_obj_X _ 0 _ 1 (by simp)).eq_of_tgt _ _
        have hg : S'.g.f 0 = (HomologicalComplex.singleObjXSelf _ 0 (I.cocomplex.X 0)).hom ≫ g ≫
            (HomologicalComplex.singleObjXSelf _ 0 Z).inv :=
          HomologicalComplex.single_map_f_self _ _ _
        rw [hd, h0, hg]
        simp only [zero_comp, smul_zero, add_zero, Category.comp_id, Category.assoc,
          Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Iso.inv_hom_id_assoc,
          Iso.inv_hom_id_assoc, reassoc_of% hj]
        exact (add_neg_cancel _).symm
      · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  ext
  rw [ShortComplex.ShortExact.extClass_hom, InjectiveResolution.extMk_hom]
  simp only [ShortComplex.ShortExact.singleδ, triangleOfSESδ, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀, ShiftedHom.map]
  simp only [singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id]
  have := mappingCone.quasiIso_descShortComplex (hS.map_of_exact
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0))
  change inv (Q.map q') ≫ Q.map δ' ≫ (Q.commShiftIso (1 : ℤ)).hom.app S'.X₁ =
    (Q.map c'' ≫ (Q.commShiftIso (1 : ℤ)).hom.app I.cochainComplex) ≫
      (inv (Q.map ι'') ≫ 𝟙 _)⟦(1 : ℤ)⟧'
  rw [Category.comp_id, IsIso.inv_comp_eq,
    ← cancel_mono ((CategoryTheory.shiftFunctor (DerivedCategory C) (1 : ℤ)).map (Q.map ι''))]
  simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  erw [Category.comp_id]
  rw [← Functor.commShiftIso_hom_naturality, ← Functor.map_comp_assoc, key, Functor.map_comp_assoc]

end ExtClassResolution

/-! ### The first Chern class from logarithms of transition functions -/

section SingularSide

open MMP.SingularChain MMP.SingularCochain Complex
open FiberBundle MMP.Analytic.ComplexLineBundle

variable {B : Type} [TopologicalSpace B]

variable {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
  [TopologicalSpace (TotalSpace ℂ E)] [∀ b, TopologicalSpace (E b)] [FiberBundle ℂ E]
  [VectorBundle ℂ ℂ E]

/-- Changing the trivialization of the edge phase adds the logarithmic increment of the
transition function. -/
theorem edgePhase_change {e e' : Trivialization ℂ (Bundle.TotalSpace.proj : TotalSpace ℂ E → B)}
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] {τ : Simplex B 1}
    (hτ : Set.range τ ⊆ e.baseSet) (hτ' : Set.range τ ⊆ e'.baseSet) :
    edgePhase (E := E) e' τ = edgePhase (E := E) e τ + logIncrement (transition e e') τ := by
  have hs := range_subset_simplexTriv (E := E) (MemTrivializationAtlas.out (e := e)) hτ
  simp only [edgePhase]
  rw [add_assoc, logIncrement_mul (g := transition (simplexTriv (E := E) τ) e)
    (h := transition e e')]
  · intro x
    rw [transition_trans (hs ⟨x, rfl⟩) (hτ ⟨x, rfl⟩) (hτ' ⟨x, rfl⟩), mul_comm]
  · exact exists_continuous_log_comp τ continuousOn_transition
      (fun y hy => transition_ne_zero hy) (Set.subset_inter hs hτ)
  · exact exists_continuous_log_comp τ continuousOn_transition
      (fun y hy => transition_ne_zero hy) (Set.subset_inter hτ hτ')

/-- The `0`-cochain of logarithms of the reference coordinates in a trivialization. -/
noncomputable def vertexLog (e : Trivialization ℂ (π ℂ E)) : Simplex B 0 → ℂ :=
  fun ρ => log (vertexCoord (E := E) e (ρ (stdSimplex.vertex 0)))

/-- The first face of a `1`-simplex starts at its second vertex. -/
lemma face00_vertex : (face 0 0) (stdSimplex.vertex 0) =
    (stdSimplex.vertex 1 : stdSimplex ℝ (Fin 2)) := by
  simp [face, stdSimplex.map_vertex]

/-- The second face of a `1`-simplex starts at its first vertex. -/
lemma face01_vertex : (face 0 1) (stdSimplex.vertex 0) =
    (stdSimplex.vertex 0 : stdSimplex ℝ (Fin 2)) := by
  simp [face, stdSimplex.map_vertex]

/-- The coboundary of `vertexLog e` on a `1`-simplex is the difference of the logarithms of the
reference coordinates at its two vertices. -/
lemma coboundary_vertexLog (e : Trivialization ℂ (π ℂ E)) (τ : Simplex B 1) :
    coboundary ℂ 0 (vertexLog (E := E) e) τ =
      log (vertexCoord (E := E) e (τ (stdSimplex.vertex 1))) -
        log (vertexCoord (E := E) e (τ (stdSimplex.vertex 0))) := by
  rw [coboundary_apply]
  change ∑ i : Fin 2, _ = _
  rw [Fin.sum_univ_two]
  simp only [vertexLog, ContinuousMap.comp_apply, face00_vertex, face01_vertex]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, neg_one_mul]
  ring

/-- **On a trivializing open the obstruction cocycle is a coboundary.** The integer `1`-cochain
`(edgePhase e - δ log vertexCoord e) / 2πi` has coboundary the obstruction cocycle on every
singular `2`-simplex in the base of `e`. -/
lemma exists_obstructionCocycle_eq_coboundary (e : Trivialization ℂ (π ℂ E))
    [MemTrivializationAtlas e] :
    ∃ w : Simplex B 1 → ℤ,
      (∀ τ : Simplex B 1, Set.range τ ⊆ e.baseSet →
        (w τ : ℂ) * (2 * Real.pi * I) =
          edgePhase (E := E) e τ - coboundary ℂ 0 (vertexLog (E := E) e) τ) ∧
      ∀ σ : Simplex B 2, Set.range σ ⊆ e.baseSet →
        obstructionCocycle E σ = coboundary ℤ 1 w σ := by
  classical
  have hex : ∀ τ : Simplex B 1, Set.range τ ⊆ e.baseSet → ∃ k : ℤ,
      edgePhase (E := E) e τ - coboundary ℂ 0 (vertexLog (E := E) e) τ = k * (2 * Real.pi * I) := by
    intro τ hτ
    refine Complex.exp_eq_one_iff.1 ?_
    have h1 : τ (stdSimplex.vertex 1) ∈ e.baseSet := hτ ⟨_, rfl⟩
    have h0 : τ (stdSimplex.vertex 0) ∈ e.baseSet := hτ ⟨_, rfl⟩
    have hv1 := vertexCoord_ne_zero (E := E) (e := e) h1
    have hv0 := vertexCoord_ne_zero (E := E) (e := e) h0
    rw [exp_sub, exp_edgePhase hτ, coboundary_vertexLog, exp_sub, exp_log hv1, exp_log hv0]
    exact div_self (div_ne_zero hv1 hv0)
  let w : Simplex B 1 → ℤ := fun τ =>
    if h : ∃ k : ℤ, edgePhase (E := E) e τ - coboundary ℂ 0 (vertexLog (E := E) e) τ =
      k * (2 * Real.pi * I) then h.choose else 0
  have hw : ∀ τ : Simplex B 1, Set.range τ ⊆ e.baseSet →
      (w τ : ℂ) * (2 * Real.pi * I) =
        edgePhase (E := E) e τ - coboundary ℂ 0 (vertexLog (E := E) e) τ := by
    intro τ hτ
    have h := hex τ hτ
    simp only [w, dif_pos h]
    exact h.choose_spec.symm
  refine ⟨w, hw, fun σ hσ => ?_⟩
  have hface : ∀ k : Fin 3, Set.range (σ.comp (face 1 k)) ⊆ e.baseSet :=
    fun _ _ ⟨t, ht⟩ => hσ ⟨_, ht⟩
  have hcast : ((coboundary ℤ 1 w σ : ℤ) : ℂ) * (2 * Real.pi * I) =
      ∑ k : Fin 3, (-1 : ℂ) ^ (k : ℕ) * ((w (σ.comp (face 1 k)) : ℂ) * (2 * Real.pi * I)) := by
    rw [coboundary_apply]
    change ((∑ k : Fin 3, (-1 : ℤ) ^ (k : ℕ) * w (σ.comp (face 1 k)) : ℤ) : ℂ) * _ = _
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdd := congr_fun (coboundary_coboundary (R := ℂ) 0 (vertexLog (E := E) e)) σ
  rw [coboundary_apply] at hdd
  change ∑ k : Fin 3, (-1 : ℂ) ^ (k : ℕ) *
    coboundary ℂ 0 (vertexLog (E := E) e) (σ.comp (face 1 k)) = 0 at hdd
  have key : (obstructionCocycle E σ : ℂ) * (2 * Real.pi * I) =
      ((coboundary ℤ 1 w σ : ℤ) : ℂ) * (2 * Real.pi * I) := by
    rw [obstructionCocycle_mul hσ, obstructionPhase_eq_coboundary hσ, hcast, coboundary_apply]
    change ∑ k : Fin 3, _ = _
    simp only [hw _ (hface _), mul_sub, Finset.sum_sub_distrib, hdd, sub_zero]
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero key

/-- The coordinate in a trivialization of a section over an open, extended by `0`. -/
noncomputable def frameCoord (e : Trivialization ℂ (π ℂ E)) (U : Opens B)
    (f : ∀ y : U, E y) (y : B) : ℂ := by
  classical
  exact if hy : y ∈ U then (e ⟨y, f ⟨y, hy⟩⟩).2 else 0

/-- On `U`, `frameCoord e U f` is the coordinate of `f` in the trivialization `e`. -/
lemma frameCoord_of_mem (e : Trivialization ℂ (π ℂ E)) (U : Opens B)
    (f : ∀ y : U, E y) {y : B} (hy : y ∈ U) : frameCoord e U f y = (e ⟨y, f ⟨y, hy⟩⟩).2 := by
  simp [frameCoord, hy]

/-- **A continuous section with nonzero value has, near the point, a coordinate with a
continuous logarithm.** -/
lemma exists_frameCoord_log (e : Trivialization ℂ (π ℂ E)) [MemTrivializationAtlas e]
    (U : Opens B) (f : ∀ y : U, E y)
    (hf : Continuous fun y : U => (⟨y.1, f y⟩ : TotalSpace ℂ E)) {x : B} (hxU : x ∈ U)
    (hxe : x ∈ e.baseSet) (hne : f ⟨x, hxU⟩ ≠ 0) :
    ∃ U' : Opens B, x ∈ U' ∧ U' ≤ U ∧ (U' : Set B) ⊆ e.baseSet ∧
      ∃ Lg : B → ℂ, ContinuousOn Lg U' ∧ ∀ y ∈ U', exp (Lg y) = frameCoord e U f y := by
  set S : Set B := (U : Set B) ∩ e.baseSet
  have hSo : IsOpen S := U.isOpen.inter e.open_baseSet
  have hcont : ContinuousOn (frameCoord e U f) S := by
    rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun y : S => (⟨y.1, f ⟨y.1, y.2.1⟩⟩ : TotalSpace ℂ E) :=
      hf.comp (continuous_inclusion (fun _ hy => hy.1) : Continuous (Set.inclusion
        (fun _ hy => hy.1 : S ⊆ (U : Set B))))
    have h2 : Continuous fun y : S => e ⟨y.1, f ⟨y.1, y.2.1⟩⟩ :=
      e.continuousOn.comp_continuous h1 (fun y => e.mem_source.2 y.2.2)
    refine (continuous_snd.comp h2).congr fun y => ?_
    simp [Set.restrict, frameCoord_of_mem e U f y.2.1]
  have hx0 : frameCoord e U f x ≠ 0 := by
    rw [frameCoord_of_mem e U f hxU]
    intro h
    apply hne
    exact (e.continuousLinearEquivAt ℂ x hxe).injective
      (a₁ := f ⟨x, hxU⟩) (a₂ := 0) (by
        rw [map_zero, Trivialization.continuousLinearEquivAt_apply]
        exact h)
  set c₀ := frameCoord e U f x
  have hball : IsOpen (Metric.ball c₀ ‖c₀‖) := Metric.isOpen_ball
  obtain ⟨W, hWo, hW⟩ := (continuousOn_iff'.1 hcont) _ hball
  refine ⟨⟨S ∩ W, hSo.inter hWo⟩, ⟨⟨hxU, hxe⟩, ?_⟩, fun y hy => hy.1.1, fun y hy => hy.1.2, ?_⟩
  · exact ((Set.ext_iff.1 hW x).1 ⟨Metric.mem_ball_self (norm_pos_iff.2 hx0), hxU, hxe⟩).1
  · have hmem : ∀ y ∈ S ∩ W, frameCoord e U f y / c₀ ∈ slitPlane := by
      intro y hy
      have hyb : frameCoord e U f y ∈ Metric.ball c₀ ‖c₀‖ :=
        ((Set.ext_iff.1 hW y).2 ⟨hy.2, hy.1⟩).1
      have hlt : ‖frameCoord e U f y / c₀ - 1‖ < 1 := by
        rw [Metric.mem_ball, dist_eq_norm] at hyb
        rw [div_sub_one hx0, norm_div]
        exact (div_lt_one (norm_pos_iff.2 hx0)).2 hyb
      have := mem_slitPlane_of_norm_lt_one hlt
      rwa [add_sub_cancel] at this
    refine ⟨fun y => log c₀ + log (frameCoord e U f y / c₀), ?_, fun y hy => ?_⟩
    · refine continuousOn_const.add (ContinuousOn.clog ?_ hmem)
      exact (hcont.mono fun y hy => hy.1).div continuousOn_const fun _ _ => hx0
    · change exp (log c₀ + log (frameCoord e U f y / c₀)) = _
      rw [exp_add, exp_log hx0, exp_log (slitPlane_ne_zero (hmem y hy)), mul_div_cancel₀ _ hx0]

/-- Changing the trivialization multiplies the coordinate by the transition function. -/
lemma coord_eq_mul_transition {ei ej : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas ei]
    [MemTrivializationAtlas ej] {z : B} (hz : z ∈ ei.baseSet ∩ ej.baseSet) (v : E z) :
    (ej ⟨z, v⟩).2 = (ei ⟨z, v⟩).2 * transition ei ej z := by
  rw [← coordChangeL_eq_mul_transition hz, Trivialization.coordChangeL_apply ei ej hz,
    Trivialization.symm_apply_apply_mk ei hz.1]

/-- The coordinate of a scalar multiple. -/
lemma coord_smul (e : Trivialization ℂ (π ℂ E)) [MemTrivializationAtlas e] {z : B}
    (hz : z ∈ e.baseSet) (c : ℂ) (v : E z) : (e ⟨z, c • v⟩).2 = c * (e ⟨z, v⟩).2 :=
  (e.linear ℂ hz).map_smul c v

/-- **The local primitive of the difference of two edge-phase cochains.** Two frames `fᵢ`, `fⱼ`
related by `fⱼ = exp (2πi φ) • fᵢ`, with continuous logarithms `Lᵢ`, `Lⱼ` of their coordinates,
give on the overlap an integer function `a` whose coboundary is the difference of the integer
cochains `wⱼ - wᵢ` of `exists_obstructionCocycle_eq_coboundary`, and whose value is
`(Lⱼ - log vⱼ)/2πi - (Lᵢ - log vᵢ)/2πi - φ`. -/
lemma exists_int_primitive {ei ej : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas ei]
    [MemTrivializationAtlas ej] {Ui Uj : Opens B} (fi : ∀ y : Ui, E y) (fj : ∀ y : Uj, E y)
    {Li Lj : B → ℂ} (hLi : ∀ y ∈ Ui, exp (Li y) = frameCoord ei Ui fi y)
    (hLj : ∀ y ∈ Uj, exp (Lj y) = frameCoord ej Uj fj y)
    (V : Opens B) (hVi : V ≤ Ui) (hVj : V ≤ Uj) (hVei : (V : Set B) ⊆ ei.baseSet)
    (hVej : (V : Set B) ⊆ ej.baseSet) (hLic : ContinuousOn Li V) (hLjc : ContinuousOn Lj V)
    {φ : B → ℂ} (hφc : ContinuousOn φ V)
    (hφ : ∀ z (hz : z ∈ V), fj ⟨z, hVj hz⟩ = exp (2 * Real.pi * I * φ z) • fi ⟨z, hVi hz⟩)
    {wi wj : Simplex B 1 → ℤ}
    (hwi : ∀ τ : Simplex B 1, Set.range τ ⊆ ei.baseSet →
      (wi τ : ℂ) * (2 * Real.pi * I) =
        edgePhase (E := E) ei τ - coboundary ℂ 0 (vertexLog (E := E) ei) τ)
    (hwj : ∀ τ : Simplex B 1, Set.range τ ⊆ ej.baseSet →
      (wj τ : ℂ) * (2 * Real.pi * I) =
        edgePhase (E := E) ej τ - coboundary ℂ 0 (vertexLog (E := E) ej) τ) :
    ∃ a : V → ℤ,
      (∀ (τ : Simplex B 1) (hτ : Set.range τ ⊆ V),
        wj τ - wi τ = a ⟨_, hτ ⟨stdSimplex.vertex 1, rfl⟩⟩ - a ⟨_, hτ ⟨stdSimplex.vertex 0, rfl⟩⟩) ∧
      ∀ z : V, (a z : ℂ) = (Lj z - log (vertexCoord (E := E) ej z)) / (2 * Real.pi * I) -
        (Li z - log (vertexCoord (E := E) ei z)) / (2 * Real.pi * I) - φ z := by
  classical
  set ℓ : B → ℂ := fun z => Lj z - Li z - 2 * Real.pi * I * φ z with hℓ
  have hexpℓ : ∀ z ∈ V, exp (ℓ z) = transition ei ej z := by
    intro z hz
    have hz2 : z ∈ ei.baseSet ∩ ej.baseSet := ⟨hVei hz, hVej hz⟩
    have hLz := hLj z (hVj hz)
    rw [frameCoord_of_mem ej Uj fj (hVj hz), hφ z hz, coord_eq_mul_transition hz2,
      coord_smul ei hz2.1, ← frameCoord_of_mem ei Ui fi (hVi hz), ← hLi z (hVi hz)] at hLz
    rw [hℓ]
    simp only
    rw [exp_sub, exp_sub, hLz]
    have := exp_ne_zero (Li z)
    have := exp_ne_zero (2 * Real.pi * I * φ z)
    field_simp
  have hint : ∀ z : V, ∃ k : ℤ, (Lj z - log (vertexCoord (E := E) ej z)) / (2 * Real.pi * I) -
      (Li z - log (vertexCoord (E := E) ei z)) / (2 * Real.pi * I) - φ z = k := by
    intro z
    have hz2 : (z : B) ∈ ei.baseSet ∩ ej.baseSet := ⟨hVei z.2, hVej z.2⟩
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 (show exp (ℓ z - (log (vertexCoord (E := E) ej z) -
        log (vertexCoord (E := E) ei z))) = 1 by
      have hvi := vertexCoord_ne_zero (E := E) (e := ei) hz2.1
      have hvj := vertexCoord_ne_zero (E := E) (e := ej) hz2.2
      rw [exp_sub, hexpℓ z z.2, exp_sub, exp_log hvi, exp_log hvj,
        vertexCoord_eq (E := E) hz2.1 hz2.2]
      have := transition_ne_zero (e := ei) (e' := ej) hz2
      field_simp)
    refine ⟨k, ?_⟩
    rw [← mul_left_inj' two_pi_I_ne_zero, ← hk]
    simp only [hℓ]
    field_simp
    ring
  choose a ha using hint
  refine ⟨a, fun τ hτ => ?_, fun z => (ha z).symm⟩
  have hτi : Set.range τ ⊆ ei.baseSet := hτ.trans hVei
  have hτj : Set.range τ ⊆ ej.baseSet := hτ.trans hVej
  have hinc := edgePhase_change (E := E) hτi hτj
  obtain ⟨Lτ, hLτ⟩ : ∃ Lτ : C(stdSimplex ℝ (Fin 2), ℂ), ∀ x, Lτ x = ℓ (τ x) :=
    ⟨⟨fun x => ℓ (τ x), ((hLjc.sub hLic).sub (continuousOn_const.mul hφc)).comp_continuous
      τ.continuous fun x => hτ ⟨x, rfl⟩⟩, fun _ => rfl⟩
  have hlog := logIncrement_eq (f := transition ei ej) Lτ (fun x => by
    rw [hLτ, hexpℓ _ (hτ ⟨x, rfl⟩)])
  have key : ((wj τ - wi τ : ℤ) : ℂ) * (2 * Real.pi * I) =
      ((a ⟨_, hτ ⟨stdSimplex.vertex 1, rfl⟩⟩ - a ⟨_, hτ ⟨stdSimplex.vertex 0, rfl⟩⟩ : ℤ) : ℂ) *
        (2 * Real.pi * I) := by
    push_cast
    rw [sub_mul, sub_mul, hwi τ hτi, hwj τ hτj, hinc, hlog, hLτ, hLτ, coboundary_vertexLog,
      coboundary_vertexLog, ← ha, ← ha]
    simp only [hℓ]
    field_simp
    ring
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero key

end SingularSide

section FunSheaf

variable (M : TopCat.{0}) (A : Type) [AddCommGroup A]

/-- The presheaf of all `A`-valued functions. -/
noncomputable def funPresheaf : TopCat.Presheaf AddCommGrpCat.{0} M where
  obj V := AddCommGrpCat.of (V.unop → A)
  map i := AddCommGrpCat.ofHom
    { toFun := fun f x => f ⟨x.1, i.unop.le x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The sheaf of all `A`-valued functions. -/
noncomputable def funSheaf : Sheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0} where
  obj := funPresheaf M A
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)]
    exact TopCat.Presheaf.isSheaf_of_iso (NatIso.ofComponents (fun V => Iso.refl _) (fun _ => rfl))
      (TopCat.Presheaf.toTypes_isSheaf M (fun _ => A))

/-- The constant sheaf `ℤ_M` of integers on `M`. -/
noncomputable abbrev ZSh : Sheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0} :=
  (constantSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).obj (.of ℤ)

/-- The integers as constant functions on `M`. -/
noncomputable def constGlobal : AddCommGrpCat.of ℤ ⟶ (funSheaf M ℂ).obj.obj (op ⊤) :=
  AddCommGrpCat.ofHom
      { toFun := fun n (_ : (⊤ : Opens M)) => (n : ℂ)
        map_zero' := by funext; simp
        map_add' := fun _ _ => by funext; simp }

/-- The inclusion `ℤ_M ⟶ ℂ^M` of the integers into all complex functions. -/
noncomputable def constFun : ZSh M ⟶ funSheaf M ℂ :=
  ((constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{0} isTerminalTop).homEquiv
    _ _).symm (constGlobal M)

/-- The inclusion `ℤ_M ⟶ ℂ^M` of the integers into all complex functions is a monomorphism. -/
theorem constFun_mono : Mono (constFun M) := by
  let J := Opens.grothendieckTopology M
  let adj1 := constantPresheafAdj AddCommGrpCat.{0} (isTerminalTop : IsTerminal (⊤ : Opens M))
  let adj2 := sheafificationAdjunction J AddCommGrpCat.{0}
  let c : (Functor.const (Opens M)ᵒᵖ).obj (AddCommGrpCat.of ℤ) ⟶ (funSheaf M ℂ).obj :=
    (adj1.homEquiv (AddCommGrpCat.of ℤ) (funSheaf M ℂ).obj).symm (constGlobal M)
  have hc : constFun M = (adj2.homEquiv _ _).symm c := by
    exact congrArg (fun F => (F (AddCommGrpCat.of ℤ) (funSheaf M ℂ)).symm (constGlobal M))
      (Adjunction.comp_homEquiv adj1 adj2)
  have hfac : toSheafify J _ ≫ (constFun M).hom = c := by
    rw [hc]
    have := adj2.homEquiv_unit (f := (adj2.homEquiv _ (funSheaf M ℂ)).symm c)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have hcapp : ∀ (U : (Opens M)ᵒᵖ) (n : ℤ) (y : U.unop), (c.app U n : U.unop → ℂ) y = n :=
    fun _ _ _ => rfl
  haveI : Presheaf.IsLocallyInjective J c := ⟨fun {U} x x' h => by
    intro y hy
    have e1 := hcapp U x ⟨y, hy⟩
    have e2 := hcapp U x' ⟨y, hy⟩
    rw [h] at e1
    have hxx : x = x' := by exact_mod_cast e1.symm.trans e2
    subst hxx
    exact ⟨U.unop, 𝟙 _, by simp [Presheaf.equalizerSieve], hy⟩⟩
  have hs := Presheaf.isLocallySurjective_toSheafify' J
      ((Functor.const (Opens M)ᵒᵖ).obj (AddCommGrpCat.of ℤ))
  haveI : Presheaf.IsLocallyInjective J (constFun M).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac (J := J)
      (f₁ := toSheafify J ((Functor.const (Opens M)ᵒᵖ).obj (AddCommGrpCat.of ℤ)))
      (f₂ := (constFun M).hom) c hfac
  exact Sheaf.mono_of_isLocallyInjective (constFun M)

/-- The quotient `ℂ^M / ℤ_M` of all complex functions by the integers. -/
noncomputable abbrev quotSheaf : Sheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0} :=
  cokernel (constFun M)

/-- The short exact sequence `0 ⟶ ℤ_M ⟶ ℂ^M ⟶ ℂ^M / ℤ_M ⟶ 0`. -/
theorem quotSeq_shortExact :
    (ShortComplex.mk (constFun M) (cokernel.π (constFun M)) (cokernel.condition _)).ShortExact :=
  haveI := constFun_mono M
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

end FunSheaf

section Residue

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- The residue `𝒪_{U,y} → ℂ` at a `ℂ`-point `y` of a chart: the value at `z(y)`. -/
noncomputable def residue (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U) :
    c.StalkRing (c.coords y) →+* ℂ :=
  Ideal.Quotient.lift (c.ideal.map (polyGermHom (c.coords y)))
    ((Germ.valueRingHom).comp (holGerms (c.coords y)).subtype) (by
      have : c.ideal.map (polyGermHom (c.coords y)) ≤
          RingHom.ker ((Germ.valueRingHom).comp (holGerms (c.coords y)).subtype) := by
        rw [Ideal.map_le_iff_le_comap]
        intro q hq
        rw [Ideal.mem_comap, RingHom.mem_ker]
        change MvPolynomial.eval (c.coords y) q = 0
        rw [← c.evalHom_pres, (RingHom.mem_ker).1 hq, map_zero]
      exact fun g hg => this hg)

/-- The residue of the class of a holomorphic germ is the value of the germ. -/
lemma residue_mk (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    (g : holGerms (c.coords y)) :
    residue c y (Chart.StalkRing.mk c _ g) = Germ.value (g : Germ (𝓝 (c.coords y)) ℂ) :=
  Ideal.Quotient.lift_mk _ _ _

/-- The ring of sections over an affine open of a scheme locally of finite type over `ℂ` is
generated by finitely many sections over `ℂ`. -/
lemma exists_gens [LocallyOfFiniteType sX] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (gen : Fin n → Γ(X, U)),
      Function.Surjective (MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen) := by
  have h₁ : (sX.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType (f := sX) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₂ : (ComplexPoints.baseRingHom sX U).FiniteType := by
    have : ComplexPoints.baseRingHom sX U =
        (sX.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom := rfl
    rw [this]
    exact h₁.comp (RingHom.FiniteType.of_surjective _ fun a =>
      ⟨(Scheme.ΓSpecIso (.of ℂ)).hom a, Iso.hom_inv_id_apply _ a⟩)
  letI := (ComplexPoints.baseRingHom sX U).toAlgebra
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h₂
  refine ⟨n, fun i => φ (MvPolynomial.X i), ?_⟩
  have : MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U)
      (fun i => φ (MvPolynomial.X i)) = φ.toRingHom :=
    MvPolynomial.ringHom_ext (fun a => by simp [RingHom.algebraMap_toAlgebra])
      (fun i => by simp)
  rw [this]
  exact hφ

/-- For `X` locally of finite type over `ℂ`, every `ℂ`-point lies in a chart. -/
lemma exists_chart [LocallyOfFiniteType sX] (x : space sX) :
    ∃ c : Chart sX, x ∈ ComplexPoints.chart c.U := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (Opens.mem_top (ComplexPoints.toScheme x))
  obtain ⟨n, gen, h⟩ := exists_gens (sX := sX) hU
  exact ⟨⟨U, hU, n, gen, h⟩, ComplexPoints.mem_chart_iff.2 hxU⟩

variable {n : ℕ}

/-- A holomorphic germ is the germ of a function that is differentiable near the base point. -/
lemma exists_rep {p : Fin n → ℂ} (g : holGerms p) :
    ∃ f : (Fin n → ℂ) → ℂ, (g : Germ (𝓝 p) ℂ) = f ∧ ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y := by
  obtain ⟨f, hf, hd⟩ := g.2
  exact ⟨f, hf.symm, hd⟩

/-- Every element of the stalk ring of a chart is the class of a holomorphic germ. -/
lemma mk_surjective (c : Chart sX) (p : Fin c.n → ℂ) (a : c.StalkRing p) :
    ∃ g, Chart.StalkRing.mk c p g = a :=
  Ideal.Quotient.mk_surjective a

/-- The residue of the class of the germ of `f` is `f` evaluated at the coordinates of the
point. -/
lemma residue_of_eq_mk (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    {a : c.StalkRing (c.coords y)} {g : holGerms (c.coords y)} {f : (Fin c.n → ℂ) → ℂ}
    (ha : a = Chart.StalkRing.mk c _ g) (hg : (g : Germ (𝓝 (c.coords y)) ℂ) = f) :
    residue c y a = f (c.coords y) := by
  rw [ha, residue_mk, hg]
  rfl

/-- A function representing a holomorphic germ is differentiable near the base point. -/
lemma eventually_differentiableAt_of_coe_eq {p : Fin n → ℂ} (g : holGerms p)
    {f : (Fin n → ℂ) → ℂ} (hf : (g : Germ (𝓝 p) ℂ) = f) :
    ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y := by
  obtain ⟨f', hf', hd⟩ := exists_rep g
  have heq : f' =ᶠ[𝓝 p] f := Germ.coe_eq.1 (hf'.symm.trans hf)
  exact (hd.and heq.eventuallyEq_nhds).mono fun y hy => hy.1.congr_of_eventuallyEq hy.2.symm

/-- The residue is compatible with the transition map of a morphism of charts. -/
lemma residue_transition {c d : Chart sX} (m : ChartHom c d)
    (y : ComplexPoints.chart (sX := sX) d.U) (a : c.StalkRing (c.coords (m.incl y))) :
    residue d y (m.transition y a) = residue c (m.incl y) a := by
  obtain ⟨g, rfl⟩ := mk_surjective c _ a
  obtain ⟨f, hf, -⟩ := exists_rep g
  rw [m.transition_mk, residue_mk, residue_mk, coe_holPullback, hf, Germ.coe_compTendsto]
  change f (m.polyMap (d.coords y)) = f (c.coords (m.incl y))
  rw [m.coords_incl]

/-- Two charts containing a common `ℂ`-point both map to a third chart containing it. -/
lemma exists_chartHom_chartHom [LocallyOfFiniteType sX] (c d : Chart sX)
    {y : ComplexPoints sX} (hc : y ∈ ComplexPoints.chart c.U)
    (hd : y ∈ ComplexPoints.chart d.U) :
    ∃ (e : Chart sX) (_ : ChartHom c e) (_ : ChartHom d e), y ∈ ComplexPoints.chart e.U := by
  obtain ⟨U, hU, hyU, hUcd⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (U := c.U ⊓ d.U) (x := y.toScheme)
    ⟨ComplexPoints.mem_chart_iff.1 hc, ComplexPoints.mem_chart_iff.1 hd⟩
  obtain ⟨k, g, hg⟩ := exists_gens (sX := sX) hU
  let gen : Fin (c.n + d.n + k) → Γ(X, U) :=
    Fin.append (Fin.append
      (fun i => X.presheaf.map (homOfLE (hUcd.trans inf_le_left)).op (c.gen i))
      (fun j => X.presheaf.map (homOfLE (hUcd.trans inf_le_right)).op (d.gen j))) g
  have hsurj : Function.Surjective
      (MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen) := by
    intro a
    obtain ⟨q, rfl⟩ := hg a
    refine ⟨MvPolynomial.rename (Fin.natAdd (c.n + d.n)) q, ?_⟩
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
    congr 1
    funext i
    exact Fin.append_right _ _ i
  let e : Chart sX := ⟨U, hU, c.n + d.n + k, gen, hsurj⟩
  refine ⟨e, ⟨hUcd.trans inf_le_left,
    fun i => MvPolynomial.X (Fin.castAdd k (Fin.castAdd d.n i)), fun i => ?_⟩,
    ⟨hUcd.trans inf_le_right, fun j => MvPolynomial.X (Fin.castAdd k (Fin.natAdd c.n j)),
      fun j => ?_⟩, ComplexPoints.mem_chart_iff.2 hyU⟩
  · change _ = MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen (MvPolynomial.X _)
    rw [MvPolynomial.eval₂Hom_X']
    simp only [gen, Fin.append_left]
  · change _ = MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen (MvPolynomial.X _)
    rw [MvPolynomial.eval₂Hom_X']
    simp only [gen, Fin.append_left, Fin.append_right]

/-- For a compatible family, the residue at a point does not depend on the chart. -/
lemma residue_eq_of_isCompatible [LocallyOfFiniteType sX] {W : Opens (space sX)}
    {s : ∀ x : W, Fibre x.1} (hs : IsCompatible s) (x : W) (c d : Chart sX)
    (hc : x.1 ∈ ComplexPoints.chart c.U) (hd : x.1 ∈ ComplexPoints.chart d.U) :
    residue c ⟨x.1, hc⟩ (s x ⟨c, hc⟩) = residue d ⟨x.1, hd⟩ (s x ⟨d, hd⟩) := by
  obtain ⟨e, m₁, m₂, he⟩ := exists_chartHom_chartHom c d hc hd
  exact ((residue_transition m₁ ⟨x.1, he⟩ _).symm.trans (congrArg _ (hs c e m₁ x he))).trans
    ((congrArg _ (hs d e m₂ x he)).symm.trans (residue_transition m₂ ⟨x.1, he⟩ _))

/-- The `ℂ`-points of an open `U` at which the value of a section `f ∈ Γ(X, U)` lies in an open
set form an open subset of `X(ℂ)`. -/
lemma isOpen_setOf_evalHom_mem (U : X.Opens) (f : Γ(X, U)) {T : Set ℂ}
    (hT : IsOpen T) :
    IsOpen {y : ComplexPoints sX | ∃ hy : y ∈ ComplexPoints.chart U,
      ComplexPoints.evalHom U ⟨y, hy⟩ f ∈ T} := by
  rw [ComplexPoints.isOpen_iff]
  intro U'
  letI := ComplexPoints.chartTopology (sX := sX) (U' : X.Opens)
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨hyU, hyT⟩
  obtain ⟨g, hgU, hyg⟩ := U'.2.exists_basicOpen_le
    ⟨y.1.toScheme, ComplexPoints.mem_chart_iff.1 hyU⟩ (ComplexPoints.mem_chart_iff.1 y.2)
  have := U'.2.isLocalization_basicOpen g
  obtain ⟨⟨a, _, k, rfl⟩, hak⟩ := IsLocalization.mk'_surjective (Submonoid.powers g)
    (X.presheaf.map (homOfLE hgU).op f)
  have hval : ∀ z : ComplexPoints.chart (sX := sX) (U' : X.Opens),
      ComplexPoints.evalHom (U' : X.Opens) z g ≠ 0 →
        ∃ hzU : z.1 ∈ ComplexPoints.chart U, ComplexPoints.evalHom U ⟨z.1, hzU⟩ f =
          ComplexPoints.evalHom (U' : X.Opens) z a /
            ComplexPoints.evalHom (U' : X.Opens) z g ^ k := by
    intro z hz
    have hzD : z.1.toScheme ∈ X.basicOpen g := (ComplexPoints.toScheme_mem_basicOpen_iff z g).2 hz
    let zB : ComplexPoints.chart (sX := sX) (X.basicOpen g) :=
      ⟨z.1, ComplexPoints.mem_chart_iff.2 hzD⟩
    have hres : ∀ b : Γ(X, (U' : X.Opens)), ComplexPoints.evalHom (U' : X.Opens) z b =
        ComplexPoints.evalHom (X.basicOpen g) zB
          (algebraMap Γ(X, (U' : X.Opens)) Γ(X, X.basicOpen g) b) :=
      fun b => ComplexPoints.evalHom_res (X.basicOpen_le g) zB b
    refine ⟨ComplexPoints.mem_chart_iff.2 (hgU hzD), ?_⟩
    rw [ComplexPoints.evalHom_res hgU zB f, ← hak, eq_div_iff (pow_ne_zero _ hz), hres, hres,
      ← map_pow, ← map_mul, ← map_pow, IsLocalization.mk'_spec]
  refine ⟨{z | ComplexPoints.evalHom (U' : X.Opens) z g ≠ 0} ∩
      (fun z => ComplexPoints.evalHom (U' : X.Opens) z a /
        ComplexPoints.evalHom (U' : X.Opens) z g ^ k) ⁻¹' T, ?_, ?_, ?_⟩
  · rintro z ⟨hz, hzT⟩
    obtain ⟨hzU, hzv⟩ := hval z hz
    exact ⟨hzU, by rwa [hzv]⟩
  · refine ContinuousOn.isOpen_inter_preimage ?_
      (isOpen_compl_singleton.preimage (ComplexPoints.continuous_eval _ g)) hT
    exact (ComplexPoints.continuous_eval _ a).continuousOn.div
      ((ComplexPoints.continuous_eval _ g).pow k).continuousOn fun z hz => pow_ne_zero _ hz
  · have hy : ComplexPoints.evalHom (U' : X.Opens) y g ≠ 0 :=
      (ComplexPoints.toScheme_mem_basicOpen_iff y g).1 hyg
    obtain ⟨_, hyv⟩ := hval y hy
    exact ⟨hy, by rwa [Set.mem_preimage, ← hyv]⟩

/-- A subset of the `ℂ`-points of an affine open, open for its chart topology, is open in
`X(ℂ)`. -/
lemma isOpen_setOf_mem_chart (U : X.affineOpens)
    {O : Set (ComplexPoints.chart (sX := sX) (U : X.Opens))}
    (hO : IsOpen[ComplexPoints.chartTopology (U : X.Opens)] O) :
    IsOpen {y : ComplexPoints sX | ∃ hy : y ∈ ComplexPoints.chart (U : X.Opens), ⟨y, hy⟩ ∈ O} := by
  have hS : IsOpen (ComplexPoints.chart (sX := sX) (U : X.Opens)) := by
    have : ComplexPoints.chart (sX := sX) (U : X.Opens) =
        ComplexPoints.toScheme ⁻¹' ((U : X.Opens) : Set X) :=
      Set.ext fun _ => ComplexPoints.mem_chart_iff
    rw [this]
    exact (U : X.Opens).2.preimage ComplexPoints.continuous_toScheme
  have hid : @Continuous _ _ instTopologicalSpaceSubtype
      (ComplexPoints.chartTopology (U : X.Opens))
      (id : ComplexPoints.chart (sX := sX) (U : X.Opens) → _) := by
    refine continuous_iInf_rng.2 fun f => continuous_induced_rng.2 ?_
    refine continuous_def.2 fun T hT => ?_
    convert (isOpen_setOf_evalHom_mem (sX := sX) (U : X.Opens) f hT).preimage
      continuous_subtype_val using 1
    ext q
    exact ⟨fun h => ⟨q.2, h⟩, fun ⟨_, h⟩ => h⟩
  convert hS.isOpenMap_subtype_val _
    (@IsOpen.preimage _ _ instTopologicalSpaceSubtype (ComplexPoints.chartTopology _) _ hid _ hO)
    using 1
  ext y
  exact ⟨fun ⟨hy, h⟩ => ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨q, hq, e⟩ => e ▸ ⟨q.2, hq⟩⟩

/-- A neighbourhood, in the chart topology, of a point of a chart, on which the coordinates lie
in a prescribed neighbourhood, contains an open of `X(ℂ)` around the point. -/
lemma exists_opens_of_mem_chart (c : Chart sX)
    {O : Set (ComplexPoints.chart (sX := sX) c.U)}
    (hO : IsOpen[ComplexPoints.chartTopology c.U] O) (y : ComplexPoints.chart (sX := sX) c.U)
    (hy : y ∈ O) {N : Set (Fin c.n → ℂ)} (hN : N ∈ 𝓝 (c.coords y)) :
    ∃ V : Opens (space sX), y.1 ∈ V ∧ ∀ z ∈ V, ∃ hz : z ∈ ComplexPoints.chart c.U,
      ⟨z, hz⟩ ∈ O ∧ c.coords ⟨z, hz⟩ ∈ N := by
  letI := ComplexPoints.chartTopology (sX := sX) c.U
  obtain ⟨B, hBN, hB, hyB⟩ := mem_nhds_iff.1 hN
  have hcont : Continuous c.coords :=
    continuous_pi fun i => ComplexPoints.continuous_eval c.U (c.gen i)
  have hO' : IsOpen (O ∩ c.coords ⁻¹' B) := hO.inter (hB.preimage hcont)
  refine ⟨⟨_, isOpen_setOf_mem_chart ⟨c.U, c.isAffineOpen⟩ hO'⟩, ⟨y.2, hy, hyB⟩, ?_⟩
  rintro z ⟨hz, hzO, hzB⟩
  exact ⟨hz, hzO, hBN hzB⟩

/-- The residue of a section of `𝒪_{X^an}` is continuous: near a point `x`, its residues in
every chart lie in any prescribed neighbourhood of its residue at `x`. -/
lemma exists_opens_residue_mem [LocallyOfFiniteType sX] {W : Opens (space sX)}
    (s : sections sX W) (x : W) (c : Chart sX) (hc : x.1 ∈ ComplexPoints.chart c.U) {N : Set ℂ}
    (hN : N ∈ 𝓝 (residue c ⟨x.1, hc⟩ (s.1 x ⟨c, hc⟩))) :
    ∃ V : Opens (space sX), x.1 ∈ V ∧ ∀ y : W, y.1 ∈ V → ∀ (d : Chart sX)
      (hd : y.1 ∈ ComplexPoints.chart d.U), residue d ⟨y.1, hd⟩ (s.1 y ⟨d, hd⟩) ∈ N := by
  obtain ⟨O, hO, hxO, h, hh⟩ := s.2.1 c x hc
  have hres : ∀ y ∈ O, ∀ hyW : y.1 ∈ W,
      residue c y (s.1 ⟨y.1, hyW⟩ ⟨c, y.2⟩) = h (c.coords y) := fun y hy _ => by
    obtain ⟨_, g, hg, hsg⟩ := hh y hy
    exact residue_of_eq_mk c y hsg hg
  obtain ⟨_, g₀, hg₀, -⟩ := hh _ hxO
  rw [hres _ hxO x.2] at hN
  obtain ⟨V, hxV, hV⟩ := exists_opens_of_mem_chart c hO _ hxO
    ((eventually_differentiableAt_of_coe_eq g₀ hg₀).self_of_nhds.continuousAt.preimage_mem_nhds hN)
  refine ⟨V, hxV, fun y hyV d hd => ?_⟩
  obtain ⟨hyc, hyO, hyN⟩ := hV y.1 hyV
  rw [residue_eq_of_isCompatible s.2.2 y d c hd hyc, hres _ hyO]
  exact hyN

variable (sX) [LocallyOfFiniteType sX]

/-- A chart containing a given `ℂ`-point. -/
noncomputable def pointChart (x : space sX) : {c : Chart sX // x ∈ ComplexPoints.chart c.U} :=
  ⟨(exists_chart x).choose, (exists_chart x).choose_spec⟩

/-- The value at a point of a section of `𝒪_{X^an}`: the residue of its component in
`pointChart`. -/
noncomputable def sectionValue {W : Opens (space sX)} (s : (structureSheaf sX).obj.obj (op W))
    (x : W) : ℂ :=
  residue (pointChart sX x.1).1 ⟨x.1, (pointChart sX x.1).2⟩ (s.1 x (pointChart sX x.1))

/-- The value of a section whose component in `pointChart` is the class of the holomorphic germ `g`
is the value of `g`. -/
lemma sectionValue_eq {W : Opens (space sX)} (s : (structureSheaf sX).obj.obj (op W))
    (x : W) (g : holGerms ((pointChart sX x.1).1.coords ⟨x.1, (pointChart sX x.1).2⟩))
    (hs : s.1 x (pointChart sX x.1) = Chart.StalkRing.mk _ _ g) :
    sectionValue sX s x =
      Germ.value (g : Germ (𝓝 ((pointChart sX x.1).1.coords ⟨x.1, (pointChart sX x.1).2⟩)) ℂ) := by
  rw [sectionValue, hs, residue_mk]

/-- Values of sections of `𝒪_{X^an}` are continuous functions. -/
lemma continuous_sectionValue {W : Opens (space sX)}
    (s : (structureSheaf sX).obj.obj (op W)) : Continuous (sectionValue sX s) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Filter.tendsto_def]
  intro N hN
  obtain ⟨V, hxV, hV⟩ := exists_opens_residue_mem s x (pointChart sX x.1).1 (pointChart sX x.1).2
    (N := N) (by rwa [← sectionValue])
  refine Filter.mem_of_superset ((V.isOpen.preimage continuous_subtype_val).mem_nhds hxV) ?_
  intro y hy
  exact hV y hy _ _

end Residue

section ValueMap

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]

/-- Evaluation `𝒪_{X^an} ⟶ ℂ^{X(ℂ)}` of sections at points. -/
noncomputable def valueMap :
    (sheafCompose (Opens.grothendieckTopology (space sX)) (forget₂ RingCat AddCommGrpCat)).obj
      (ringCatSheaf sX) ⟶ funSheaf (space sX) ℂ where
  hom :=
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun s x => sectionValue sX (show (structureSheaf sX).obj.obj W from s) x
          map_zero' := by funext x; simp [sectionValue]; rfl
          map_add' := fun s t => by funext x; simp only [sectionValue]; exact map_add _ _ _ }
      naturality := fun W W' i => rfl }

/-- The value of the integer section `n` is `n` at every point. -/
lemma sectionValue_intCast {W : Opens (space sX)} (n : ℤ) (x : W) :
    sectionValue sX ((n : ℤ) : (structureSheaf sX).obj.obj (op W)) x = n := by
  simp only [sectionValue]
  have : (n : (structureSheaf sX).obj.obj (op W)).1 x (pointChart sX x.1) =
      (n : (pointChart sX x.1).1.StalkRing _) := rfl
  rw [this, map_intCast]

/-- The exponential sequence's first map followed by evaluation is the inclusion of the constant
integer functions. -/
lemma comp_valueMap_eq_constFun
    (ι : ZSh (space sX) ⟶ (sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX))
    (hι : ∀ (W : Opens (space sX)) (n : ℤ),
      (show (structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
        ((toSheafify (Opens.grothendieckTopology (space sX))
          ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) :
    ι ≫ valueMap sX = constFun (space sX) := by
  apply ((constantSheafAdj (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}
    isTerminalTop).homEquiv _ _).injective
  rw [constFun, Equiv.apply_symm_apply]
  erw [Adjunction.homEquiv_unit]
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun n => funext fun x => ?_)
  change sectionValue sX (show (structureSheaf sX).obj.obj (op ⊤) from ι.hom.app (op ⊤)
    ((toSheafify (Opens.grothendieckTopology (space sX))
      ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op ⊤) n)) x = (n : ℂ)
  rw [hι, sectionValue_intCast]

end ValueMap

section LocalLog

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
  [∀ x, IsLocalRing ((analytification sX).presheaf.stalk x)]

/-- The ring element underlying a section of `𝒪^×`. -/
abbrev unitVal {W : Opens (space sX)}
    (u : (Stacks.Cohomology.Generators.unitsSheaf (analytification sX)).obj.obj (op W)) :
    (structureSheaf sX).obj.obj (op W) :=
  ((Additive.toMul u : ((structureSheaf sX).obj.obj (op W))ˣ) : (structureSheaf sX).obj.obj (op W))

/-- The value of `exp (2πi f)` is `exp (2πi)` of the value of `f`. -/
lemma sectionValue_exp
    (e : (sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX) ⟶
        Stacks.Cohomology.Generators.unitsSheaf (analytification sX))
    (he : ∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
      (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
      (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
      (g' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
        (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
      s.1 x c = Chart.StalkRing.mk c.1 _ g →
      ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
        (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ g')
    {W : Opens (space sX)} (t : (structureSheaf sX).obj.obj (op W)) (x : W) :
    sectionValue sX (unitVal sX (e.hom.app (op W) t)) x =
      Complex.exp (2 * Real.pi * Complex.I * sectionValue sX t x) := by
  obtain ⟨g, hg⟩ := mk_surjective (pointChart sX x.1).1 _ (t.1 x (pointChart sX x.1))
  obtain ⟨F, hF, hd⟩ := exists_rep g
  let g' : holGerms ((pointChart sX x.1).1.coords ⟨x.1, (pointChart sX x.1).2⟩) :=
    ⟨((fun z => Complex.exp (2 * Real.pi * Complex.I * F z) : (Fin _ → ℂ) → ℂ) : Germ _ ℂ),
      fun z => Complex.exp (2 * Real.pi * Complex.I * F z), rfl,
      hd.mono fun z hz => ((differentiableAt_const _).mul hz).cexp⟩
  have h1 := he W t x (pointChart sX x.1) F g g' hF rfl hg.symm
  rw [sectionValue_eq sX _ x g' h1, sectionValue_eq sX t x g hg.symm, hF]
  rfl

/-- **Local logarithms of `λ`.** Near every point, the image under `λ` of a section of `𝒪^×` is the
class of a continuous function `φ` with `exp (2πi φ)` the value of the section. -/
lemma exists_local_log_lam
    (e : (sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX) ⟶
        Stacks.Cohomology.Generators.unitsSheaf (analytification sX)) [Epi e]
    (he : ∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
      (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
      (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
      (g' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
        (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
      s.1 x c = Chart.StalkRing.mk c.1 _ g →
      ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
        (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ g')
    (lam : Stacks.Cohomology.Generators.unitsSheaf (analytification sX) ⟶ quotSheaf (space sX))
    (hlam : e ≫ lam = valueMap sX ≫ cokernel.π (constFun (space sX)))
    {W : Opens (space sX)}
    (u : (Stacks.Cohomology.Generators.unitsSheaf (analytification sX)).obj.obj (op W))
    {y : space sX} (hy : y ∈ W) :
    ∃ (V : Opens (space sX)) (hVW : V ≤ W), y ∈ V ∧ ∃ φ : space sX → ℂ, ContinuousOn φ V ∧
      (∀ z (hz : z ∈ V), Complex.exp (2 * Real.pi * Complex.I * φ z) =
        sectionValue sX (unitVal sX u) ⟨z, hVW hz⟩) ∧
      (quotSheaf (space sX)).obj.map (homOfLE hVW).op (lam.hom.app (op W) u) =
        (cokernel.π (constFun (space sX))).hom.app (op V) (show V → ℂ from fun z => φ z) := by
  classical
  haveI : Sheaf.IsLocallySurjective e := (Sheaf.isLocallySurjective_iff_epi' (φ := e)).2 inferInstance
  have hsieve := Presheaf.imageSieve_mem (Opens.grothendieckTopology (space sX)) e.hom (U := op W) u
  obtain ⟨V, i, ⟨t, ht⟩, hyV⟩ := hsieve y hy
  let φ : space sX → ℂ := fun z => if hz : z ∈ V then sectionValue sX t ⟨z, hz⟩ else 0
  have hφV : ∀ z : V, φ z = sectionValue sX t z := fun z => by simp [φ, z.2]
  refine ⟨V, leOfHom i, hyV, φ, ?_, fun z hz => ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    exact (continuous_sectionValue sX t).congr fun z => (hφV z).symm
  · rw [hφV ⟨z, hz⟩, ← sectionValue_exp sX e he t ⟨z, hz⟩]
    change sectionValue sX (unitVal sX (e.hom.app (op V) t)) ⟨z, hz⟩ = _
    rw [ht]
    rfl
  · have hn := ConcreteCategory.congr_hom (lam.hom.naturality i.op) u
    change (quotSheaf (space sX)).obj.map i.op (lam.hom.app (op W) u) = _
    rw [← ConcreteCategory.comp_apply, ← hn, ConcreteCategory.comp_apply, ← ht,
      ← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
    change (e ≫ lam).hom.app (op V) t = _
    rw [hlam]
    change (cokernel.π (constFun (space sX))).hom.app (op V) ((valueMap sX).hom.app (op V) t) = _
    congr 1
    funext z
    exact (hφV z).symm

end LocalLog

section UnitsLog

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
  [∀ x, IsLocalRing ((analytification sX).presheaf.stalk x)]

/-- **The exponential sequence maps to `0 ⟶ ℤ ⟶ ℂ^M ⟶ ℂ^M/ℤ ⟶ 0`.** Evaluation of sections
induces a map `λ : 𝒪^× ⟶ ℂ^M/ℤ` on the quotients, and the extension class of the exponential
sequence is that of the quotient sequence pulled back along `λ`. -/
theorem exists_unitsLog
    (ι : ZSh (space sX) ⟶ (sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX))
    (e : (sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX) ⟶
        Stacks.Cohomology.Generators.unitsSheaf (analytification sX))
    (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact)
    (hι : ∀ (W : Opens (space sX)) (n : ℤ),
      (show (structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
        ((toSheafify (Opens.grothendieckTopology (space sX))
          ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) :
    ∃ lam : Stacks.Cohomology.Generators.unitsSheaf (analytification sX) ⟶ quotSheaf (space sX),
      e ≫ lam = valueMap sX ≫ cokernel.π (constFun (space sX)) ∧
        hS.extClass = (Ext.mk₀ lam).comp (quotSeq_shortExact (space sX)).extClass (zero_add 1) := by
  have hcomp := comp_valueMap_eq_constFun sX ι hι
  have w' : ι ≫ valueMap sX ≫ cokernel.π (constFun (space sX)) = 0 := by
    rw [← Category.assoc, hcomp, cokernel.condition]
  let lam := hS.gIsCokernel.desc (CokernelCofork.ofπ _ w')
  have hlam : e ≫ lam = valueMap sX ≫ cokernel.π (constFun (space sX)) :=
    hS.gIsCokernel.fac (CokernelCofork.ofπ _ w') WalkingParallelPair.one
  refine ⟨lam, hlam, ?_⟩
  let f : ShortComplex.mk ι e w ⟶
      ShortComplex.mk (constFun (space sX)) (cokernel.π (constFun (space sX)))
        (cokernel.condition _) :=
    { τ₁ := 𝟙 _
      τ₂ := valueMap sX
      τ₃ := lam
      comm₁₂ := by simpa using hcomp.symm
      comm₂₃ := hlam.symm }
  have h := hS.extClass_naturality (quotSeq_shortExact (space sX)) f
  rw [show f.τ₁ = 𝟙 _ from rfl, Ext.comp_mk₀_id] at h
  exact h

end UnitsLog

section Frames

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
  [∀ x, IsLocalRing ((analytification sX).presheaf.stalk x)]

/-- Near every point an invertible module has a local generator whose value is nonzero there. -/
lemma exists_generator_ne_zero (L : SheafOfModules (ringCatSheaf sX))
    (hL : Stacks.SheafOfModules.IsInvertible (analytification sX).sheaf.obj
      (ringCatSheaf sX).property L)
    (E : space sX → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    (val : ∀ V : Opens (space sX), L.val.obj (op V) → ∀ x : V, E x)
    (h3 : ∀ (V W : Opens (space sX)) (h : W ≤ V) (t : L.val.obj (op V)) (x : W),
      val W (L.val.map (homOfLE h).op t) x = val V t ⟨x.1, h x.2⟩)
    (h4 : ∀ (V : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op V))
      (t : L.val.obj (op V)) (x : V)
      (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U})
      (g : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      s.1 x c = Chart.StalkRing.mk c.1 _ g →
      val V ((show (ringCatSheaf sX).obj.obj (op V) from s) • t) x =
        Germ.value (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) • val V t x)
    (h5 : ∀ x : space sX, ∃ (V : Opens (space sX)) (t : L.val.obj (op V)) (hx : x ∈ V),
      val V t ⟨x, hx⟩ ≠ 0) (x : space sX) :
    ∃ (U : Opens (space sX)) (hx : x ∈ U)
      (s : (Stacks.Cohomology.Generators.generatorTorsorOfInvertible (analytification sX)
        L hL).F.obj U),
      val U ((Stacks.Cohomology.Generators.generatorTorsorOfInvertible (analytification sX)
        L hL).sectionsEquiv U s).val ⟨x, hx⟩ ≠ 0 := by
  set T := Stacks.Cohomology.Generators.generatorTorsorOfInvertible (analytification sX) L hL
  obtain ⟨U₀, hxU₀, ⟨s₀⟩⟩ := T.isTorsor.2 x
  obtain ⟨V, t, hxV, ht⟩ := h5 x
  refine ⟨U₀, hxU₀, s₀, fun h0 => ht ?_⟩
  let W : Opens (space sX) := U₀ ⊓ V
  have hxW : x ∈ W := ⟨hxU₀, hxV⟩
  obtain ⟨r, hr⟩ := ((T.sectionsEquiv U₀ s₀).2 W inf_le_left).2
    (L.val.map (homOfLE (inf_le_right : W ≤ V)).op t)
  have e1 := h3 V W inf_le_right t ⟨x, hxW⟩
  rw [← hr] at e1
  obtain ⟨g, hg⟩ := mk_surjective (pointChart sX x).1 _ (r.1 ⟨x, hxW⟩ (pointChart sX x))
  have e2 := h4 W r (L.val.restrictₛₗ (homOfLE (inf_le_left : W ≤ U₀)).op
    (T.sectionsEquiv U₀ s₀).val) ⟨x, hxW⟩ (pointChart sX x) g hg.symm
  have e3 := h3 U₀ W inf_le_left (T.sectionsEquiv U₀ s₀).val ⟨x, hxW⟩
  change val W (L.val.map (homOfLE (inf_le_left : W ≤ U₀)).op (T.sectionsEquiv U₀ s₀).val)
    ⟨x, hxW⟩ = _ at e3
  rw [← e1]
  refine e2.trans ?_
  have e4 : val W (L.val.restrictₛₗ (homOfLE (inf_le_left : W ≤ U₀)).op
      (T.sectionsEquiv U₀ s₀).val) ⟨x, hxW⟩ = 0 := e3.trans h0
  rw [e4, smul_zero]

/-- **Frames related by a unit.** If `u • s = t` in the torsor of generators, then the values of
the generators satisfy `val t = (value of u) • val s` pointwise. -/
lemma val_act_eq (L : SheafOfModules (ringCatSheaf sX))
    (hL : Stacks.SheafOfModules.IsInvertible (analytification sX).sheaf.obj
      (ringCatSheaf sX).property L)
    (E : space sX → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    (val : ∀ V : Opens (space sX), L.val.obj (op V) → ∀ x : V, E x)
    (h4 : ∀ (V : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op V))
      (t : L.val.obj (op V)) (x : V)
      (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U})
      (g : holGerms (c.1.coords ⟨x.1, c.2⟩)),
      s.1 x c = Chart.StalkRing.mk c.1 _ g →
      val V ((show (ringCatSheaf sX).obj.obj (op V) from s) • t) x =
        Germ.value (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) • val V t x)
    {W : Opens (space sX)}
    (s t : (Stacks.Cohomology.Generators.generatorTorsorOfInvertible (analytification sX)
      L hL).F.obj W)
    (u : (Stacks.Cohomology.Generators.unitsSheaf (analytification sX)).presheaf.obj (op W))
    (hst : (Stacks.Cohomology.Generators.generatorTorsorOfInvertible (analytification sX)
      L hL).action.act (Multiplicative.ofAdd (α := ToType
      ((Stacks.Cohomology.Generators.unitsSheaf (analytification sX)).presheaf.obj (op W))) u)
      s = t) (z : W) :
    val W ((Stacks.Cohomology.Generators.generatorTorsorOfInvertible (analytification sX)
        L hL).sectionsEquiv W t).val z =
      sectionValue sX ((Additive.toMul u : ((structureSheaf sX).obj.obj (op W))ˣ) :
        (structureSheaf sX).obj.obj (op W)) z •
      val W ((Stacks.Cohomology.Generators.generatorTorsorOfInvertible (analytification sX)
        L hL).sectionsEquiv W s).val z := by
  subst hst
  have hsm := (Stacks.Cohomology.Generators.generatorTorsorOfInvertible (analytification sX)
    L hL).sectionsEquiv_smul W (Additive.toMul u) s
  refine (congrArg (fun v => val W v z) hsm).trans ?_
  obtain ⟨g, hg⟩ := mk_surjective (pointChart sX z.1).1 _
    (((Additive.toMul u : ((structureSheaf sX).obj.obj (op W))ˣ) :
      (structureSheaf sX).obj.obj (op W)).1 z (pointChart sX z.1))
  exact (h4 W _ _ z (pointChart sX z.1) g hg.symm).trans
    (by rw [sectionValue_eq sX _ z g hg.symm])

end Frames

section PicardSide

/-- The obstruction map on the class of an invertible module: the first cohomology class of its
torsor of local generators, composed with the extension class of the sequence. -/
theorem picardObstruction_classOf (A : RingedSpace.{0})
    [∀ x, IsLocalRing (A.presheaf.stalk x)]
    {F M : Sheaf (Opens.grothendieckTopology A.carrier) AddCommGrpCat.{0}}
    {i : F ⟶ M} {e : M ⟶ Stacks.Cohomology.Generators.unitsSheaf A}
    {w : i ≫ e = 0} (hS : (ShortComplex.mk i e w).ShortExact)
    (L : SheafOfModules (structureSheaf A.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible A.sheaf.obj (structureSheaf A.sheaf).property L) :
    picardObstruction A hS (Stacks.SheafOfModules.Picard.classOf A.sheaf.obj _ L hL) =
      ((Stacks.Thickenings.sheafCohomologyOneExtEquiv A.carrier
          (Stacks.Cohomology.Generators.unitsSheaf A)).hom
        (Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne A.carrier
          (Stacks.Cohomology.Generators.unitsSheaf A)
          ⟦(Stacks.Cohomology.Generators.generatorTorsorOfInvertible A L hL).toTorsor⟧)).comp
        hS.extClass (show 1 + 1 = 2 from rfl) := by
  refine (MMP.Analytic.picardObstruction_apply A hS _).trans ?_
  rw [Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup_symm_classOf]
  rfl

/-- The pushforward along `lam` of the class of a torsor, computed on a cover trivializing it:
minus the class of any cocycle `c` cohomologous to minus the image of the transition cocycle. -/
theorem rightDerived_map_torsorClass_eq_neg {X : TopCat.{0}}
    {H G : TopCat.Sheaf AddCommGrpCat.{0} X} (T : Stacks.Cohomology.SheafTorsor.Torsor X H)
    (lam : H ⟶ G) {I : Type} (Ui : I → Opens X) (hUi : (⊤ : Opens X) = ⨆ i, Ui i)
    (s : ∀ i, T.F.obj (Ui i)) (g : CechCochains.cocycles1 Ui H.presheaf)
    (hg : Stacks.Cohomology.SheafTorsor.IsTransitionCocycle T Ui s g)
    (h : CechCochains.Cochain Ui G.presheaf 0) (c : CechCochains.cocycles1 Ui G.presheaf)
    (hc : ∀ i, c.1 i = CechCochains.cechD Ui G.presheaf 0 h i -
      lam.hom.app (op (CechCochains.inter Ui i)) (g.1 i)) :
    (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        (op ⊤)).rightDerived 1).map lam
      (Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne X H ⟦T⟧) =
      -Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi G
        (CechCochains.cls Ui G.presheaf c) := by
  let c' : CechCochains.cocycles1 Ui G.presheaf :=
    ⟨CechCochains.cechD Ui G.presheaf 0 h - c.1, by
      rw [CechCochains.mem_cocycles1_iff, map_sub, CechCochains.cechD_cechD,
        (CechCochains.mem_cocycles1_iff _ _ _).1 c.2, sub_zero]⟩
  have hc' : ∀ i : Fin 2 → I, c'.1 i = lam.hom.app (op (CechCochains.inter Ui i)) (g.1 i) := by
    intro i
    change CechCochains.cechD Ui G.presheaf 0 h i - c.1 i = _
    rw [hc i]
    abel
  rw [Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne_of_cocycle X H T Ui hUi s g hg,
    Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections_naturality X ⊤ Ui hUi lam g c' hc',
    ← map_neg]
  congr 1
  rw [CechCochains.cls, CechCochains.cls, ← QuotientAddGroup.mk_neg, QuotientAddGroup.eq]
  refine ⟨-h, ?_⟩
  funext i
  change CechCochains.cechD Ui G.presheaf 0 (-h) i =
    -(CechCochains.cechD Ui G.presheaf 0 h i - c.1 i) + -c.1 i
  rw [map_neg]
  change -(CechCochains.cechD Ui G.presheaf 0 h i) = _
  abel

end PicardSide

open MMP.SingularChain MMP.SingularCochain

/-- `c` is, Čech-locally, the class in `quotSheaf` of an integer primitive of `w j - w i`. -/
def IsKappaCocycle {M : TopCat.{0}} {I : Type} (Ui : I → Opens M) (w : I → Simplex M 1 → ℤ)
    (c : CechCochains.cocycles1 Ui (quotSheaf M).obj) : Prop :=
  ∀ (i : Fin 2 → I) (y : M), y ∈ CechCochains.inter Ui i →
    ∃ (V : Opens M) (hV : V ≤ CechCochains.inter Ui i), y ∈ V ∧ ∃ a : V → ℤ,
      (∀ (τ : Simplex M 1) (hτ : Set.range τ ⊆ V),
        w (i 1) τ - w (i 0) τ = a ⟨_, hτ ⟨stdSimplex.vertex 1, rfl⟩⟩ -
          a ⟨_, hτ ⟨stdSimplex.vertex 0, rfl⟩⟩) ∧
      (quotSheaf M).obj.map (homOfLE hV).op (c.1 i) =
        (cokernel.π (constFun M)).hom.app (op V) (show V → ℂ from fun y => (a y : ℂ))

/-- The class in `H²(M, ℤ)` of a Čech `1`-cocycle of `quotSheaf M`: its first cohomology class
followed by the connecting map of `0 ⟶ ℤ ⟶ ℂ^M ⟶ quotSheaf M ⟶ 0`. -/
noncomputable def quotExtClass (M : TopCat.{0}) {I : Type} (Ui : I → Opens M)
    (hUi : (⊤ : Opens M) = ⨆ i, Ui i) (c : CechCochains.cocycles1 Ui (quotSheaf M).obj) :
    Sheaf.H.{0} (ZSh M) 2 :=
  ((Stacks.Thickenings.sheafCohomologyOneExtEquiv M (quotSheaf M)).hom
    (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections M ⊤ Ui hUi (quotSheaf M)
      (CechCochains.cls Ui (quotSheaf M).obj c))).comp
    (quotSeq_shortExact M).extClass (show 1 + 1 = 2 from rfl)

section TopologicalComparison

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology Metric

noncomputable section

/-- The integral singular chain complex `C_•(X; ℤ)`. -/
abbrev singChains (X : TopCat.{u}) : ChainComplex AddCommGrpCat.{u} ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).obj X

section CochainBridge

open scoped Simplicial

/-- The value of an `A`-valued cochain on a singular simplex. -/
def cochainEval (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ)
    (φ : (singChains X).X n ⟶ A) (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) : A :=
  (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ φ).hom ⟨1⟩

/-- The `A`-valued cochain taking the value `g σ` on each singular simplex `σ`. -/
def cochainOfFun (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ)
    (g : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → A) : (singChains X).X n ⟶ A :=
  Sigma.desc fun σ ↦ AddCommGrpCat.ofHom
    { toFun := fun k ↦ k.down • g σ
      map_zero' := by simp
      map_add' := fun a b ↦ by simp [add_smul] }

/-- `A`-valued singular `n`-cochains are the functions from singular `n`-simplices to `A`. -/
def cochainEquiv (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ) :
    ((singChains X).X n ⟶ A) ≃ ((TopCat.toSSet.obj X).obj (op ⦋n⦌) → A) where
  toFun φ := cochainEval A X n φ
  invFun g := cochainOfFun A X n g
  left_inv φ := by
    refine Sigma.hom_ext _ _ fun σ ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun k ↦ ?_)
    change (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ cochainOfFun A X n (cochainEval A X n
        φ)).hom k = _
    rw [cochainOfFun, Sigma.ι_desc]
    change k.down • cochainEval A X n φ σ = (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ φ).hom
        k
    have : k = k.down • (⟨1⟩ : ULift ℤ) := by ext; simp
    conv_rhs => rw [this]
    rw [map_zsmul]
    rfl
  right_inv g := by
    funext σ
    change (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ cochainOfFun A X n g).hom ⟨1⟩ = g σ
    simp [cochainOfFun]

/-- Evaluating a finite sum of morphisms of abelian groups is the sum of the evaluations. -/
lemma hom_sum' {M N : AddCommGrpCat.{u}} {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (x :
    M) :
    (∑ i ∈ s, f i).hom x = ∑ i ∈ s, (f i).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add]; simp
      [ih]

/-- The differential of the singular chain complex on the generator of a simplex `σ` is the
alternating sum of the generators of its faces. -/
@[reassoc]
lemma ι_singChains_d (X : TopCat.{u}) (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
    Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ (singChains X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) ((TopCat.toSSet.obj X).δ i σ) := by
  have : (singChains X).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      SimplicialObject.δ (TopCat.toSSet.obj X ⋙ sigmaConst.obj (AddCommGrpCat.of (ULift.{u} ℤ))) i :=
    AlternatingFaceMapComplex.obj_d_eq _ n
  rw [this]
  erw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [Preadditive.comp_zsmul]
  congr 1
  simp only [SimplicialObject.δ, sigmaConst]
  erw [Sigma.ι_comp_map', Category.id_comp]

/-- The coboundary of a cochain takes on a simplex `σ` the alternating sum of the values of the
cochain on the faces of `σ`. -/
lemma cochainEval_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ)
    (φ : (singChains X).X n ⟶ A) (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
    cochainEval A X (n + 1) ((singChains X).d (n + 1) n ≫ φ) σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • cochainEval A X n φ ((TopCat.toSSet.obj X).δ i σ) :=
          by
  unfold cochainEval
  change (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ (singChains X).d (n + 1) n ≫ φ).hom ⟨1⟩ =
      _
  erw [ι_singChains_d_assoc, Preadditive.sum_comp]
  rw [hom_sum']
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [Preadditive.zsmul_comp]
  simp
  rfl

/-- The pullback of a cochain along `f` takes on a simplex `σ` the value of the cochain on `f ∘
σ`. -/
lemma cochainEval_map (A : AddCommGrpCat.{u}) {X Y : TopCat.{u}} (f : Y ⟶ X) (n : ℕ)
    (φ : (singChains X).X n ⟶ A) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    cochainEval A Y n ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of
        (ULift ℤ))).map f).f n ≫ φ) σ =
      cochainEval A X n φ ((TopCat.toSSet.map f).app _ σ) := by
  unfold cochainEval
  change (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫
    (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map f).f n ≫
        φ).hom ⟨1⟩ = _
  have : Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫
        (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map f).f
            n =
      Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) ((TopCat.toSSet.map f).app _ σ) := by
    dsimp [singularChainComplexFunctor, SSet.chainComplexFunctor]
    simp [Sigma.ι_comp_map']
  erw [← Category.assoc, this]
  rfl

end CochainBridge

section CochainBridge2

open scoped Simplicial

/-- The one-point space. -/
abbrev pt : TopCat.{u} := TopCat.of PUnit.{u + 1}

/-- The one-point space has exactly one singular `n`-simplex. -/
instance (n : ℕ) : Unique ((TopCat.toSSet.obj pt).obj (op ⦋n⦌)) :=
  haveI : Unique C(Convexity.StdSimplex ℝ (Fin ((op ⦋n⦌).unop.len + 1)), (pt : Type u)) :=
    ⟨⟨⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext x⟩
  (TopCat.toSSetObjEquiv pt (op ⦋n⦌)).unique

/-- On the one-point space the coboundary of an `m`-cochain takes on the unique simplex `0` for `m`
even and the value of the cochain for `m` odd. -/
lemma pt_eval_d (A : AddCommGrpCat.{u}) (m : ℕ) (φ : (singChains pt).X m ⟶ A) :
    cochainEval A pt (m + 1) ((singChains pt).d (m + 1) m ≫ φ) default =
      (if m % 2 = 0 then (0 : ℤ) else 1) • cochainEval A pt m φ default := by
  rw [cochainEval_d, show (if m % 2 = 0 then (0 : ℤ) else 1) =
      ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) by
    rw [Fin.sum_neg_one_pow]; simp [Nat.even_add, Nat.even_iff], Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subsingleton.elim ((TopCat.toSSet.obj pt).δ i default) default]

/-- A cochain is determined by its values on singular simplices. -/
lemma cochainEval_injective (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ) :
    Function.Injective (cochainEval A X n) := (cochainEquiv A X n).injective

/-- The cohomology of a point vanishes in positive degrees. -/
lemma pt_coboundary (A : AddCommGrpCat.{u}) (n : ℕ) (z : (singChains pt).X (n + 1) ⟶ A)
    (hz : (singChains pt).d (n + 2) (n + 1) ≫ z = 0) :
    ∃ w : (singChains pt).X n ⟶ A, (singChains pt).d (n + 1) n ≫ w = z := by
  have h1 := pt_eval_d A (n + 1) z
  rw [hz] at h1
  have h0 : cochainEval A pt (n + 2) (0 : (singChains pt).X (n + 2) ⟶ A) default = 0 := by
    rfl
  rw [h0] at h1
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · -- n even: `z` itself vanishes
    refine ⟨0, ?_⟩
    have h2 : cochainEval A pt (n + 1) z default = 0 := by
      have : (n + 1) % 2 ≠ 0 := by omega
      rw [if_neg this] at h1
      simpa using h1.symm
    refine cochainEval_injective A pt (n + 1) ?_
    funext σ
    rw [Subsingleton.elim σ default]
    change cochainEval A pt (n + 1) _ default = cochainEval A pt (n + 1) z default
    rw [comp_zero, h2]
    rfl
  · refine ⟨cochainOfFun A pt n (fun _ => cochainEval A pt (n + 1) z default), ?_⟩
    refine cochainEval_injective A pt (n + 1) ?_
    funext σ
    rw [Subsingleton.elim σ default, pt_eval_d]
    have : (if n % 2 = 0 then (0 : ℤ) else 1) = 1 := by simp [show n % 2 ≠ 0 by omega]
    rw [this, one_smul]
    exact congrFun ((cochainEquiv A pt n).right_inv (fun _ => cochainEval A pt (n + 1) z default))
        default

/-- The pullback of a chain along a continuous map. -/
abbrev chainMap {Z Y : TopCat.{u}} (i : Z ⟶ Y) :=
  ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map i

/-- Along a nullhomotopic map, the pullback of a singular cocycle of positive degree is a
coboundary. -/
lemma nullhomotopic_coboundary (A : AddCommGrpCat.{u}) {Z Y : TopCat.{u}} (i : Z ⟶ Y)
    (hi : ContinuousMap.Nullhomotopic i.hom) (n : ℕ) (z : (singChains Y).X (n + 1) ⟶ A)
    (hz : (singChains Y).d (n + 2) (n + 1) ≫ z = 0) :
    ∃ b : (singChains Z).X n ⟶ A, (chainMap i).f (n + 1) ≫ z = (singChains Z).d (n + 1) n ≫ b := by
  obtain ⟨y0, ⟨H⟩⟩ := hi
  let q : Z ⟶ pt := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let j : pt ⟶ Y := TopCat.ofHom ⟨fun _ => y0, continuous_const⟩
  have hc : (TopCat.ofHom (ContinuousMap.const Z y0) : Z ⟶ Y) = q ≫ j := rfl
  let Hh := TopCat.Homotopy.singularChainComplexFunctorObjMap (C := AddCommGrpCat.{u})
    (f := i) (g := TopCat.ofHom (ContinuousMap.const Z y0)) H (AddCommGrpCat.of (ULift ℤ))
  have hcomm := Hh.comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hcomm
  have hw : (singChains pt).d (n + 2) (n + 1) ≫ (chainMap j).f (n + 1) ≫ z = 0 := by
    rw [← Category.assoc, ← (chainMap j).comm (n + 2) (n + 1), Category.assoc, hz, comp_zero]
  obtain ⟨w', hw'⟩ := pt_coboundary A n _ hw
  refine ⟨Hh.hom n (n + 1) ≫ z + (chainMap q).f n ≫ w', ?_⟩
  have hg : (chainMap (TopCat.ofHom (ContinuousMap.const Z y0) : Z ⟶ Y)).f (n + 1) =
      (chainMap q).f (n + 1) ≫ (chainMap j).f (n + 1) := by
    rw [hc]
    have hm : chainMap (q ≫ j) = chainMap q ≫ chainMap j := Functor.map_comp _ q j
    rw [hm, HomologicalComplex.comp_f]
  have e1 : (singChains Z).d (n + 1) n ≫ (chainMap q).f n ≫ w' =
      (chainMap q).f (n + 1) ≫ (chainMap j).f (n + 1) ≫ z := by
    rw [← Category.assoc, ← (chainMap q).comm (n + 1) n, Category.assoc, hw']
  rw [hcomm, hg]
  simp only [Preadditive.add_comp, Category.assoc, Preadditive.comp_add]
  erw [hz, comp_zero, add_zero, e1]

/-- Along a nullhomotopic map, the pullback of a singular `0`-cocycle is constant. -/
lemma nullhomotopic_const (A : AddCommGrpCat.{u}) {Z Y : TopCat.{u}} (i : Z ⟶ Y)
    (hi : ContinuousMap.Nullhomotopic i.hom) (z : (singChains Y).X 0 ⟶ A)
    (hz : (singChains Y).d 1 0 ≫ z = 0) :
    ∃ a : A, ∀ σ, cochainEval A Z 0 ((chainMap i).f 0 ≫ z) σ = a := by
  obtain ⟨y0, ⟨H⟩⟩ := hi
  let q : Z ⟶ pt := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let j : pt ⟶ Y := TopCat.ofHom ⟨fun _ => y0, continuous_const⟩
  have hc : (TopCat.ofHom (ContinuousMap.const Z y0) : Z ⟶ Y) = q ≫ j := rfl
  let Hh := TopCat.Homotopy.singularChainComplexFunctorObjMap (C := AddCommGrpCat.{u})
    (f := i) (g := TopCat.ofHom (ContinuousMap.const Z y0)) H (AddCommGrpCat.of (ULift ℤ))
  have hcomm := Hh.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at hcomm
  have hg : (chainMap (TopCat.ofHom (ContinuousMap.const Z y0) : Z ⟶ Y)).f 0 =
      (chainMap q).f 0 ≫ (chainMap j).f 0 := by
    rw [hc]
    have hm : chainMap (q ≫ j) = chainMap q ≫ chainMap j := Functor.map_comp _ q j
    rw [hm, HomologicalComplex.comp_f]
  refine ⟨cochainEval A pt 0 ((chainMap j).f 0 ≫ z) default, fun σ => ?_⟩
  have h1 : (chainMap i).f 0 ≫ z = (chainMap q).f 0 ≫ (chainMap j).f 0 ≫ z := by
    rw [hcomm, hg]
    simp only [Preadditive.add_comp, Category.assoc, Preadditive.comp_add, zero_add]
    erw [hz, comp_zero, zero_add]
  rw [h1, cochainEval_map]
  congr 1

end CochainBridge2

/-- The presheaf complex `U ↦ Hom(C_•(U; ℤ), A)` of singular cochains, as a functor from
`(Opens X)ᵒᵖ` to cochain complexes. -/
def singCochainPresheaf (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    (Opens X)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  (Opens.toTopCat X).op ⋙
    ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).op ⋙
      HomologicalComplex.opFunctor _ _ ⋙ (preadditiveYoneda.obj A).mapHomologicalComplex _

/-- In a locally contractible space, every neighbourhood of a point contains an open neighbourhood
whose inclusion is nullhomotopic. -/
lemma exists_open_nullhomotopic {X : TopCat.{u}} (hX : LocallyContractibleSpace X) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧
      ContinuousMap.Nullhomotopic ((Opens.toTopCat X).map (homOfLE h)).hom := by
  obtain ⟨V, hVU, hV, hnull⟩ := hX x (U : Set X) (U.isOpen.mem_nhds hx)
  refine ⟨⟨interior V, isOpen_interior⟩, (interior_subset.trans hVU), mem_interior_iff_mem_nhds.2
      hV, ?_⟩
  exact hnull.comp_left (ContinuousMap.inclusion (interior_subset : interior V ⊆ V))

/-- The `p`-th term of the presheaf complex of singular cochains, `U ↦ Hom(C_p(U; ℤ), A)`. -/
def singCochainTerm (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) :
    TopCat.Presheaf AddCommGrpCat.{u} X :=
  singCochainPresheaf A X ⋙ HomologicalComplex.eval _ _ p

/-- The differential `Hom(C_p(U; ℤ), A) ⟶ Hom(C_{p+1}(U; ℤ), A)` as a map of presheaves. -/
def singCochainTermD (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) :
    singCochainTerm A X p ⟶ singCochainTerm A X (p + 1) where
  app U := ((singCochainPresheaf A X).obj U).d p (p + 1)
  naturality _ _ i := ((singCochainPresheaf A X).map i).comm p (p + 1)

/-- The complex of presheaves of singular cochains. -/
def singCochainPresheafComplex (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℕ :=
  CochainComplex.of (singCochainTerm A X) (singCochainTermD A X) (fun p => by
    refine NatTrans.ext (funext fun U => ?_)
    exact ((singCochainPresheaf A X).obj U).d_comp_d p (p + 1) (p + 2))

/-- The complex of sheafified singular cochains `𝒮^•`. -/
def singCochainSheaves (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
    (singCochainPresheafComplex A X)

section SheafifyStalks

variable {X : TopCat.{u}}

/-- the sheafified complex -/
abbrev sheafifyComplex (P : CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex _).obj P

/-- the sheafification as a `TopCat.Sheaf` -/
abbrev sheafify (F : TopCat.Presheaf AddCommGrpCat.{u} X) : TopCat.Sheaf AddCommGrpCat.{u}
    X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj F

/-- stalk comparison -/
def stalkTau (x : X) (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    F.stalk x ⟶ (sheafify F).presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.app F)

/-- The comparison of the stalk of a presheaf with that of its sheafification is an isomorphism. -/
instance (x : X) (F : TopCat.Presheaf AddCommGrpCat.{u} X) : IsIso (stalkTau x F) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ F

/-- The comparison of the stalk of a presheaf with that of its sheafification is bijective. -/
lemma stalkTau_bijective (x : X) (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    Function.Bijective (stalkTau x F) :=
  (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- The comparison `stalkTau` is natural in the presheaf. -/
lemma stalkTau_naturality (x : X) {F G : TopCat.Presheaf AddCommGrpCat.{u} X} (η : F ⟶ G) :
    stalkTau x F ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map η).hom =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η ≫ stalkTau x G := by
  unfold stalkTau
  have hnat := (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).unit.naturality η
  exact (Functor.map_comp (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) _ _).symm.trans
    ((congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map hnat.symm).trans
      (Functor.map_comp (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) _ _))

/-- The sheafification of a complex of presheaves is exact in degree `n + 1` when every cocycle of
degree `n + 1` is, near each point, a coboundary. -/
lemma exactAt_sheafifyComplex (P : CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℕ)
    (n : ℕ)
    (h : ∀ (U : Opens X) (x : X) (hx : x ∈ U) (z : (P.X (n + 1)).obj (op U)),
      (P.d (n + 1) (n + 2)).app (op U) z = 0 →
        ∃ (V : Opens X) (hV : V ≤ U), x ∈ V ∧ ∃ b : (P.X n).obj (op V),
          (P.X (n + 1)).map (homOfLE hV).op z = (P.d n (n + 1)).app (op V) b) :
    (sheafifyComplex P).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro e he
  have hsurj := fun F => (stalkTau_bijective x F).2
  have hinj := fun F => (stalkTau_bijective x F).1
  obtain ⟨e', rfl⟩ := hsurj (P.X (n + 1)) e
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (P.X (n + 1)) e'
  have hg : ∀ w, (ConcreteCategory.hom ((HomologicalComplex.sc' (sheafifyComplex P) n (n + 1) (n +
      2)).map
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          x)).g)
        (stalkTau x (P.X (n + 1)) w) =
      stalkTau x (P.X (n + 2)) ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (P.d (n + 1)
          (n + 2)) w) :=
    fun w => ConcreteCategory.congr_hom (stalkTau_naturality x (P.d (n + 1) (n + 2))) w
  have hf : ∀ w, (ConcreteCategory.hom ((HomologicalComplex.sc' (sheafifyComplex P) n (n + 1) (n +
      2)).map
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          x)).f)
        (stalkTau x (P.X n) w) =
      stalkTau x (P.X (n + 1)) ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (P.d n (n +
          1)) w) :=
    fun w => ConcreteCategory.congr_hom (stalkTau_naturality x (P.d n (n + 1))) w
  rw [hg] at he
  have he1 : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (P.d (n + 1) (n + 2))
      ((P.X (n + 1)).germ U x hxU s) = 0 := hinj _ (he.trans (map_zero _).symm)
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at he1
  have he2 : (P.X (n + 2)).germ U x hxU ((P.d (n + 1) (n + 2)).app (op U) s) =
      (P.X (n + 2)).germ U x hxU 0 := he1.trans (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ he2
  have hd0 : (ConcreteCategory.hom ((P.d (n + 1) (n + 2)).app (op W)))
      ((ConcreteCategory.hom ((P.X (n + 1)).map iU.op)) s) = 0 := by
    have hn := ConcreteCategory.congr_hom ((P.d (n + 1) (n + 2)).naturality iU.op) s
    refine hn.trans (hW.trans (map_zero _))
  obtain ⟨V, hV, hxV, b, hb⟩ := h W x hxW _ hd0
  refine ⟨stalkTau x (P.X n) ((P.X n).germ V x hxV b), ?_⟩
  rw [hf, TopCat.Presheaf.stalkFunctor_map_germ_apply, ← hb]
  congr 1
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

end SheafifyStalks

/-- The sheafified singular cochain complex is exact in positive degrees when `X` is locally
contractible. -/
theorem singCochainSheaves_exactAt (A : AddCommGrpCat.{u}) (X : TopCat.{u})
    (hX : LocallyContractibleSpace X) (n : ℕ) : (singCochainSheaves A X).ExactAt (n + 1) :=
  exactAt_sheafifyComplex (singCochainPresheafComplex A X) n (fun U x hx z hz => by
    have hz' : ((singCochainPresheaf A X).obj (op U)).d (n + 1) (n + 2) z = 0 := by
      have e : (singCochainPresheafComplex A X).d (n + 1) (n + 2) = singCochainTermD A X (n + 1) :=
        CochainComplex.of_d _ _ _
      rw [e] at hz
      exact hz
    obtain ⟨V, h, hxV, hnull⟩ := exists_open_nullhomotopic hX x U hx
    obtain ⟨b, hb⟩ :=
      nullhomotopic_coboundary A ((Opens.toTopCat X).map (homOfLE h)) hnull n z hz'
    refine ⟨V, h, hxV, b, ?_⟩
    have e : (singCochainPresheafComplex A X).d n (n + 1) = singCochainTermD A X n :=
      CochainComplex.of_d _ _ _
    rw [e]
    exact hb)

section ConstantAugmentation

open scoped Simplicial

/-- The constant `0`-cochain with value `a`. -/
def constCochain (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (a : A) : (singChains Y).X 0 ⟶
    A :=
  cochainOfFun A Y 0 (fun _ => a)

/-- The constant `0`-cochain with value `a` takes the value `a` on every point. -/
lemma cochainEval_constCochain (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (a : A)
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋0⦌)) : cochainEval A Y 0 (constCochain A Y a) σ = a :=
  congrFun ((cochainEquiv A Y 0).right_inv (fun _ => a)) σ

/-- Evaluation of cochains on a simplex is additive. -/
lemma cochainEval_add (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (n : ℕ)
    (φ ψ : (singChains Y).X n ⟶ A) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    cochainEval A Y n (φ + ψ) σ = cochainEval A Y n φ σ + cochainEval A Y n ψ σ := by
  unfold cochainEval
  rfl

/-- The augmentation of the constant presheaf into the `0`-cochains: `a ↦ (σ ↦ a)`. -/
def constToCochain (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    (Functor.const (Opens X)ᵒᵖ).obj A ⟶ singCochainTerm A X 0 where
  app U := AddCommGrpCat.ofHom
    { toFun := fun a => constCochain A (Opens.toTopCat X |>.obj U.unop) a
      map_zero' := by
        refine cochainEval_injective A _ 0 (funext fun σ => ?_)
        rw [cochainEval_constCochain]; rfl
      map_add' := fun a b => by
        refine cochainEval_injective A _ 0 (funext fun σ => ?_)
        rw [cochainEval_constCochain]
        erw [cochainEval_add, cochainEval_constCochain, cochainEval_constCochain] }
  naturality U V i := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
    refine cochainEval_injective A _ 0 (funext fun σ => ?_)
    change cochainEval A _ 0 (constCochain A _ a) σ =
      cochainEval A _ 0 ((chainMap ((Opens.toTopCat X).map i.unop)).f 0 ≫ constCochain A _ a) σ
    rw [cochainEval_map, cochainEval_constCochain, cochainEval_constCochain]

/-- The constant `0`-cochains are cocycles. -/
lemma constToCochain_comp_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    constToCochain A X ≫ singCochainTermD A X 0 = 0 := by
  refine NatTrans.ext (funext fun U => ?_)
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
  refine cochainEval_injective A _ 1 (funext fun σ => ?_)
  change cochainEval A _ 1 ((singChains _).d 1 0 ≫ constCochain A _ a) σ = cochainEval A _ 1 0 σ
  rw [cochainEval_d]
  have h0 : cochainEval A _ 1 (0 : (singChains _).X 1 ⟶ A) σ = 0 := rfl
  rw [h0, Fin.sum_univ_two]
  simp only [cochainEval_constCochain]
  simp

/-- The constant sheaf. -/
abbrev constSheaf (A : AddCommGrpCat.{u}) (X : TopCat.{u}) : TopCat.Sheaf AddCommGrpCat.{u}
    X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A

/-- The augmentation `A_X ⟶ 𝒮^0`, as the sheafification of `constToCochain`. -/
def constAugDeg0 (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    constSheaf A X ⟶ (singCochainSheaves A X).X 0 :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (constToCochain A X)

/-- The augmentation `A_X ⟶ 𝒮^0` composed with the differential is zero. -/
lemma constAugDeg0_comp_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    constAugDeg0 A X ≫ (singCochainSheaves A X).d 0 1 = 0 := by
  have e : (singCochainSheaves A X).d 0 1 =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (singCochainTermD A X
          0) :=
    congrArg (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (show (singCochainPresheafComplex A X).d 0 1 = singCochainTermD A X 0 by
        simp [singCochainPresheafComplex]
        exact CochainComplex.of_d _ _ _)
  have h : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (constToCochain A X ≫ singCochainTermD A X 0) = 0 := by
    rw [constToCochain_comp_d]; exact Functor.map_zero _ _ _
  rw [e]
  exact (Functor.map_comp _ _ _).symm.trans h

end ConstantAugmentation

/-- The sheaf-level exactness at degree `0`, on stalks. -/
theorem exact_constAugDeg0 (A : AddCommGrpCat.{u}) (X : TopCat.{u})
    (hX : LocallyContractibleSpace X) :
    (ShortComplex.mk (constAugDeg0 A X) ((singCochainSheaves A X).d 0 1)
      (constAugDeg0_comp_d A X)).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro e he
  have hsurj := fun F => (stalkTau_bijective x F).2
  have hinj := fun F => (stalkTau_bijective x F).1
  obtain ⟨e', rfl⟩ := hsurj (singCochainTerm A X 0) e
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (singCochainTerm A X 0) e'
  have hg : ∀ w, (ConcreteCategory.hom ((ShortComplex.mk (constAugDeg0 A X) ((singCochainSheaves A
      X).d 0 1)
      (constAugDeg0_comp_d A X)).map
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          x)).g)
        (stalkTau x (singCochainTerm A X 0) w) =
      stalkTau x (singCochainTerm A X 1)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (singCochainTermD A X 0) w) :=
    fun w => ConcreteCategory.congr_hom (stalkTau_naturality x (singCochainTermD A X 0)) w
  have hf : ∀ w, (ConcreteCategory.hom ((ShortComplex.mk (constAugDeg0 A X) ((singCochainSheaves A
      X).d 0 1)
      (constAugDeg0_comp_d A X)).map
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          x)).f)
        (stalkTau x ((Functor.const (Opens X)ᵒᵖ).obj A) w) =
      stalkTau x (singCochainTerm A X 0)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (constToCochain A X) w) :=
    fun w => ConcreteCategory.congr_hom (stalkTau_naturality x (constToCochain A X)) w
  rw [hg] at he
  have he1 : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (singCochainTermD A X 0)
      ((singCochainTerm A X 0).germ U x hxU s) = 0 := hinj _ (he.trans (map_zero _).symm)
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at he1
  have he2 : (singCochainTerm A X 1).germ U x hxU ((singCochainTermD A X 0).app (op U) s) =
      (singCochainTerm A X 1).germ U x hxU 0 := he1.trans (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ he2
  have hd0 : ConcreteCategory.hom ((singCochainTermD A X 0).app (op W))
      ((ConcreteCategory.hom ((singCochainTerm A X 0).map iU.op)) s) = 0 := by
    have hn := ConcreteCategory.congr_hom ((singCochainTermD A X 0).naturality iU.op) s
    exact hn.trans (hW.trans (map_zero _))
  obtain ⟨V, hV, hxV, hnull⟩ := exists_open_nullhomotopic hX x W hxW
  obtain ⟨a, ha⟩ := nullhomotopic_const A ((Opens.toTopCat X).map (homOfLE hV)) hnull
    (ConcreteCategory.hom ((singCochainTerm A X 0).map iU.op) s) hd0
  let cp : TopCat.Presheaf AddCommGrpCat.{u} X := (Functor.const (Opens X)ᵒᵖ).obj A
  refine ⟨stalkTau x cp (cp.germ V x hxV a), ?_⟩
  rw [hf, TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have hres : (ConcreteCategory.hom ((constToCochain A X).app (op V))) a =
      (ConcreteCategory.hom ((singCochainTerm A X 0).map (homOfLE hV).op))
        ((ConcreteCategory.hom ((singCochainTerm A X 0).map iU.op)) s) := by
    refine cochainEval_injective A _ 0 (funext fun σ => ?_)
    exact (cochainEval_constCochain A _ a σ).trans (ha σ).symm
  rw [hres]
  congr 1
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

/-- The augmentation `A_X ⟶ 𝒮^0` is a monomorphism. -/
theorem mono_constAugDeg0 (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    Mono (constAugDeg0 A X) := by
  have hm : ∀ x : X, Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (constAugDeg0 A X).hom) := fun x => by
   rw [AddCommGrpCat.mono_iff_injective, injective_iff_map_eq_zero]
   intro w hw
   have hsurj := fun F => (stalkTau_bijective x F).2
   have hinj := fun F => (stalkTau_bijective x F).1
   let cp : TopCat.Presheaf AddCommGrpCat.{u} X := (Functor.const (Opens X)ᵒᵖ).obj A
   obtain ⟨w', rfl⟩ := hsurj cp w
   obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq cp w'
   have hf : (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
       (constAugDeg0 A X).hom)) (stalkTau x cp (cp.germ U x hxU a)) =
       stalkTau x (singCochainTerm A X 0)
         ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (constToCochain A X) (cp.germ U x
             hxU a)) :=
     ConcreteCategory.congr_hom (stalkTau_naturality x (constToCochain A X)) _
   have hw' : (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
       (constAugDeg0 A X).hom)) (stalkTau x cp (cp.germ U x hxU a)) = 0 := hw
   rw [hf] at hw'
   have h1 := hinj _ (hw'.trans (map_zero _).symm)
   rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at h1
   have h2 : (singCochainTerm A X 0).germ U x hxU ((constToCochain A X).app (op U) a) =
       (singCochainTerm A X 0).germ U x hxU 0 := h1.trans (map_zero _).symm
   obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ h2
   have hn := ConcreteCategory.congr_hom ((constToCochain A X).naturality iU.op) a
   have h3 : cochainEval A ((Opens.toTopCat X).obj W) 0
       (ConcreteCategory.hom ((singCochainTerm A X 0).map iU.op)
         (ConcreteCategory.hom ((constToCochain A X).app (op U)) a))
       ((TopCat.toSSetObj₀Equiv (X := (Opens.toTopCat X).obj W)).symm ⟨x, hxW⟩) = 0 := by
     rw [hW]
     exact congrArg (fun φ => cochainEval A _ 0 φ _) (map_zero _)
   have h4 : ConcreteCategory.hom ((singCochainTerm A X 0).map iU.op)
         (ConcreteCategory.hom ((constToCochain A X).app (op U)) a) =
       constCochain A _ a := by
     exact hn.symm.trans (by rfl)
   rw [h4] at h3
   erw [cochainEval_constCochain] at h3
   rw [h3]
   exact (congrArg (stalkTau x cp) (map_zero _)).trans (map_zero _)
  haveI := hm
  exact TopCat.Presheaf.mono_of_stalk_mono _

section FnSmall

open MMP MMP.SingularChain Finsupp Set

variable {Y : Type u} [TopologicalSpace Y] {M : Type u} [AddCommGroup M]

/-- evaluation of an `M`-valued cochain on an integral chain -/
abbrev evalA {n : ℕ} (φ : Simplex Y n → M) : Chain ℤ Y n →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ φ

/-- coboundary of `M`-valued cochains -/
def cob (n : ℕ) (φ : Simplex Y n → M) : Simplex Y (n + 1) → M :=
  fun σ => ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (σ.comp (face n i))

/-- Evaluating a cochain on a single simplex gives its value there. -/
lemma evalA_single {n : ℕ} (φ : Simplex Y n → M) (σ : Simplex Y n) :
    evalA φ (single σ 1) = φ σ := by simp

/-- Evaluating a cochain on a boundary is evaluating its coboundary. -/
lemma evalA_bd (n : ℕ) (φ : Simplex Y n → M) (c : Chain ℤ Y (n + 1)) :
    evalA φ (bd ℤ n c) = evalA (cob n φ) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, bd_single,
      map_sum]
    simp [cob]

/-- A cochain vanishing on `𝒰`-small simplices vanishes on `𝒰`-small chains. -/
lemma evalA_eq_zero_of_mem_small {n : ℕ} {𝒰 : Set (Set Y)} {φ : Simplex Y n → M}
    (h : ∀ σ : Simplex Y n, (∃ U ∈ 𝒰, range σ ⊆ U) → φ σ = 0) {c : Chain ℤ Y n}
    (hc : c ∈ small ℤ n 𝒰) : evalA φ c = 0 := by
  have hc' := (mem_supported ℤ c).1 hc
  rw [Finsupp.linearCombination_apply]
  exact Finset.sum_eq_zero fun σ hσ => by show c σ • φ σ = 0; rw [h σ (hc' hσ), smul_zero]

/-- The subdivision index of a `𝒰`-small simplex is `0`. -/
lemma smallIndex_eq_zero {𝒰 : Set (Set Y)} (n : ℕ) :
    ∀ σ : Simplex Y n, (∃ U ∈ 𝒰, range σ ⊆ U) → smallIndex ℤ 𝒰 n σ = 0 := by
  have h0 : ∀ {m : ℕ} (σ : Simplex Y m), (∃ U ∈ 𝒰, range σ ⊆ U) → smallIndex₀ ℤ 𝒰 σ = 0 := by
    intro m σ hσ
    classical
    have hs : (subdiv ℤ m ^ 0) (single σ (1 : ℤ)) ∈ small ℤ m 𝒰 := by
      obtain ⟨U, hU, hs⟩ := hσ
      rw [pow_zero]; exact mem_small_of_mem_inside hU (single_mem_inside hs)
    have h : ∃ k, (subdiv ℤ m ^ k) (single σ (1 : ℤ)) ∈ small ℤ m 𝒰 := ⟨0, hs⟩
    simp only [smallIndex₀, h, dite_true]
    exact Nat.eq_zero_of_le_zero (Nat.find_min' h hs)
  induction n with
  | zero => exact fun σ hσ => h0 σ hσ
  | succ n ih =>
    intro σ hσ
    simp only [smallIndex, h0 σ hσ, max_eq_left_iff]
    refine Finset.sup_le fun i _ => ?_
    refine le_of_eq (ih _ ?_)
    obtain ⟨U, hU, hs⟩ := hσ
    exact ⟨U, hU, fun _ ⟨t, ht⟩ => hs ⟨_, ht⟩⟩

/-- The subdivision homotopy vanishes on a `𝒰`-small simplex. -/
lemma smallHomotopy_eq_zero {𝒰 : Set (Set Y)} (n : ℕ) (σ : Simplex Y n)
    (hσ : ∃ U ∈ 𝒰, range σ ⊆ U) : smallHomotopy ℤ 𝒰 n (single σ 1) = 0 := by
  rw [smallHomotopy_single, smallIndex_eq_zero n σ hσ]
  simp [homotopyUpTo]

/-- Evaluating a cochain on the subdivision homotopy of a chain is evaluating the pulled-back
cochain `τ ↦ φ (smallHomotopy τ)` on the chain. -/
lemma evalA_smallHomotopy_pull {𝒰 : Set (Set Y)} (n : ℕ) (φ : Simplex Y (n + 1) → M)
    (c : Chain ℤ Y n) :
    evalA (fun τ : Simplex Y n => evalA φ (smallHomotopy ℤ 𝒰 n (single τ 1))) c =
      evalA φ (smallHomotopy ℤ 𝒰 n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul]
    simp

/-- small-chains acyclicity at the level of cochains: a cocycle vanishing on `𝒰`-small simplices
is the coboundary of a cochain vanishing on `𝒰`-small simplices. -/
theorem exists_cob_eq_of_small {𝒰 : Set (Set Y)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U)
    (h𝒰c : ⋃₀ 𝒰 = univ) (n : ℕ) (φ : Simplex Y (n + 1) → M)
    (hφ : ∀ σ : Simplex Y (n + 1), (∃ U ∈ 𝒰, range σ ⊆ U) → φ σ = 0) (hc : cob (n + 1) φ = 0) :
    ∃ ψ : Simplex Y n → M, cob n ψ = φ ∧ ∀ τ : Simplex Y n, (∃ U ∈ 𝒰, range τ ⊆ U) → ψ τ = 0 := by
  refine ⟨fun τ : Simplex Y n => evalA φ (smallHomotopy ℤ 𝒰 n (single τ 1)), ?_, ?_⟩
  · funext σ
    have h1 : cob n (fun τ : Simplex Y n => evalA φ (smallHomotopy ℤ 𝒰 n (single τ 1))) σ =
        evalA φ (smallHomotopy ℤ 𝒰 n (bd ℤ n (single σ 1))) := by
      rw [← evalA_smallHomotopy_pull, ← evalA_single (cob n _) σ, ← evalA_bd]
    have h2 := smallChainMap_add_succ (R := ℤ) 𝒰 n (single σ 1)
    have h3 : evalA φ (smallChainMap ℤ 𝒰 (n + 1) (single σ 1)) = 0 :=
      evalA_eq_zero_of_mem_small hφ
        (smallChainMap_single_mem_small h𝒰 (n + 1) (by rw [h𝒰c]; exact subset_univ _))
    have h4 : evalA φ (bd ℤ (n + 1) (smallHomotopy ℤ 𝒰 (n + 1) (single σ 1))) = 0 := by
      rw [evalA_bd, hc]; simp
    have h5 := congrArg (evalA φ) h2
    rw [map_add, map_add, h3, h4, zero_add, zero_add, evalA_single] at h5
    rw [h1, h5]
  · intro τ hτ
    simp [smallHomotopy_eq_zero n τ hτ]

end FnSmall

section CochainModel

open scoped Simplicial

/-- The singular `n`-simplices of `Y`. -/
abbrev Sx (Y : Type u) [TopologicalSpace Y] (n : ℕ) :=
    MMP.SingularChain.Simplex Y n

/-- `A`-valued singular `n`-cochains are the functions from `Sx Y n` to `A`. -/
def fnEquiv (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (n : ℕ) :
    ((singChains Y).X n ⟶ A) ≃ (Sx Y n → A) :=
  (cochainEquiv A Y n).trans
    (Equiv.arrowCongr (MMP.SingularCochain.simplexEquiv Y n) (Equiv.refl _))

/-- The function of a cochain is its evaluation on simplices. -/
lemma fnEquiv_apply (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (n : ℕ)
    (φ : (singChains Y).X n ⟶ A) (τ : Sx Y n) :
    fnEquiv A Y n φ τ = cochainEval A Y n φ ((MMP.SingularCochain.simplexEquiv Y
        n).symm τ) :=
  rfl

/-- The function of the pullback of a cochain along `f` is the function of the cochain composed
with `f`. -/
lemma fnEquiv_map (A : AddCommGrpCat.{u}) {Y Z : TopCat.{u}} (f : Z ⟶ Y) (n : ℕ)
    (φ : (singChains Y).X n ⟶ A) (τ : Sx Z n) :
    fnEquiv A Z n ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))).map f).f n ≫ φ) τ = fnEquiv A Y n φ (f.hom.comp τ) := by
  rw [fnEquiv_apply, fnEquiv_apply, cochainEval_map]
  rfl

end CochainModel

section CochainModel2

variable (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ)

/-- The inclusion of an open set as a continuous map. -/
def openVal (V : Opens X) : C(↥V, X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The singular cochain on `V` given by restricting a function on the simplices of `X` to the
simplices of `V`. -/
def reprFn (V : Opens X) (g : Sx X p → A) : (singCochainTerm A X p).obj (op V) :=
  (fnEquiv A ((Opens.toTopCat X).obj V) p).symm (fun τ => g ((openVal X V).comp τ))

/-- The function of the restriction of a cochain from `V` to `W` is the function of the cochain on
simplices of `W` composed into `V`. -/
lemma fnEquiv_res {V W : Opens X} (h : W ≤ V) (φ : (singCochainTerm A X p).obj (op V))
    (τ : Sx ((Opens.toTopCat X).obj W) p) :
    fnEquiv A ((Opens.toTopCat X).obj W) p ((singCochainTerm A X p).map (homOfLE h).op φ) τ =
      fnEquiv A ((Opens.toTopCat X).obj V) p φ (((Opens.toTopCat X).map (homOfLE h)).hom.comp τ) :=
  fnEquiv_map A ((Opens.toTopCat X).map (homOfLE h)) p φ τ

/-- The restriction of `reprFn A X p V g` to `W` is `reprFn A X p W g`. -/
lemma reprFn_res {V W : Opens X} (h : W ≤ V) (g : Sx X p → A) :
    (singCochainTerm A X p).map (homOfLE h).op (reprFn A X p V g) = reprFn A X p W g := by
  apply (fnEquiv A ((Opens.toTopCat X).obj W) p).injective
  funext τ
  rw [fnEquiv_res]
  simp only [reprFn, Equiv.apply_symm_apply]
  rfl

/-- A singular simplex of `X` with image in `V`, as a simplex of `V`. -/
def liftOpen (V : Opens X) (σ : Sx X p) (h : Set.range σ ⊆ V) :
    Sx ((Opens.toTopCat X).obj V) p :=
  ⟨fun t => ⟨σ t, h ⟨t, rfl⟩⟩, σ.continuous.subtype_mk _⟩

/-- Lifting to `V` a simplex of `V` composed into `X` recovers it. -/
lemma liftOpen_openVal_comp (V : Opens X) (τ : Sx ((Opens.toTopCat X).obj V) p)
    (h : Set.range ((openVal X V).comp τ) ⊆ V) :
    liftOpen X p V ((openVal X V).comp τ) h = τ := by ext; rfl

/-- Every singular cochain on `V` is `reprFn A X p V g` for some function `g`. -/
lemma reprFn_surj (V : Opens X) (φ : (singCochainTerm A X p).obj (op V)) :
    ∃ g, reprFn A X p V g = φ := by
  classical
  refine ⟨fun σ => if h : Set.range σ ⊆ V then fnEquiv A ((Opens.toTopCat X).obj V) p φ (liftOpen X
      p V σ h)
    else 0, ?_⟩
  apply (fnEquiv A ((Opens.toTopCat X).obj V) p).injective
  funext τ
  simp only [reprFn, Equiv.apply_symm_apply]
  have h : Set.range ((openVal X V).comp τ) ⊆ V := by
    rintro _ ⟨t, rfl⟩
    exact (τ t).2
  rw [dif_pos h, liftOpen_openVal_comp]

/-- Two functions give the same cochain on `V` exactly when they agree on simplices with image in
`V`. -/
lemma reprFn_eq (V : Opens X) (g g' : Sx X p → A) :
    reprFn A X p V g = reprFn A X p V g' ↔ ∀ t : Sx X p, Set.range t ⊆ V → g t = g' t := by
  constructor
  · intro h t ht
    have := congrFun ((fnEquiv A ((Opens.toTopCat X).obj V) p).symm.injective h)
    have h2 := this (liftOpen X p V t ht)
    exact h2
  · intro h
    refine congrArg (fnEquiv A ((Opens.toTopCat X).obj V) p).symm (funext fun τ => ?_)
    exact h ((openVal X V).comp τ) (by rintro _ ⟨t, rfl⟩; exact (τ t).2)

/-- The function of a sum of cochains is the sum of their functions. -/
lemma fnEquiv_add (Y : TopCat.{u}) (n : ℕ) (φ ψ : (singChains Y).X n ⟶ A) :
    fnEquiv A Y n (φ + ψ) = fnEquiv A Y n φ + fnEquiv A Y n ψ := by
  funext τ
  exact cochainEval_add A Y n φ ψ _

/-- The function of the zero cochain is zero. -/
lemma fnEquiv_zero (Y : TopCat.{u}) (n : ℕ) : fnEquiv A Y n 0 = 0 := by
  funext τ
  rw [fnEquiv_apply]
  unfold cochainEval
  erw [Limits.comp_zero]
  rfl

/-- `reprFn` is additive. -/
lemma reprFn_add (V : Opens X) (g g' : Sx X p → A) :
    reprFn A X p V (g + g') = reprFn A X p V g + reprFn A X p V g' := by
  apply (fnEquiv A ((Opens.toTopCat X).obj V) p).injective
  refine Eq.trans ?_ (fnEquiv_add A _ p _ _).symm
  funext τ
  simp only [reprFn, Equiv.apply_symm_apply, Pi.add_apply]

/-- `reprFn` sends zero to zero. -/
lemma reprFn_zero (V : Opens X) : reprFn A X p V 0 = 0 := by
  apply (fnEquiv A ((Opens.toTopCat X).obj V) p).injective
  refine Eq.trans ?_ (fnEquiv_zero A _ p).symm
  funext τ
  simp only [reprFn, Equiv.apply_symm_apply, Pi.zero_apply]

/-- The function of the coboundary of a cochain takes on a simplex `τ` the alternating sum of its
values on the faces of `τ`. -/
lemma fnEquiv_d (Y : TopCat.{u}) (n : ℕ) (φ : (singChains Y).X n ⟶ A) (τ : Sx Y (n + 1)) :
    fnEquiv A Y (n + 1) ((singChains Y).d (n + 1) n ≫ φ) τ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • fnEquiv A Y n φ (τ.comp
          (MMP.SingularChain.face n i)) := by
  rw [fnEquiv_apply, cochainEval_d]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fnEquiv_apply, MMP.SingularCochain.simplexEquiv_symm_δ]

/-- The coboundary of `reprFn A X p V g` is `reprFn A X (p + 1) V (cob p g)`. -/
lemma reprFn_d (V : Opens X) (g : Sx X p → A) :
    ((singCochainPresheaf A X).obj (op V)).d p (p + 1) (reprFn A X p V g) =
      reprFn A X (p + 1) V (cob p g) := by
  apply (fnEquiv A ((Opens.toTopCat X).obj V) (p + 1)).injective
  have h := fun τ => fnEquiv_d A ((Opens.toTopCat X).obj V) p (reprFn A X p V g) τ
  funext τ
  refine (h τ).trans ?_
  simp only [reprFn, Equiv.apply_symm_apply, cob]
  rfl

end CochainModel2

section FunModelSection

variable {X : TopCat.{u}}

/-- The unit `F ⟶ sheafify F` of sheafification. -/
abbrev unitNat (F : TopCat.Presheaf AddCommGrpCat.{u} X) : F ⟶ (sheafify F).obj :=
  (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.app F

/-- The comparison `stalkTau` sends the germ of a section to the germ of its image in the
sheafification. -/
lemma stalkTau_germ (F : TopCat.Presheaf AddCommGrpCat.{u} X) (U : Opens X) (x : X) (hx : x
    ∈ U)
    (s : F.obj (op U)) :
    stalkTau x F (F.germ U x hx s) = (sheafify F).presheaf.germ U x hx ((unitNat F).app (op U) s) :=
        by
  unfold stalkTau
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (unitNat F) s

/-- Every section of the sheafification of `P` over `V` is, near each point of `V`, the image of a
section of `P`. -/
lemma exists_local_repr (P : TopCat.Presheaf AddCommGrpCat.{u} X) (V : Opens X)
    (s : (sheafify P).obj.obj (op V)) (x : X) (hx : x ∈ V) :
    ∃ (W : Opens X) (hW : W ≤ V) (_ : x ∈ W) (ψ : P.obj (op W)),
      (unitNat P).app (op W) ψ = (sheafify P).obj.map (homOfLE hW).op s := by
  obtain ⟨e, he⟩ := (stalkTau_bijective x P).2 ((sheafify P).presheaf.germ V x hx s)
  obtain ⟨U, hxU, ψ, rfl⟩ := TopCat.Presheaf.exists_germ_eq P e
  rw [stalkTau_germ] at he
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hx _ _ he
  refine ⟨W, leOfHom iV, hxW, P.map iU.op ψ, ?_⟩
  have hn := ConcreteCategory.congr_hom ((unitNat P).naturality iU.op) ψ
  exact hn.trans hW

/-- A presheaf modelled on functions on a set `T` with supports `rng` (singular cochains). -/
structure FunModel (A : Type u) [AddCommGroup A] (P : TopCat.Presheaf AddCommGrpCat.{u} X)
    where
  /-- The index set of the model (e.g. the singular simplices). -/
  T : Type u
  /-- The support of an element of `T`. -/
  rng : T → Set X
  /-- Every support is nonempty. -/
  rng_nonempty : ∀ t, (rng t).Nonempty
  /-- The section over `V` represented by a function `T → A`. -/
  repr : ∀ V : Opens X, (T → A) → P.obj (op V)
  /-- Representation is compatible with restriction. -/
  repr_res : ∀ {V W : Opens X} (h : W ≤ V) (g : T → A), P.map (homOfLE h).op (repr V g) = repr W g
  /-- Every section is represented by some function. -/
  repr_surj : ∀ (V : Opens X) (φ : P.obj (op V)), ∃ g, repr V g = φ
  /-- Two functions represent the same section over `V` iff they agree on every element supported
  in `V`. -/
  repr_eq : ∀ (V : Opens X) (g g' : T → A), repr V g = repr V g' ↔ ∀ t, rng t ⊆ V → g t = g' t

variable {A : Type u} [AddCommGroup A] {P : TopCat.Presheaf AddCommGrpCat.{u} X}

/-- Two representatives of the same section of the sheafification agree, near each point of the
intersection of their domains, on all elements supported there. -/
lemma FunModel.agree (M : FunModel A P) (V : Opens X) (s : (sheafify P).obj.obj (op V))
    {W₁ W₂ : Opens X} (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V) (g₁ g₂ : M.T → A)
    (e₁ : (unitNat P).app (op W₁) (M.repr W₁ g₁) = (sheafify P).obj.map (homOfLE h₁).op s)
    (e₂ : (unitNat P).app (op W₂) (M.repr W₂ g₂) = (sheafify P).obj.map (homOfLE h₂).op s)
    (x : X) (hx₁ : x ∈ W₁) (hx₂ : x ∈ W₂) :
    ∃ N : Opens X, N ≤ W₁ ⊓ W₂ ∧ x ∈ N ∧ ∀ t, M.rng t ⊆ N → g₁ t = g₂ t := by
  have hg : stalkTau x P (P.germ W₁ x hx₁ (M.repr W₁ g₁)) = stalkTau x P (P.germ W₂ x hx₂ (M.repr W₂
      g₂)) := by
    rw [stalkTau_germ, stalkTau_germ, e₁, e₂]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hx₁ hx₂ _ _ ((stalkTau_bijective x P).1 hg)
  have r1 : P.map iU.op (M.repr W₁ g₁) = M.repr W g₁ := M.repr_res (leOfHom iU) g₁
  have r2 : P.map iV.op (M.repr W₂ g₂) = M.repr W g₂ := M.repr_res (leOfHom iV) g₂
  rw [r1, r2, M.repr_eq] at hW
  exact ⟨W, le_inf (leOfHom iU) (leOfHom iV), hxW, fun t ht => hW t ht⟩

/-- On a paracompact normal space, an open cover has a locally finite open refinement `u` with
`closure (u i) ⊆ W i`. -/
lemma exists_shrink {Y : Type*} [TopologicalSpace Y] [ParacompactSpace Y] [NormalSpace Y]
    {ι : Type*} (W : ι → Set Y) (hW : ∀ i, IsOpen (W i)) (hc : ⋃ i, W i = Set.univ) :
    ∃ u : ι → Set Y, (∀ i, IsOpen (u i)) ∧ ⋃ i, u i = Set.univ ∧ LocallyFinite u ∧
      ∀ i, closure (u i) ⊆ W i := by
  obtain ⟨v, hvo, hvc, hvl, hvW⟩ := precise_refinement W hW hc
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_subset_iUnion_closure_subset (u := v) (s := Set.univ)
    isClosed_univ hvo (fun x _ => hvl.point_finite x) (by rw [hvc])
  refine ⟨u, hu2, Set.eq_univ_of_univ_subset hu1, hvl.subset fun i => ?_, fun i => ?_⟩
  · exact subset_closure.trans (hu3 i)
  · exact (hu3 i).trans (hvW i)

/-- On a paracompact normal open set, every section of the sheafification of a presheaf with a
function model is the image of a section of the presheaf. -/
lemma FunModel.exists_glue (M : FunModel A P) (V : Opens X) [ParacompactSpace V]
    [NormalSpace V]
    (s : (sheafify P).obj.obj (op V)) :
    ∃ φ : P.obj (op V), (unitNat P).app (op V) φ = s := by
  classical
  have hloc := fun (x : V) => exists_local_repr P V s x.1 x.2
  choose W hWV hxW ψ hψ using hloc
  have hg := fun (x : V) => M.repr_surj (W x) (ψ x)
  choose g hg using hg
  have he : ∀ x : V, (unitNat P).app (op (W x)) (M.repr (W x) (g x)) =
      (sheafify P).obj.map (homOfLE (hWV x)).op s := fun x => by rw [hg x]; exact hψ x
  obtain ⟨u, huo, huc, hul, hucl⟩ := exists_shrink (fun i : V => (Subtype.val ⁻¹' (W i : Set X) :
      Set V))
    (fun i => (W i).isOpen.preimage continuous_subtype_val)
    (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨y, hxW y⟩)
  let g0 : M.T → A := fun t =>
    if h : ∃ i : V, M.rng t ⊆ Subtype.val '' u i then g (Classical.choose h) t else 0
  have hC : ∀ x (hx : x ∈ V), ∃ (i0 : V) (N : Opens X), N ≤ W i0 ∧ N ≤ V ∧ x ∈ N ∧
      ∀ t, M.rng t ⊆ N → g0 t = g i0 t := by
    intro x hx
    set xv : V := ⟨x, hx⟩ with hxv
    obtain ⟨i0, hi0⟩ := Set.mem_iUnion.1 (huc ▸ Set.mem_univ xv)
    obtain ⟨Nv, hNv, hfin⟩ := hul xv
    have hNi : ∀ i : V, ∃ Ni : Opens X, xv ∈ closure (u i) →
        (x ∈ Ni ∧ Ni ≤ W i ⊓ W i0 ∧ ∀ t, M.rng t ⊆ Ni → g i t = g i0 t) := by
      intro i
      by_cases hc : xv ∈ closure (u i)
      · have hxi : x ∈ W i := hucl i hc
        have hxi0 : x ∈ W i0 := hucl i0 (subset_closure hi0)
        obtain ⟨N, hN1, hN2, hN3⟩ := M.agree V s (hWV i) (hWV i0) (g i) (g i0) (he i) (he i0) x hxi
            hxi0
        exact ⟨N, fun _ => ⟨hN2, hN1, hN3⟩⟩
      · exact ⟨⊥, fun h => absurd h hc⟩
    choose Ni hNi using hNi
    let F : V → Set V := fun i => if xv ∈ closure (u i) then Subtype.val ⁻¹' (Ni i : Set X) else
        (closure (u i))ᶜ
    have hFo : ∀ i, IsOpen (F i) := fun i => by
      by_cases hc : xv ∈ closure (u i)
      · simpa only [F, if_pos hc] using (Ni i).isOpen.preimage continuous_subtype_val
      · simpa only [F, if_neg hc] using isClosed_closure.isOpen_compl
    have hFx : ∀ i, xv ∈ F i := fun i => by
      by_cases hc : xv ∈ closure (u i)
      · simp only [F, if_pos hc]; exact (hNi i hc).1
      · simp only [F, if_neg hc]; exact hc
    let S : Set V := interior Nv ∩ u i0 ∩ ⋂ i ∈ hfin.toFinset, F i
    have hSo : IsOpen S := by
      refine (isOpen_interior.inter (huo i0)).inter ?_
      exact Set.Finite.isOpen_biInter hfin.toFinset.finite_toSet fun i _ => hFo i
    have hxS : xv ∈ S := ⟨⟨mem_interior_iff_mem_nhds.2 hNv, hi0⟩, Set.mem_iInter₂.2 fun i _ => hFx
        i⟩
    have hSV : IsOpen (Subtype.val '' S) := V.isOpen.isOpenMap_subtype_val S hSo
    refine ⟨i0, ⟨Subtype.val '' S, hSV⟩, ?_, ?_, ⟨xv, hxS, rfl⟩, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hucl i0 (subset_closure hy.1.2)
    · rintro _ ⟨y, hy, rfl⟩
      exact y.2
    · intro t ht
      have hex : ∃ i : V, M.rng t ⊆ Subtype.val '' u i := ⟨i0, fun q hq => by
        obtain ⟨y, hy, rfl⟩ := ht hq
        exact ⟨y, hy.1.2, rfl⟩⟩
      have h0 : g0 t = g (Classical.choose hex) t := dif_pos hex
      rw [h0]
      set j := Classical.choose hex with hj
      have hjt : M.rng t ⊆ Subtype.val '' u j := Classical.choose_spec hex
      obtain ⟨p, hp⟩ := M.rng_nonempty t
      obtain ⟨y, hyS, rfl⟩ := ht hp
      obtain ⟨y', hy'u, hy'⟩ := hjt hp
      have hyy : y' = y := Subtype.ext hy'
      subst hyy
      have hjG : j ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨y', hy'u, interior_subset hyS.1.1⟩
      have hyF : y' ∈ F j := Set.mem_iInter₂.1 hyS.2 j hjG
      by_cases hc : xv ∈ closure (u j)
      · refine (hNi j hc).2.2 t (fun q hq => ?_)
        obtain ⟨z, hz, rfl⟩ := ht hq
        have hzF : z ∈ F j := Set.mem_iInter₂.1 hz.2 j hjG
        simp only [F, if_pos hc] at hzF
        exact hzF
      · simp only [F, if_neg hc] at hyF
        exact absurd (subset_closure hy'u) hyF
  refine ⟨M.repr V g0, TopCat.Presheaf.section_ext (sheafify P) V _ _ fun x hx => ?_⟩
  obtain ⟨i0, N, hNW, hNV, hxN, hNg⟩ := hC x hx
  rw [← TopCat.Presheaf.germ_res_apply (sheafify P).presheaf (homOfLE hNV) x hxN,
    ← TopCat.Presheaf.germ_res_apply (sheafify P).presheaf (homOfLE hNV) x hxN s]
  congr 1
  have h1 : (sheafify P).obj.map (homOfLE hNV).op ((unitNat P).app (op V) (M.repr V g0)) =
      (unitNat P).app (op N) (P.map (homOfLE hNV).op (M.repr V g0)) :=
    (ConcreteCategory.congr_hom ((unitNat P).naturality (homOfLE hNV).op) (M.repr V g0)).symm
  have h2 : P.map (homOfLE hNV).op (M.repr V g0) = P.map (homOfLE hNW).op (M.repr (W i0) (g i0)) :=
      by
    rw [M.repr_res hNV, M.repr_res hNW, M.repr_eq]
    exact hNg
  have h3 : (unitNat P).app (op N) (P.map (homOfLE hNW).op (M.repr (W i0) (g i0))) =
      (sheafify P).obj.map (homOfLE hNW).op ((unitNat P).app (op (W i0)) (M.repr (W i0) (g i0))) :=
    ConcreteCategory.congr_hom ((unitNat P).naturality (homOfLE hNW).op) (M.repr (W i0) (g i0))
  have h4 : (sheafify P).obj.map (homOfLE hNV).op s =
      (sheafify P).obj.map (homOfLE hNW).op ((sheafify P).obj.map (homOfLE (hWV i0)).op s) := by
    rw [← ConcreteCategory.comp_apply, ← (sheafify P).obj.map_comp]
    rfl
  erw [h1, h2, h3, he i0]
  exact h4.symm

end FunModelSection

section Flasque5

/-- The function model of singular `p`-cochains: functions on singular `p`-simplices, supported on
their images. -/
def cochainFunModel (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) :
    FunModel (A : Type u) (singCochainTerm A X p) where
  T := Sx X p
  rng := fun t => Set.range t
  rng_nonempty := fun t => ⟨t (stdSimplex.vertex 0), ⟨_, rfl⟩⟩
  repr := reprFn A X p
  repr_res := reprFn_res A X p
  repr_surj := reprFn_surj A X p
  repr_eq := reprFn_eq A X p

/-- The sheafified singular cochains are flasque on a metrizable space. -/
theorem singCochainSheaves_isFlasque (A : AddCommGrpCat.{u}) (X : TopCat.{u})
    [MetrizableSpace X] (p : ℕ) : TopCat.Presheaf.IsFlasque ((singCochainSheaves A X).X p).obj where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    haveI : MetrizableSpace V.unop := Topology.IsEmbedding.subtypeVal.metrizableSpace
    letI := TopologicalSpace.metrizableSpaceMetric V.unop
    obtain ⟨φ, hφ⟩ := (cochainFunModel A X p).exists_glue V.unop t
    obtain ⟨g, rfl⟩ := reprFn_surj A X p V.unop φ
    refine ⟨(unitNat (singCochainTerm A X p)).app U (reprFn A X p U.unop g), ?_⟩
    have h1 : (unitNat (singCochainTerm A X p)).app V ((singCochainTerm A X p).map i (reprFn A X p
        U.unop g)) =
        (sheafify (singCochainTerm A X p)).obj.map i
          ((unitNat (singCochainTerm A X p)).app U (reprFn A X p U.unop g)) :=
      ConcreteCategory.congr_hom ((unitNat (singCochainTerm A X p)).naturality i) _
    have h2 : (singCochainTerm A X p).map i (reprFn A X p U.unop g) = reprFn A X p V.unop g :=
      reprFn_res A X p (leOfHom i.unop) g
    rw [h2] at h1
    exact h1.symm.trans hφ

end Flasque5

section Step6

/-- The complex of global sections of the sheafified singular cochains. -/
abbrev gammaS (A : AddCommGrpCat.{u}) (X : TopCat.{u}) : CochainComplex AddCommGrpCat.{u}
    ℕ :=
  ((globalSections X).mapHomologicalComplex _).obj (singCochainSheaves A X)

/-- The map from singular cochains on `X` to global sections of the sheafified singular
cochains. -/
def singEps (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    (singCochainPresheaf A X).obj (op ⊤) ⟶ gammaS A X where
  f p := (unitNat (singCochainTerm A X p)).app (op ⊤)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have e : (singCochainPresheafComplex A X).d i (i + 1) = singCochainTermD A X i :=
      CochainComplex.of_d _ _ _
    have h := (sheafificationAdjunction (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).unit.naturality
      (singCochainTermD A X i)
    have h2 := congrArg (fun t => t.app (op ⊤)) h
    simp only [Functor.id_map, NatTrans.comp_app] at h2
    have hd : (gammaS A X).d i (i + 1) =
        ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
          (singCochainTermD A X i)).hom.app (op ⊤) := by
      change ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        ((singCochainPresheafComplex A X).d i (i + 1))).hom.app (op ⊤) = _
      rw [e]
      rfl
    rw [hd]
    exact h2.symm

/-- A cochain vanishing on all simplices that are small for some open cover. -/
def LocZero {A : AddCommGrpCat.{u}} {X : TopCat.{u}} {p : ℕ} (g : Sx X p → A) : Prop :=
  ∃ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) ∧ ⋃₀ 𝒰 = Set.univ ∧
    ∀ t : Sx X p, (∃ U ∈ 𝒰, Set.range t ⊆ U) → g t = 0

/-- A cochain whose image in global sections of the sheafified cochains is zero vanishes on all
simplices small for some open cover. -/
lemma locZero_of_eps_eq_zero (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (g : Sx X p →
    A)
    (h : (singEps A X).f p (reprFn A X p ⊤ g) = 0) : LocZero g := by
  classical
  have hloc : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ t : Sx X p, Set.range t ⊆ W → g t = 0 := by
    intro x
    have hx : x ∈ (⊤ : Opens X) := trivial
    have hg : stalkTau x (singCochainTerm A X p) ((singCochainTerm A X p).germ ⊤ x hx (reprFn A X p
        ⊤ g)) =
        stalkTau x (singCochainTerm A X p) ((singCochainTerm A X p).germ ⊤ x hx 0) := by
      rw [stalkTau_germ, stalkTau_germ]
      have h' : (unitNat (singCochainTerm A X p)).app (op ⊤) (reprFn A X p ⊤ g) = 0 := h
      rw [h']
      rw [map_zero, map_zero, map_zero]
    obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hx hx _ _ ((stalkTau_bijective x _).1 hg)
    refine ⟨W, hxW, ?_⟩
    have r1 : (singCochainTerm A X p).map iU.op (reprFn A X p ⊤ g) = reprFn A X p W g :=
      reprFn_res A X p (leOfHom iU) g
    rw [r1, map_zero, ← reprFn_zero A X p W, reprFn_eq] at hW
    exact fun t ht => by simpa using hW t ht
  choose W hxW hW using hloc
  refine ⟨Set.range (fun x => (W x : Set X)), ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩; exact (W x).isOpen
  · exact Set.eq_univ_of_forall fun x => Set.mem_sUnion.2 ⟨_, ⟨x, rfl⟩, hxW x⟩
  · rintro t ⟨_, ⟨x, rfl⟩, ht⟩
    exact hW x t ht

/-- A cochain vanishing on all simplices small for some open cover has zero image in global
sections of the sheafified cochains. -/
lemma eps_eq_zero_of_locZero (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (g : Sx X p →
    A)
    (h : LocZero g) : (singEps A X).f p (reprFn A X p ⊤ g) = 0 := by
  obtain ⟨𝒰, ho, hc, hv⟩ := h
  refine TopCat.Presheaf.section_ext (sheafify (singCochainTerm A X p)) ⊤ _ _ fun x hx => ?_
  obtain ⟨U, hU, hxU⟩ := Set.mem_sUnion.1 (hc ▸ Set.mem_univ x)
  let U' : Opens X := ⟨U, ho U hU⟩
  have hle : U' ≤ ⊤ := le_top
  have hz : (singCochainTerm A X p).map (homOfLE hle).op (reprFn A X p ⊤ g) = 0 := by
    rw [reprFn_res, ← reprFn_zero A X p U', reprFn_eq]
    exact fun t ht => hv t ⟨U, hU, ht⟩
  change (sheafify (singCochainTerm A X p)).presheaf.germ ⊤ x hx
      ((unitNat (singCochainTerm A X p)).app (op ⊤) (reprFn A X p ⊤ g)) = _
  rw [← TopCat.Presheaf.germ_res_apply (sheafify (singCochainTerm A X p)).presheaf (homOfLE hle) x
      hxU]
  have h1 : (sheafify (singCochainTerm A X p)).obj.map (homOfLE hle).op
      ((unitNat (singCochainTerm A X p)).app (op ⊤) (reprFn A X p ⊤ g)) =
      (unitNat (singCochainTerm A X p)).app (op U') ((singCochainTerm A X p).map (homOfLE hle).op
          (reprFn A X p ⊤ g)) :=
    (ConcreteCategory.congr_hom ((unitNat (singCochainTerm A X p)).naturality (homOfLE hle).op)
        _).symm
  erw [h1, hz, map_zero, map_zero, map_zero]

/-- On a metrizable space, every global section of the sheafified singular `p`-cochains is the
image of a singular cochain. -/
lemma eps_surj (A : AddCommGrpCat.{u}) (X : TopCat.{u}) [MetrizableSpace X] (p : ℕ)
    (s : (gammaS A X).X p) : ∃ g : Sx X p → A, (singEps A X).f p (reprFn A X p ⊤ g) = s := by
  haveI : MetrizableSpace (⊤ : Opens X) := Topology.IsEmbedding.subtypeVal.metrizableSpace
  letI := TopologicalSpace.metrizableSpaceMetric (⊤ : Opens X)
  obtain ⟨φ, hφ⟩ := (cochainFunModel A X p).exists_glue ⊤ s
  obtain ⟨g, rfl⟩ := reprFn_surj A X p ⊤ φ
  exact ⟨g, hφ⟩

/-- `reprFn` commutes with subtraction. -/
lemma reprFn_sub (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (V : Opens X) (g g' : Sx X
    p → A) :
    reprFn A X p V (g - g') = reprFn A X p V g - reprFn A X p V g' := by
  rw [eq_sub_iff_add_eq, ← reprFn_add, sub_add_cancel]

/-- On `X` itself, `reprFn` is injective. -/
lemma reprFn_top_injective (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) {g g' : Sx X p →
    A}
    (h : reprFn A X p ⊤ g = reprFn A X p ⊤ g') : g = g' :=
  funext fun t => (reprFn_eq A X p ⊤ g g').1 h t (fun _ _ => trivial)

/-- The coboundary commutes with subtraction. -/
lemma cob_sub (n : ℕ) {A : AddCommGrpCat.{u}} {X : TopCat.{u}} (g g' : Sx X n → A) :
    cob n (g - g') = cob n g - cob n g' := by
  funext σ
  simp [cob, smul_sub, Finset.sum_sub_distrib]

/-- The coboundary of a coboundary is zero. -/
lemma cob_cob (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (g : Sx X p → A) :
    cob (p + 1) (cob p g) = 0 := by
  apply reprFn_top_injective A X (p + 2)
  have h := ConcreteCategory.congr_hom (((singCochainPresheaf A X).obj (op ⊤)).d_comp_d p (p + 1) (p
      + 2))
    (reprFn A X p ⊤ g)
  rw [reprFn_zero]
  erw [← reprFn_d, ← reprFn_d]
  erw [← ConcreteCategory.comp_apply]
  rw [HomologicalComplex.d_comp_d]
  rfl

/-- `singEps` commutes with the differentials. -/
lemma eps_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (x : ((singCochainPresheaf A
    X).obj (op ⊤)).X p) :
    (singEps A X).f (p + 1) (((singCochainPresheaf A X).obj (op ⊤)).d p (p + 1) x) =
      (gammaS A X).d p (p + 1) ((singEps A X).f p x) :=
  (ConcreteCategory.congr_hom ((singEps A X).comm p (p + 1)) x).symm

/-- On a metrizable space, every global cocycle of the sheafified singular cochains is the image of
a singular cocycle. -/
lemma eps_surj_cohom (A : AddCommGrpCat.{u}) (X : TopCat.{u}) [MetrizableSpace X] (q : ℕ)
    (y : (gammaS A X).X q) (hy : (gammaS A X).d q (q + 1) y = 0) :
    ∃ g : Sx X q → A, cob q g = 0 ∧ (singEps A X).f q (reprFn A X q ⊤ g) = y := by
  obtain ⟨g, hg⟩ := eps_surj A X q y
  have h1 : (singEps A X).f (q + 1) (reprFn A X (q + 1) ⊤ (cob q g)) = 0 := by
    have e1 := eps_d A X q (reprFn A X q ⊤ g)
    rw [hg, hy] at e1
    erw [reprFn_d] at e1
    exact e1
  obtain ⟨𝒰, ho, hc, hv⟩ := locZero_of_eps_eq_zero A X (q + 1) _ h1
  obtain ⟨ψ, hψ, hψv⟩ := exists_cob_eq_of_small ho hc q (cob q g) hv (cob_cob A X q g)
  refine ⟨g - ψ, ?_, ?_⟩
  · rw [cob_sub, hψ, sub_self]
  · have h2 := eps_eq_zero_of_locZero A X q ψ ⟨𝒰, ho, hc, hψv⟩
    rw [reprFn_sub]
    erw [map_sub, hg, h2, sub_zero]

/-- The coboundary is additive. -/
lemma cob_add (n : ℕ) {A : AddCommGrpCat.{u}} {X : TopCat.{u}} (g g' : Sx X n → A) :
    cob n (g + g') = cob n g + cob n g' := by
  funext σ
  simp [cob, smul_add, Finset.sum_add_distrib]

/-- On a metrizable space, a singular cocycle of positive degree whose image in global sections is
a coboundary is a singular coboundary. -/
lemma eps_inj_succ (A : AddCommGrpCat.{u}) (X : TopCat.{u}) [MetrizableSpace X] (m : ℕ)
    (g : Sx X (m + 1) → A) (hg : cob (m + 1) g = 0) (t : (gammaS A X).X m)
    (ht : (singEps A X).f (m + 1) (reprFn A X (m + 1) ⊤ g) = (gammaS A X).d m (m + 1) t) :
    ∃ h : Sx X m → A, cob m h = g := by
  obtain ⟨h0, hh0⟩ := eps_surj A X m t
  have h1 : (singEps A X).f (m + 1) (reprFn A X (m + 1) ⊤ (g - cob m h0)) = 0 := by
    rw [reprFn_sub]
    have e1 := eps_d A X m (reprFn A X m ⊤ h0)
    rw [hh0] at e1
    erw [reprFn_d] at e1
    erw [map_sub, e1, ht, sub_self]
  obtain ⟨𝒰, ho, hc, hv⟩ := locZero_of_eps_eq_zero A X (m + 1) _ h1
  obtain ⟨ψ, hψ, -⟩ := exists_cob_eq_of_small ho hc m (g - cob m h0) hv (by
    rw [cob_sub, hg, cob_cob, sub_zero])
  refine ⟨ψ + h0, ?_⟩
  rw [cob_add, hψ, sub_add_cancel]

end Step6

end

noncomputable section Comparison

/-- The integers as an abelian group. -/
abbrev Zc : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ

variable (M : TopCat.{0})

/-- Sheaves of abelian groups on `M`. -/
abbrev Sh : Type 1 := Sheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}

/-- The sheafified integral singular cochains. -/
abbrev KS : CochainComplex (Sh M) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).mapHomologicalComplex _).obj
    (singCochainPresheafComplex Zc M)

/-- The augmentation `ℤ_M ⟶ 𝒮⁰`. -/
abbrev aug0 : ZSh M ⟶ (KS M).X 0 :=
  (presheafToSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).map (constToCochain Zc M)

/-- The sheaf of `1`-cocycles. -/
abbrev Z1 : Sh M := kernel ((KS M).d 1 2)

/-- The sheaf of `2`-cocycles. -/
abbrev Z2 : Sh M := kernel ((KS M).d 2 3)

/-- The map `𝒮⁰ ⟶ Z¹` induced by the differential. -/
def g1 : (KS M).X 0 ⟶ Z1 M := kernel.lift _ ((KS M).d 0 1) ((KS M).d_comp_d 0 1 2)

/-- The map `𝒮¹ ⟶ Z²` induced by the differential. -/
def g2 : (KS M).X 1 ⟶ Z2 M := kernel.lift _ ((KS M).d 1 2) ((KS M).d_comp_d 1 2 3)

/-- `g1` followed by the inclusion `Z¹ ⟶ 𝒮¹` is the differential. -/
lemma g1_ι : g1 M ≫ kernel.ι _ = (KS M).d 0 1 := kernel.lift_ι _ _ _

/-- `g2` followed by the inclusion `Z² ⟶ 𝒮²` is the differential. -/
lemma g2_ι : g2 M ≫ kernel.ι _ = (KS M).d 1 2 := kernel.lift_ι _ _ _

/-- The augmentation `ℤ_M ⟶ 𝒮⁰` composed with the differential is zero. -/
lemma aug0_d : aug0 M ≫ (KS M).d 0 1 = 0 := constAugDeg0_comp_d Zc M

/-- The augmentation `ℤ_M ⟶ 𝒮⁰` composed with `g1` is zero. -/
lemma w1 : aug0 M ≫ g1 M = 0 := by
  rw [← cancel_mono (kernel.ι ((KS M).d 1 2)), Category.assoc, g1_ι, zero_comp]
  exact aug0_d M

/-- The inclusion `Z¹ ⟶ 𝒮¹` composed with `g2` is zero. -/
lemma w2 : kernel.ι ((KS M).d 1 2) ≫ g2 M = 0 := by
  rw [← cancel_mono (kernel.ι ((KS M).d 2 3)), Category.assoc, g2_ι, zero_comp]
  exact kernel.condition _

/-- `0 ⟶ ℤ_M ⟶ 𝒮⁰ ⟶ Z¹ ⟶ 0`. -/
abbrev S1 : ShortComplex (Sh M) := ShortComplex.mk (aug0 M) (g1 M) (w1 M)

/-- `0 ⟶ Z¹ ⟶ 𝒮¹ ⟶ Z² ⟶ 0`. -/
abbrev S2 : ShortComplex (Sh M) :=
  ShortComplex.mk (kernel.ι ((KS M).d 1 2)) (g2 M) (w2 M)

variable {M}

/-- The sheafified integral singular cochains on a locally contractible space are exact in positive
degrees. -/
lemma KS_exactAt (hM : LocallyContractibleSpace M) (n : ℕ) : (KS M).ExactAt (n + 1) :=
  singCochainSheaves_exactAt Zc M hM n

/-- On a locally contractible space, `0 ⟶ ℤ_M ⟶ 𝒮⁰ ⟶ Z¹ ⟶ 0` is short exact. -/
lemma S1_shortExact (hM : LocallyContractibleSpace M) : (S1 M).ShortExact := by
  have hex : (ShortComplex.mk (aug0 M) ((KS M).d 0 1) (aug0_d M)).Exact :=
    exact_constAugDeg0 Zc M hM
  have : Mono (aug0 M) := mono_constAugDeg0 Zc M
  refine ShortComplex.ShortExact.mk' ?_ inferInstance ?_
  · let φ : S1 M ⟶ ShortComplex.mk (aug0 M) ((KS M).d 0 1) (aug0_d M) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι _, comm₂₃ := (Category.id_comp _).trans (g1_ι M).symm }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hex
  · have h1 := ((KS M).exactAt_iff' 0 1 2 (by simp) (by simp)).1 (KS_exactAt hM 0)
    exact h1.epi_kernelLift

/-- On a locally contractible space, `0 ⟶ Z¹ ⟶ 𝒮¹ ⟶ Z² ⟶ 0` is short exact. -/
lemma S2_shortExact (hM : LocallyContractibleSpace M) : (S2 M).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ inferInstance ?_
  · let φ : S2 M ⟶ ShortComplex.mk (kernel.ι ((KS M).d 1 2)) ((KS M).d 1 2) (kernel.condition _) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι _, comm₂₃ := (Category.id_comp _).trans (g2_ι M).symm }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
  · have h1 := ((KS M).exactAt_iff' 1 2 3 (by simp) (by simp)).1 (KS_exactAt hM 1)
    exact h1.epi_kernelLift

section Psi

open CategoryTheory.Abelian Stacks.SupportedVanishing

/-- The global section of `𝒮^p` of a singular cochain. -/
def epsG (p : ℕ) (g : Sx M p → ℤ) : ToType (((KS M).X p).obj.obj (op ⊤)) :=
  (singEps Zc M).f p (reprFn Zc M p ⊤ g)

/-- The differential of `𝒮^•` sends `epsG p g` to `epsG (p + 1) (cob p g)`. -/
lemma epsG_d (p : ℕ) (g : Sx M p → ℤ) :
    ((KS M).d p (p + 1)).hom.app (op ⊤) (epsG p g) = epsG (p + 1) (cob p g) := by
  have e1 := eps_d Zc M p (reprFn Zc M p ⊤ g)
  erw [reprFn_d] at e1
  exact e1.symm

/-- `epsG` is additive. -/
lemma epsG_add (p : ℕ) (g g' : Sx M p → ℤ) : epsG p (g + g') = epsG p g + epsG p g' := by
  simp only [epsG]
  erw [reprFn_add]
  exact map_add _ _ _

/-- `epsG` sends zero to zero. -/
lemma epsG_zero (p : ℕ) : epsG (M := M) p 0 = 0 := by
  simp only [epsG]
  erw [reprFn_zero]
  exact map_zero _

/-- The morphism `ℤ_M ⟶ 𝒮^p` of a singular cochain. -/
def epsH (p : ℕ) (g : Sx M p → ℤ) : constZ M ⟶ (KS M).X p :=
  (homConstAddEquiv _).symm (epsG p g)

/-- The global section corresponding to `epsH p g` is `epsG p g`. -/
lemma homConstAddEquiv_epsH (p : ℕ) (g : Sx M p → ℤ) :
    homConstAddEquiv _ (epsH p g) = epsG p g := by
  simp [epsH]

/-- `epsH p g` followed by the differential of `𝒮^•` is `epsH (p + 1) (cob p g)`. -/
lemma epsH_d (p : ℕ) (g : Sx M p → ℤ) :
    epsH p g ≫ (KS M).d p (p + 1) = epsH (p + 1) (cob p g) := by
  apply (homConstAddEquiv _).injective
  rw [homConstAddEquiv_comp, homConstAddEquiv_epsH, homConstAddEquiv_epsH]
  exact epsG_d p g

/-- `epsH` is additive. -/
lemma epsH_add (p : ℕ) (g g' : Sx M p → ℤ) : epsH p (g + g') = epsH p g + epsH p g' := by
  simp only [epsH, epsG_add, map_add]

/-- `epsH` sends zero to zero. -/
lemma epsH_zero (p : ℕ) : epsH (M := M) p 0 = 0 := by
  simp only [epsH, epsG_zero, map_zero]

/-- The morphism of a singular `2`-cocycle lands in the `2`-cocycles of `𝒮^•`. -/
lemma epsH_cocycle (z : Sx M 2 → ℤ) (hz : cob 2 z = 0) :
    epsH 2 z ≫ (KS M).d 2 3 = 0 := by
  rw [epsH_d, hz, epsH_zero]

/-- The morphism `ℤ_M ⟶ Z²` of a singular `2`-cocycle. -/
def zhat (z : Sx M 2 → ℤ) (hz : cob 2 z = 0) : constZ M ⟶ Z2 M :=
  kernel.lift _ (epsH 2 z) (epsH_cocycle z hz)

/-- `zhat z hz` followed by the inclusion `Z² ⟶ 𝒮²` is `epsH 2 z`. -/
lemma zhat_ι (z : Sx M 2 → ℤ) (hz : cob 2 z = 0) :
    zhat z hz ≫ kernel.ι _ = epsH 2 z := kernel.lift_ι _ _ _

/-- `zhat` is additive. -/
lemma zhat_add (z z' : Sx M 2 → ℤ) (hz : cob 2 z = 0) (hz' : cob 2 z' = 0)
    (h : cob 2 (z + z') = 0) : zhat (z + z') h = zhat z hz + zhat z' hz' := by
  rw [← cancel_mono (kernel.ι ((KS M).d 2 3)), Preadditive.add_comp, zhat_ι, zhat_ι, zhat_ι,
    epsH_add]

/-- The morphism of the coboundary of `m` is `epsH 1 m` followed by `g2`. -/
lemma zhat_cob (m : Sx M 1 → ℤ) (h : cob 2 (cob 1 m) = 0) :
    zhat (cob 1 m) h = epsH 1 m ≫ g2 M := by
  rw [← cancel_mono (kernel.ι ((KS M).d 2 3)), zhat_ι, Category.assoc, g2_ι, epsH_d]

variable (hM : LocallyContractibleSpace M)

/-- The class in `Ext²(ℤ_M, ℤ_M)` of a singular `2`-cocycle. -/
def Psi (z : Sx M 2 → ℤ) (hz : cob 2 z = 0) : Ext (constZ M) (ZSh M) 2 :=
  ((Ext.mk₀ (zhat z hz)).comp (S2_shortExact hM).extClass (zero_add 1)).comp
    (S1_shortExact hM).extClass (show 1 + 1 = 2 from rfl)

/-- `Psi` is additive. -/
lemma Psi_add (z z' : Sx M 2 → ℤ) (hz : cob 2 z = 0) (hz' : cob 2 z' = 0)
    (h : cob 2 (z + z') = 0) : Psi hM (z + z') h = Psi hM z hz + Psi hM z' hz' := by
  simp only [Psi, zhat_add z z' hz hz' h, Ext.mk₀_add, Ext.add_comp]

/-- `Psi` vanishes on coboundaries. -/
lemma Psi_cob (m : Sx M 1 → ℤ) (h : cob 2 (cob 1 m) = 0) : Psi hM (cob 1 m) h = 0 := by
  have h0 : (Ext.mk₀ (g2 M)).comp (S2_shortExact hM).extClass (zero_add 1) = 0 :=
    (S2_shortExact hM).comp_extClass
  simp only [Psi, zhat_cob, ← Ext.mk₀_comp_mk₀]
  rw [Ext.comp_assoc_of_second_deg_zero, h0, Ext.comp_zero, Ext.zero_comp]

end Psi

section PsiIso

open CategoryTheory.Abelian Stacks.SupportedVanishing MMP MMP.SingularCochain

variable [MetrizableSpace M] (hM : LocallyContractibleSpace M)

/-- On a metrizable space, `Ext^{k+1}(ℤ_M, 𝒮^p)` vanishes. -/
lemma ext_KS_subsingleton (p k : ℕ) :
    Subsingleton (Ext (constZ M) ((KS M).X p) (k + 1)) := by
  haveI : TopCat.Sheaf.IsFlasque ((KS M).X p) := singCochainSheaves_isFlasque Zc M p
  exact subsingleton_ext_of_isFlasque k _

/-- On a metrizable locally contractible space, every class in `Ext²(ℤ_M, ℤ_M)` is the class of a
singular `2`-cocycle. -/
lemma Psi_surjective (e : Ext (constZ M) (ZSh M) 2) :
    ∃ (z : Sx M 2 → ℤ) (hz : cob 2 z = 0), Psi hM z hz = e := by
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ (S1_shortExact hM) e
    (@Subsingleton.elim _ (ext_KS_subsingleton 0 1) _ _) (show 1 + 1 = 2 from rfl)
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ (S2_shortExact hM) x₃
    (@Subsingleton.elim _ (ext_KS_subsingleton 1 0) _ _) (zero_add 1)
  obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  set σ := homConstAddEquiv _ (s ≫ kernel.ι ((KS M).d 2 3)) with hσdef
  have hσ : ((KS M).d 2 3).hom.app (op ⊤) σ = 0 := by
    rw [hσdef, ← homConstAddEquiv_comp, Category.assoc, kernel.condition, Limits.comp_zero, map_zero]
  obtain ⟨g, hg, hgσ⟩ := eps_surj_cohom Zc M 2 σ hσ
  refine ⟨g, hg, ?_⟩
  have hs : zhat g hg = s := by
    rw [← cancel_mono (kernel.ι _), zhat_ι]
    apply (homConstAddEquiv _).injective
    rw [homConstAddEquiv_epsH]
    exact hgσ
  simp only [Psi, hs, hy, hx₃]

/-- On a metrizable locally contractible space, a singular `2`-cocycle with zero class in
`Ext²(ℤ_M, ℤ_M)` is a coboundary. -/
lemma exists_cob_eq_of_Psi_eq_zero (z : Sx M 2 → ℤ) (hz : cob 2 z = 0)
    (h : Psi hM z hz = 0) : ∃ m : Sx M 1 → ℤ, cob 1 m = z := by
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ (S1_shortExact hM) _
    (show 1 + 1 = 2 from rfl) h
  have h1 : (Ext.mk₀ (zhat z hz)).comp (S2_shortExact hM).extClass (zero_add 1) = 0 := by
    rw [← hx₂, @Subsingleton.elim _ (ext_KS_subsingleton 0 0) x₂ 0, Ext.zero_comp]
  obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ _ (S2_shortExact hM) _ (zero_add 1) h1
  obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective _ _).2 t
  rw [Ext.mk₀_comp_mk₀] at ht
  have ht' := (Ext.mk₀_bijective _ _).1 ht
  refine eps_inj_succ Zc M 1 z hz (homConstAddEquiv _ t) ?_
  have := congrArg (fun f => homConstAddEquiv _ (f ≫ kernel.ι ((KS M).d 2 3))) ht'
  simp only [zhat_ι, Category.assoc, g2_ι, homConstAddEquiv_comp, homConstAddEquiv_epsH] at this
  exact this.symm

/-- The coboundary `cob` agrees with the singular coboundary `coboundary`. -/
lemma cob_eq_coboundary (n : ℕ) (g : Sx M n → ℤ) : cob n g = coboundary ℤ n g := by
  funext σ
  rw [coboundary_apply]
  simp only [cob, zsmul_eq_mul, Int.cast_id]

/-- A relative `2`-cocycle relative to the empty set is a cocycle for `cob`. -/
lemma cob_of_mem_relCocycles {z : Sx M 2 → ℤ} (hz : z ∈ relCocycles ℤ (∅ : Set M) 2) :
    cob 2 z = 0 := by
  rw [cob_eq_coboundary]
  exact hz.2

/-- `Psi` on relative cocycles. -/
def PsiCoc : relCocycles ℤ (∅ : Set M) 2 →+ Ext (constZ M) (ZSh M) 2 where
  toFun z := Psi hM z.1 (cob_of_mem_relCocycles z.2)
  map_zero' := by
    have h0 : cob 2 (0 : Sx M 2 → ℤ) = 0 := by rw [cob_eq_coboundary, map_zero]
    have := Psi_add hM 0 0 h0 h0 (by rwa [add_zero])
    simp only [add_zero] at this
    exact add_eq_left.1 this.symm
  map_add' z z' := Psi_add hM z.1 z'.1 _ _ _

/-- `Psi` on relative cohomology. -/
def PsiBar : relCohomology ℤ (∅ : Set M) 2 →ₗ[ℤ] Ext (constZ M) (ZSh M) 2 :=
  ((relCoboundaries ℤ (∅ : Set M) 2).comap (relCocycles ℤ (∅ : Set M) 2).subtype).liftQ
    (PsiCoc hM).toIntLinearMap (by
      rintro ⟨z, hz⟩ hb
      obtain ⟨m, -, hm⟩ := hb
      change Psi hM z _ = 0
      subst hm
      have : coboundary ℤ 1 m = cob 1 m := (cob_eq_coboundary 1 m).symm
      revert hz
      rw [this]
      intro hz
      exact Psi_cob hM m _)

/-- `PsiBar` on the class of a cocycle `z` is `Psi` of `z`. -/
lemma PsiBar_mk (z : relCocycles ℤ (∅ : Set M) 2) :
    PsiBar hM (Submodule.Quotient.mk z) = Psi hM z.1 (cob_of_mem_relCocycles z.2) := rfl

/-- On a metrizable locally contractible space, `PsiBar` is bijective. -/
lemma PsiBar_bijective : Function.Bijective (PsiBar hM) := by
  refine ⟨?_, fun e => ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, PsiBar_mk] at hx
    obtain ⟨m, hm⟩ := exists_cob_eq_of_Psi_eq_zero hM _ _ hx
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨m, fun σ hσ => absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
      by rw [← cob_eq_coboundary, hm]; rfl⟩
  · obtain ⟨z, hz, rfl⟩ := Psi_surjective hM e
    have hz' : z ∈ relCocycles ℤ (∅ : Set M) 2 :=
      ⟨fun σ hσ => absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
        LinearMap.mem_ker.2 (by rwa [← cob_eq_coboundary])⟩
    exact ⟨Submodule.Quotient.mk ⟨z, hz'⟩, rfl⟩

/-- **The comparison isomorphism** `Ext²(ℤ_M, ℤ_M) ≃ H²_sing(M; ℤ)`. -/
def Phi : Ext (constZ M) (ZSh M) 2 ≃+ relativeSingularCohomology ℤ (.of ℤ ℤ) M ∅ 2 :=
  (LinearEquiv.ofBijective (PsiBar hM) (PsiBar_bijective hM)).symm.toAddEquiv.trans
    (relativeSingularCohomologyEquiv ℤ (∅ : Set M) 2).symm.toAddEquiv

/-- The inverse of `Phi` on the class of a cocycle `z` is `Psi` of `z`. -/
lemma Phi_symm_mk (z : relCocycles ℤ (∅ : Set M) 2) :
    (Phi hM).symm ((relativeSingularCohomologyEquiv ℤ (∅ : Set M) 2).symm
      (Submodule.Quotient.mk z)) = Psi hM z.1 (cob_of_mem_relCocycles z.2) := by
  simp [Phi, PsiBar_mk]

end PsiIso

end Comparison

end TopologicalComparison

end LogarithmFirstChern

end MMP.FourfoldProofs.LogObstructionProof

end
