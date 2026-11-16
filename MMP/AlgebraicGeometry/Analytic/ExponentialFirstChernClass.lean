module

public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CocycleFormula
public import MMP.AlgebraicGeometry.Analytic.ComplexScheme.OfProjective

/-!
# The exponential obstruction is the first Chern class

Let `X` be a projective scheme over `ℂ`, nilpotents allowed, and `A = X^an` its analytification
with its full structure sheaf. The exponential sequence `0 ⟶ ℤ_A ⟶ 𝒪_A ⟶ 𝒪_A^× ⟶ 0`,
`u ↦ exp (2πi u)`, has a connecting map which, precomposed with `Pic(A) ≃ H¹(A, 𝒪_A^×)`, is the
exponential obstruction `c_exp : Pic(A) → H²(A, ℤ_A)` (`MMP.Analytic.picardObstruction`). An
analytic invertible sheaf `L` on `A` has an underlying complex topological line bundle `E` on
`X(ℂ)`, whose continuous sections are the values of the sections of `L`. Under the natural
comparison `H²(A, ℤ_A) ≅ H²(X(ℂ); ℤ)` of constant-sheaf and singular cohomology, `c_exp(L)` is
`± c₁(E)`, with one sign `±` independent of `X` and `L`: it only records the convention for
transition functions.

## Main results

* `MMP.Analytic.exists_addEquiv_picardObstruction_eq_firstChernClass`: there are comparison
  isomorphisms `H²(X^an, ℤ) ≅ H²_sing(X^an; ℤ)`, natural for pullback along morphisms of
  projective schemes over `ℂ`, and a sign `ε = ±1`, such that `c_exp(L)` corresponds to
  `ε • c₁(E)` for every projective `X` over `ℂ`, every analytic invertible sheaf `L` on `X^an`
  and its underlying topological line bundle `E`.

## Implementation notes

* An analytic invertible sheaf is an invertible sheaf of modules `L` on the ringed space
  `MMP.Analytic.analytification sX`, and its exponential obstruction is
  `MMP.Analytic.picardObstruction` of the exponential sequence, applied to the Picard class of
  `L`. The exponential sequence is quantified over the short exact sequences
  `ℤ_A ⟶ 𝒪_A ⟶ 𝒪_A^×` with the two maps of `MMP.Analytic.exists_shortExact_exponentialSequence`:
  an integer goes to the constant section and the class of a holomorphic germ `f` to the class
  of `exp (2πi f)`; these formulas determine both maps.
* The underlying topological line bundle of `L` is characterised rather than constructed: a
  complex topological line bundle `E` on `X(ℂ)` together with a map `val` from sections of `L`
  over `V` to continuous sections of `E` over `V`, additive, compatible with restriction,
  semilinear along evaluation `𝒪_A(V) → C(V, ℂ)` of analytic functions at points, and nonzero
  at every point on some local section. This determines `E` up to isomorphism: near every point
  `val` sends a local generator of `L` to a nowhere vanishing section, and the transition functions
  of `E` in these frames are the values of those of `L`. Its first Chern class is
  `MMP.Analytic.analyticFirstChernClass`, carried from `H²(X(ℂ), ∅; ℤ)` to `H²(X(ℂ); ℤ)` by the
  identity of `X(ℂ)`.
* The comparison isomorphisms are those of the projective constant-sheaf comparison
  `MMP.Analytic.exists_addEquiv_sheafH_constantSheaf_singularCohomology`, with the same
  naturality.
* The auxiliary lemmas of the proof live in the namespace
  `MMP.Proof_lem_mmp_projective_logarithm_first_chern`, which is opened only for the main result.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace Filter
  Topology Bundle MMP MMP.Analytic MMP.Analytic.ComplexPoints MMP.Analytic.Analytification

attribute [local instance] hasExt_of_enoughInjectives
  Stacks.Cohomology.Generators.picardGroupAddCommGroup
attribute [local implicit_reducible] TopCat.Sheaf

universe u

namespace MMP.Proof_lem_mmp_projective_logarithm_first_chern

/-! ### The extension class of the first step of an injective resolution -/

section ExtClassResolution

open CochainComplex HomComplex DerivedCategory Pretriangulated

variable {C : Type*} [Category C] [Abelian C] [HasExt C]

/-- Let `I` be an injective resolution of `A` and `0 ⟶ A ⟶ I⁰ ⟶ Z ⟶ 0` a short exact sequence
whose first map is the augmentation, and let `j : Z ⟶ I¹` factor the first differential. Then the
extension class of the sequence is the class of the cocycle `-j`. -/
private theorem extClass_eq_extMk {A Z : C} (I : InjectiveResolution A) (g : I.cocomplex.X 0 ⟶ Z)
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
private theorem edgePhase_change {e e' : Trivialization ℂ (Bundle.TotalSpace.proj : TotalSpace ℂ E → B)}
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
private noncomputable def vertexLog (e : Trivialization ℂ (π ℂ E)) : Simplex B 0 → ℂ :=
  fun ρ => log (vertexCoord (E := E) e (ρ (stdSimplex.vertex 0)))

/-- The first face of a `1`-simplex starts at its second vertex. -/
private lemma face00_vertex : (face 0 0) (stdSimplex.vertex 0) =
    (stdSimplex.vertex 1 : stdSimplex ℝ (Fin 2)) := by
  simp [face, stdSimplex.map_vertex]

/-- The second face of a `1`-simplex starts at its first vertex. -/
private lemma face01_vertex : (face 0 1) (stdSimplex.vertex 0) =
    (stdSimplex.vertex 0 : stdSimplex ℝ (Fin 2)) := by
  simp [face, stdSimplex.map_vertex]

private lemma coboundary_vertexLog (e : Trivialization ℂ (π ℂ E)) (τ : Simplex B 1) :
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
private lemma exists_obstructionCocycle_eq_coboundary (e : Trivialization ℂ (π ℂ E))
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
private noncomputable def frameCoord (e : Trivialization ℂ (π ℂ E)) (U : Opens B)
    (f : ∀ y : U, E y) (y : B) : ℂ := by
  classical
  exact if hy : y ∈ U then (e ⟨y, f ⟨y, hy⟩⟩).2 else 0

private lemma frameCoord_of_mem (e : Trivialization ℂ (π ℂ E)) (U : Opens B)
    (f : ∀ y : U, E y) {y : B} (hy : y ∈ U) : frameCoord e U f y = (e ⟨y, f ⟨y, hy⟩⟩).2 := by
  simp [frameCoord, hy]

/-- **A continuous section with nonzero value has, near the point, a coordinate with a
continuous logarithm.** -/
private lemma exists_frameCoord_log (e : Trivialization ℂ (π ℂ E)) [MemTrivializationAtlas e]
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
    have := (e.continuousLinearEquivAt ℂ x hxe).injective
      (a₁ := f ⟨x, hxU⟩) (a₂ := 0) (by
        rw [map_zero, Trivialization.continuousLinearEquivAt_apply]
        exact h)
    exact this
  set c₀ := frameCoord e U f x
  have hball : IsOpen (Metric.ball c₀ ‖c₀‖) := Metric.isOpen_ball
  obtain ⟨W, hWo, hW⟩ := (continuousOn_iff'.1 hcont) _ hball
  refine ⟨⟨S ∩ W, hSo.inter hWo⟩, ⟨⟨hxU, hxe⟩, ?_⟩, fun y hy => hy.1.1, fun y hy => hy.1.2, ?_⟩
  · have : x ∈ frameCoord e U f ⁻¹' Metric.ball c₀ ‖c₀‖ ∩ S :=
      ⟨by change dist c₀ c₀ < ‖c₀‖; rw [dist_self]; exact norm_pos_iff.2 hx0, hxU, hxe⟩
    rw [hW] at this
    exact this.1
  · have hmem : ∀ y ∈ S ∩ W, frameCoord e U f y / c₀ ∈ slitPlane := by
      intro y hy
      have hyb : frameCoord e U f y ∈ Metric.ball c₀ ‖c₀‖ := by
        have : y ∈ W ∩ S := ⟨hy.2, hy.1⟩
        rw [← hW] at this
        exact this.1
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
private lemma coord_eq_mul_transition {ei ej : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas ei]
    [MemTrivializationAtlas ej] {z : B} (hz : z ∈ ei.baseSet ∩ ej.baseSet) (v : E z) :
    (ej ⟨z, v⟩).2 = (ei ⟨z, v⟩).2 * transition ei ej z := by
  rw [← coordChangeL_eq_mul_transition hz, Trivialization.coordChangeL_apply ei ej hz,
    Trivialization.symm_apply_apply_mk ei hz.1]

/-- The coordinate of a scalar multiple. -/
private lemma coord_smul (e : Trivialization ℂ (π ℂ E)) [MemTrivializationAtlas e] {z : B}
    (hz : z ∈ e.baseSet) (c : ℂ) (v : E z) : (e ⟨z, c • v⟩).2 = c * (e ⟨z, v⟩).2 :=
  (e.linear ℂ hz).map_smul c v

/-- **The local primitive of the difference of two edge-phase cochains.** Two frames `fᵢ`, `fⱼ`
related by `fⱼ = exp (2πi φ) • fᵢ`, with continuous logarithms `Lᵢ`, `Lⱼ` of their coordinates,
give on the overlap an integer function `a` whose coboundary is the difference of the integer
cochains `wⱼ - wᵢ` of `exists_obstructionCocycle_eq_coboundary`, and whose value is
`(Lⱼ - log vⱼ)/2πi - (Lᵢ - log vᵢ)/2πi - φ`. -/
private lemma exists_int_primitive {ei ej : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas ei]
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
  -- the continuous logarithm of the transition function on `V`
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
  -- the value is an integer
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
private noncomputable def funPresheaf : TopCat.Presheaf AddCommGrpCat.{0} M where
  obj V := AddCommGrpCat.of (V.unop → A)
  map i := AddCommGrpCat.ofHom
    { toFun := fun f x => f ⟨x.1, i.unop.le x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The sheaf of all `A`-valued functions. -/
private noncomputable def funSheaf : Sheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0} where
  obj := funPresheaf M A
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)]
    exact TopCat.Presheaf.isSheaf_of_iso (NatIso.ofComponents (fun V => Iso.refl _) (fun _ => rfl))
      (TopCat.Presheaf.toTypes_isSheaf M (fun _ => A))

/-- The constant sheaf `ℤ_M` of the statement. -/
private noncomputable abbrev ZSh : Sheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0} :=
  (constantSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).obj (.of ℤ)

/-- The integers as constant functions on `M`. -/
private noncomputable def constGlobal : AddCommGrpCat.of ℤ ⟶ (funSheaf M ℂ).obj.obj (op ⊤) :=
  AddCommGrpCat.ofHom
      { toFun := fun n (_ : (⊤ : Opens M)) => (n : ℂ)
        map_zero' := by funext; simp
        map_add' := fun _ _ => by funext; simp }

/-- The inclusion `ℤ_M ⟶ ℂ^M` of the integers into all complex functions. -/
private noncomputable def constFun : ZSh M ⟶ funSheaf M ℂ :=
  ((constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{0} isTerminalTop).homEquiv
    _ _).symm (constGlobal M)

private theorem constFun_mono : Mono (constFun M) := by
  let J := Opens.grothendieckTopology M
  let adj1 := constantPresheafAdj AddCommGrpCat.{0} (isTerminalTop : IsTerminal (⊤ : Opens M))
  let adj2 := sheafificationAdjunction J AddCommGrpCat.{0}
  let c : (Functor.const (Opens M)ᵒᵖ).obj (AddCommGrpCat.of ℤ) ⟶ (funSheaf M ℂ).obj :=
    (adj1.homEquiv (AddCommGrpCat.of ℤ) (funSheaf M ℂ).obj).symm (constGlobal M)
  have hc : constFun M = (adj2.homEquiv _ _).symm c := by
    have := congrArg (fun F => (F (AddCommGrpCat.of ℤ) (funSheaf M ℂ)).symm (constGlobal M))
      (Adjunction.comp_homEquiv adj1 adj2)
    exact this
  have hfac : toSheafify J _ ≫ (constFun M).hom = c := by
    rw [hc]
    have := adj2.homEquiv_unit (f := (adj2.homEquiv _ (funSheaf M ℂ)).symm c)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have hcapp : ∀ (U : (Opens M)ᵒᵖ) (n : ℤ) (y : U.unop), (c.app U n : U.unop → ℂ) y = n := by
    intro U n y
    rfl
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
private noncomputable abbrev quotSheaf : Sheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0} :=
  cokernel (constFun M)

/-- The short exact sequence `0 ⟶ ℤ_M ⟶ ℂ^M ⟶ ℂ^M / ℤ_M ⟶ 0`. -/
private theorem quotSeq_shortExact :
    (ShortComplex.mk (constFun M) (cokernel.π (constFun M)) (cokernel.condition _)).ShortExact :=
  haveI := constFun_mono M
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

end FunSheaf

section Residue

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- The residue `𝒪_{U,y} → ℂ` at a `ℂ`-point `y` of a chart: the value at `z(y)`. -/
private noncomputable def residue (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U) :
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

private lemma residue_mk (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    (g : holGerms (c.coords y)) :
    residue c y (Chart.StalkRing.mk c _ g) = Germ.value (g : Germ (𝓝 (c.coords y)) ℂ) :=
  Ideal.Quotient.lift_mk _ _ _

private lemma exists_gens [LocallyOfFiniteType sX] {U : X.Opens} (hU : IsAffineOpen U) :
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
private lemma exists_chart [LocallyOfFiniteType sX] (x : space sX) :
    ∃ c : Chart sX, x ∈ ComplexPoints.chart c.U := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (Opens.mem_top (ComplexPoints.toScheme x))
  obtain ⟨n, gen, h⟩ := exists_gens (sX := sX) hU
  exact ⟨⟨U, hU, n, gen, h⟩, ComplexPoints.mem_chart_iff.2 hxU⟩

variable {n : ℕ}

private lemma exists_rep {p : Fin n → ℂ} (g : holGerms p) :
    ∃ f : (Fin n → ℂ) → ℂ, (g : Germ (𝓝 p) ℂ) = f ∧ ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y := by
  obtain ⟨f, hf, hd⟩ := g.2
  exact ⟨f, hf.symm, hd⟩

private lemma mk_surjective (c : Chart sX) (p : Fin c.n → ℂ) (a : c.StalkRing p) :
    ∃ g, Chart.StalkRing.mk c p g = a :=
  Ideal.Quotient.mk_surjective a

private lemma residue_of_eq_mk (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    {a : c.StalkRing (c.coords y)} {g : holGerms (c.coords y)} {f : (Fin c.n → ℂ) → ℂ}
    (ha : a = Chart.StalkRing.mk c _ g) (hg : (g : Germ (𝓝 (c.coords y)) ℂ) = f) :
    residue c y a = f (c.coords y) := by
  rw [ha, residue_mk, hg]
  rfl

private lemma eventually_differentiableAt_of_coe_eq {p : Fin n → ℂ} (g : holGerms p)
    {f : (Fin n → ℂ) → ℂ} (hf : (g : Germ (𝓝 p) ℂ) = f) :
    ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y := by
  obtain ⟨f', hf', hd⟩ := exists_rep g
  have heq : f' =ᶠ[𝓝 p] f := Germ.coe_eq.1 (hf'.symm.trans hf)
  exact (hd.and heq.eventuallyEq_nhds).mono fun y hy => hy.1.congr_of_eventuallyEq hy.2.symm

private lemma residue_transition {c d : Chart sX} (m : ChartHom c d)
    (y : ComplexPoints.chart (sX := sX) d.U) (a : c.StalkRing (c.coords (m.incl y))) :
    residue d y (m.transition y a) = residue c (m.incl y) a := by
  obtain ⟨g, rfl⟩ := mk_surjective c _ a
  obtain ⟨f, hf, -⟩ := exists_rep g
  rw [m.transition_mk, residue_mk, residue_mk, coe_holPullback, hf, Germ.coe_compTendsto]
  change f (m.polyMap (d.coords y)) = f (c.coords (m.incl y))
  rw [m.coords_incl]

private lemma exists_chartHom_chartHom [LocallyOfFiniteType sX] (c d : Chart sX)
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
private lemma residue_eq_of_isCompatible [LocallyOfFiniteType sX] {W : Opens (space sX)}
    {s : ∀ x : W, Fibre x.1} (hs : IsCompatible s) (x : W) (c d : Chart sX)
    (hc : x.1 ∈ ComplexPoints.chart c.U) (hd : x.1 ∈ ComplexPoints.chart d.U) :
    residue c ⟨x.1, hc⟩ (s x ⟨c, hc⟩) = residue d ⟨x.1, hd⟩ (s x ⟨d, hd⟩) := by
  obtain ⟨e, m₁, m₂, he⟩ := exists_chartHom_chartHom c d hc hd
  exact ((residue_transition m₁ ⟨x.1, he⟩ _).symm.trans (congrArg _ (hs c e m₁ x he))).trans
    ((congrArg _ (hs d e m₂ x he)).symm.trans (residue_transition m₂ ⟨x.1, he⟩ _))

/-- The `ℂ`-points of an open `U` at which the value of a section `f ∈ Γ(X, U)` lies in an open
set form an open subset of `X(ℂ)`. -/
private lemma isOpen_setOf_evalHom_mem (U : X.Opens) (f : Γ(X, U)) {T : Set ℂ}
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
    exact ⟨hy, by rw [Set.mem_preimage, ← hyv]; exact hyT⟩

/-- A subset of the `ℂ`-points of an affine open, open for its chart topology, is open in
`X(ℂ)`. -/
private lemma isOpen_setOf_mem_chart (U : X.affineOpens)
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
private lemma exists_opens_of_mem_chart (c : Chart sX)
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
private lemma exists_opens_residue_mem [LocallyOfFiniteType sX] {W : Opens (space sX)}
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
private noncomputable def pointChart (x : space sX) : {c : Chart sX // x ∈ ComplexPoints.chart c.U} :=
  ⟨(exists_chart x).choose, (exists_chart x).choose_spec⟩

/-- The value at a point of a section of `𝒪_{X^an}`: the residue of its component in
`pointChart`. -/
private noncomputable def sectionValue {W : Opens (space sX)} (s : (structureSheaf sX).obj.obj (op W))
    (x : W) : ℂ :=
  residue (pointChart sX x.1).1 ⟨x.1, (pointChart sX x.1).2⟩ (s.1 x (pointChart sX x.1))

private lemma sectionValue_eq {W : Opens (space sX)} (s : (structureSheaf sX).obj.obj (op W))
    (x : W) (g : holGerms ((pointChart sX x.1).1.coords ⟨x.1, (pointChart sX x.1).2⟩))
    (hs : s.1 x (pointChart sX x.1) = Chart.StalkRing.mk _ _ g) :
    sectionValue sX s x =
      Germ.value (g : Germ (𝓝 ((pointChart sX x.1).1.coords ⟨x.1, (pointChart sX x.1).2⟩)) ℂ) := by
  rw [sectionValue, hs, residue_mk]

/-- Values of sections of `𝒪_{X^an}` are continuous functions. -/
private lemma continuous_sectionValue {W : Opens (space sX)}
    (s : (structureSheaf sX).obj.obj (op W)) : Continuous (sectionValue sX s) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Filter.tendsto_def]
  intro N hN
  obtain ⟨V, hxV, hV⟩ := exists_opens_residue_mem s x (pointChart sX x.1).1 (pointChart sX x.1).2
    (N := N) (by rw [← sectionValue]; exact hN)
  refine Filter.mem_of_superset ((V.isOpen.preimage continuous_subtype_val).mem_nhds hxV) ?_
  intro y hy
  exact hV y hy _ _

end Residue

section ValueMap

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]

/-- Evaluation `𝒪_{X^an} ⟶ ℂ^{X(ℂ)}` of sections at points. -/
private noncomputable def valueMap :
    (sheafCompose (Opens.grothendieckTopology (space sX)) (forget₂ RingCat AddCommGrpCat)).obj
      (ringCatSheaf sX) ⟶ funSheaf (space sX) ℂ where
  hom :=
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun s x => sectionValue sX (show (structureSheaf sX).obj.obj W from s) x
          map_zero' := by funext x; simp [sectionValue]; rfl
          map_add' := fun s t => by funext x; simp only [sectionValue]; exact map_add _ _ _ }
      naturality := fun W W' i => rfl }

private lemma sectionValue_intCast {W : Opens (space sX)} (n : ℤ) (x : W) :
    sectionValue sX ((n : ℤ) : (structureSheaf sX).obj.obj (op W)) x = n := by
  simp only [sectionValue]
  have : (n : (structureSheaf sX).obj.obj (op W)).1 x (pointChart sX x.1) =
      (n : (pointChart sX x.1).1.StalkRing _) := rfl
  rw [this, map_intCast]

/-- The exponential sequence's first map followed by evaluation is the inclusion of the constant
integer functions. -/
private lemma comp_valueMap_eq_constFun
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
private abbrev unitVal {W : Opens (space sX)}
    (u : (Stacks.Cohomology.Generators.unitsSheaf (analytification sX)).obj.obj (op W)) :
    (structureSheaf sX).obj.obj (op W) :=
  ((Additive.toMul u : ((structureSheaf sX).obj.obj (op W))ˣ) : (structureSheaf sX).obj.obj (op W))

/-- The value of `exp (2πi f)` is `exp (2πi)` of the value of `f`. -/
private lemma sectionValue_exp
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
private lemma exists_local_log_lam
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
private theorem exists_unitsLog
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
private lemma exists_generator_ne_zero (L : SheafOfModules (ringCatSheaf sX))
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
private lemma val_act_eq (L : SheafOfModules (ringCatSheaf sX))
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

/-- `sheafCohomologyOneExtEquiv` is the composite of its two defining isomorphisms. -/
private theorem sheafCohomologyOneExtEquiv_hom_apply {Y : TopCat.{0}}
    (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0})
    (x : Stacks.Cohomology.SheafTorsor.sheafCohomologyOne Y F) :
    (Stacks.Thickenings.sheafCohomologyOneExtEquiv Y F).hom x =
      (ModuleSheafCohomology.rightDerivedCoyonedaSuccIso
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (ULift.{0, 0} ℤ))) 0).hom.app F
        ((ModuleSheafCohomology.rightDerivedIso
          (Stacks.Thickenings.sectionsCoyonedaIso Y).symm 1).hom.app F x) := by
  unfold Stacks.Thickenings.sheafCohomologyOneExtEquiv
  exact ConcreteCategory.comp_apply _ _ x

/-- Postcomposition with `Ext.mk₀ f` is the map of `extFunctorObj` on `f`. -/
private theorem ext_comp_mk₀_eq_extFunctorObj_map {Y : TopCat.{0}}
    {F G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}} (f : F ⟶ G)
    (y : Sheaf.H.{0} F 1) :
    y.comp (Ext.mk₀ f) (add_zero 1) = ((extFunctorObj
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift.{0, 0} ℤ))) (0 + 1)).map f) y := rfl

/-- `sheafCohomologyOneExtEquiv` is natural in the sheaf. -/
private theorem sheafCohomologyOneExtEquiv_naturality {Y : TopCat.{0}}
    {F G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}} (f : F ⟶ G)
    (x : Stacks.Cohomology.SheafTorsor.sheafCohomologyOne Y F) :
    ((Stacks.Thickenings.sheafCohomologyOneExtEquiv Y F).hom x).comp (Ext.mk₀ f) (add_zero 1) =
      (Stacks.Thickenings.sheafCohomologyOneExtEquiv Y G).hom
        ((((sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj
          (op ⊤)).rightDerived 1).map f x) := by
  have key := ((ModuleSheafCohomology.rightDerivedIso
    (Stacks.Thickenings.sectionsCoyonedaIso Y).symm 1).hom ≫
      (ModuleSheafCohomology.rightDerivedCoyonedaSuccIso
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (ULift.{0, 0} ℤ))) 0).hom).naturality f
  refine (congrArg (fun y ↦ y.comp (Ext.mk₀ f) (add_zero 1))
    (sheafCohomologyOneExtEquiv_hom_apply F x)).trans ?_
  refine (ext_comp_mk₀_eq_extFunctorObj_map f _).trans ?_
  refine (ConcreteCategory.congr_hom key x).symm.trans ?_
  exact (sheafCohomologyOneExtEquiv_hom_apply G _).symm

/-- The obstruction map on the class of an invertible module: the first cohomology class of its
torsor of local generators, composed with the extension class of the sequence. -/
private theorem picardObstruction_classOf (A : RingedSpace.{0})
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
private theorem rightDerived_map_torsorClass_eq_neg {X : TopCat.{0}}
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
private def IsKappaCocycle {M : TopCat.{0}} {I : Type} (Ui : I → Opens M) (w : I → Simplex M 1 → ℤ)
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
private noncomputable def quotExtClass (M : TopCat.{0}) {I : Type} (Ui : I → Opens M)
    (hUi : (⊤ : Opens M) = ⨆ i, Ui i) (c : CechCochains.cocycles1 Ui (quotSheaf M).obj) :
    Sheaf.H.{0} (ZSh M) 2 :=
  ((Stacks.Thickenings.sheafCohomologyOneExtEquiv M (quotSheaf M)).hom
    (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections M ⊤ Ui hUi (quotSheaf M)
      (CechCochains.cls Ui (quotSheaf M).obj c))).comp
    (quotSeq_shortExact M).extClass (show 1 + 1 = 2 from rfl)

section TopologicalComparison

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology Metric

universe u' v'

noncomputable section

private abbrev singChains (X : TopCat.{u}) : ChainComplex AddCommGrpCat.{u} ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).obj X

section CochainBridge

open scoped Simplicial

/-- The value of an `A`-valued cochain on a singular simplex. -/
private def cochainEval (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ)
    (φ : (singChains X).X n ⟶ A) (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) : A :=
  (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ φ).hom ⟨1⟩

private def cochainOfFun (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ)
    (g : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → A) : (singChains X).X n ⟶ A :=
  Sigma.desc fun σ ↦ AddCommGrpCat.ofHom
    { toFun := fun k ↦ k.down • g σ
      map_zero' := by simp
      map_add' := fun a b ↦ by simp [add_smul] }

private def cochainEquiv (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ) :
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

private lemma hom_sum' {M N : AddCommGrpCat.{u}} {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (x :
    M) :
    (∑ i ∈ s, f i).hom x = ∑ i ∈ s, (f i).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add]; simp
      [ih]

@[reassoc]
private lemma ι_singChains_d (X : TopCat.{u}) (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
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

private lemma cochainEval_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ)
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

private lemma cochainEval_map (A : AddCommGrpCat.{u}) {X Y : TopCat.{u}} (f : Y ⟶ X) (n : ℕ)
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
private abbrev pt : TopCat.{u} := TopCat.of PUnit.{u + 1}

open scoped Simplicial in
private instance (n : ℕ) : Unique ((TopCat.toSSet.obj pt).obj (op ⦋n⦌)) :=
  haveI : Unique C(Convexity.StdSimplex ℝ (Fin ((op ⦋n⦌).unop.len + 1)), (pt : Type u)) :=
    ⟨⟨⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext x⟩
  (TopCat.toSSetObjEquiv pt (op ⦋n⦌)).unique

open scoped Simplicial in
private lemma pt_eval_d (A : AddCommGrpCat.{u}) (m : ℕ) (φ : (singChains pt).X m ⟶ A) :
    cochainEval A pt (m + 1) ((singChains pt).d (m + 1) m ≫ φ) default =
      (if m % 2 = 0 then (0 : ℤ) else 1) • cochainEval A pt m φ default := by
  have hs : ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) = if m % 2 = 0 then 0 else 1 := by
    rw [Fin.sum_neg_one_pow]; simp [Nat.even_add_one, Nat.even_iff]
  rw [cochainEval_d, ← hs, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subsingleton.elim ((TopCat.toSSet.obj pt).δ i default) default]

private lemma cochainEval_injective (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ) :
    Function.Injective (cochainEval A X n) := (cochainEquiv A X n).injective

/-- The cohomology of a point vanishes in positive degrees. -/
private lemma pt_coboundary (A : AddCommGrpCat.{u}) (n : ℕ) (z : (singChains pt).X (n + 1) ⟶ A)
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
private abbrev chainMap {Z Y : TopCat.{u}} (i : Z ⟶ Y) :=
  ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map i

private lemma nullhomotopic_coboundary (A : AddCommGrpCat.{u}) {Z Y : TopCat.{u}} (i : Z ⟶ Y)
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

private lemma nullhomotopic_const (A : AddCommGrpCat.{u}) {Z Y : TopCat.{u}} (i : Z ⟶ Y)
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
private def singCochainPresheaf (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    (Opens X)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  (Opens.toTopCat X).op ⋙
    ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).op ⋙
      HomologicalComplex.opFunctor _ _ ⋙ (preadditiveYoneda.obj A).mapHomologicalComplex _

private lemma exists_open_nullhomotopic {X : TopCat.{u}} (hX : LocallyContractibleSpace X) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧
      ContinuousMap.Nullhomotopic ((Opens.toTopCat X).map (homOfLE h)).hom := by
  obtain ⟨V, hVU, hV, hnull⟩ := hX x (U : Set X) (U.isOpen.mem_nhds hx)
  refine ⟨⟨interior V, isOpen_interior⟩, (interior_subset.trans hVU), mem_interior_iff_mem_nhds.2
      hV, ?_⟩
  have := hnull.comp_left (ContinuousMap.inclusion (interior_subset : interior V ⊆ V))
  exact this

private lemma restrict_coboundary {X : TopCat.{u}} (A : AddCommGrpCat.{u}) (hX :
    LocallyContractibleSpace X)
    (x : X) (U : Opens X) (hx : x ∈ U) (n : ℕ)
    (z : ((singCochainPresheaf A X).obj (op U)).X (n + 1))
    (hz : ((singCochainPresheaf A X).obj (op U)).d (n + 1) (n + 2) z = 0) :
    ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ ∃ b : ((singCochainPresheaf A X).obj (op V)).X n,
      ((singCochainPresheaf A X).map (homOfLE h).op).f (n + 1) z =
        ((singCochainPresheaf A X).obj (op V)).d n (n + 1) b := by
  obtain ⟨V, h, hxV, hnull⟩ := exists_open_nullhomotopic hX x U hx
  obtain ⟨b, hb⟩ := nullhomotopic_coboundary A ((Opens.toTopCat X).map (homOfLE h)) hnull n z hz
  exact ⟨V, h, hxV, b, hb⟩

private lemma restrict_const {X : TopCat.{u}} (A : AddCommGrpCat.{u}) (hX : LocallyContractibleSpace
    X)
    (x : X) (U : Opens X) (hx : x ∈ U)
    (z : ((singCochainPresheaf A X).obj (op U)).X 0)
    (hz : ((singCochainPresheaf A X).obj (op U)).d 0 1 z = 0) :
    ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ ∃ a : A, ∀ σ,
      cochainEval A (Opens.toTopCat X |>.obj V) 0
        (((singCochainPresheaf A X).map (homOfLE h).op).f 0 z) σ = a := by
  obtain ⟨V, h, hxV, hnull⟩ := exists_open_nullhomotopic hX x U hx
  obtain ⟨a, ha⟩ := nullhomotopic_const A ((Opens.toTopCat X).map (homOfLE h)) hnull z hz
  exact ⟨V, h, hxV, a, ha⟩

/-- The `p`-th term of the presheaf complex of singular cochains, `U ↦ Hom(C_p(U; ℤ), A)`. -/
private def singCochainTerm (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) :
    TopCat.Presheaf AddCommGrpCat.{u} X :=
  singCochainPresheaf A X ⋙ HomologicalComplex.eval _ _ p

private def singCochainTermD (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) :
    singCochainTerm A X p ⟶ singCochainTerm A X (p + 1) where
  app U := ((singCochainPresheaf A X).obj U).d p (p + 1)
  naturality _ _ i := ((singCochainPresheaf A X).map i).comm p (p + 1)

/-- The complex of presheaves of singular cochains. -/
private def singCochainPresheafComplex (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℕ :=
  CochainComplex.of (singCochainTerm A X) (singCochainTermD A X) (fun p => by
    refine NatTrans.ext (funext fun U => ?_)
    exact ((singCochainPresheaf A X).obj U).d_comp_d p (p + 1) (p + 2))

/-- The complex of sheafified singular cochains `𝒮^•`. -/
private def singCochainSheaves (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
    (singCochainPresheafComplex A X)

section SheafifyStalks

variable {X : TopCat.{u}}

/-- the sheafified complex -/
private abbrev sheafifyComplex (P : CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex _).obj P

/-- the sheafification as a `TopCat.Sheaf` -/
private abbrev sheafify (F : TopCat.Presheaf AddCommGrpCat.{u} X) : TopCat.Sheaf AddCommGrpCat.{u}
    X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj F

/-- stalk comparison -/
private def stalkTau (x : X) (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    F.stalk x ⟶ (sheafify F).presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.app F)

private instance (x : X) (F : TopCat.Presheaf AddCommGrpCat.{u} X) : IsIso (stalkTau x F) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ F

private lemma stalkTau_bijective (x : X) (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    Function.Bijective (stalkTau x F) :=
  (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

private lemma stalkTau_naturality (x : X) {F G : TopCat.Presheaf AddCommGrpCat.{u} X} (η : F ⟶ G) :
    stalkTau x F ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map η).hom =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η ≫ stalkTau x G := by
  unfold stalkTau
  have hnat := (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).unit.naturality η
  exact (Functor.map_comp (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) _ _).symm.trans
    ((congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map hnat.symm).trans
      (Functor.map_comp (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) _ _))

private lemma exactAt_sheafifyComplex (P : CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℕ)
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
private theorem singCochainSheaves_exactAt (A : AddCommGrpCat.{u}) (X : TopCat.{u})
    (hX : LocallyContractibleSpace X) (n : ℕ) : (singCochainSheaves A X).ExactAt (n + 1) :=
  exactAt_sheafifyComplex (singCochainPresheafComplex A X) n (fun U x hx z hz => by
    have hz' : ((singCochainPresheaf A X).obj (op U)).d (n + 1) (n + 2) z = 0 := by
      have e : (singCochainPresheafComplex A X).d (n + 1) (n + 2) = singCochainTermD A X (n + 1) :=
        CochainComplex.of_d _ _ _
      rw [e] at hz
      exact hz
    obtain ⟨V, h, hxV, b, hb⟩ := restrict_coboundary A hX x U hx n z hz'
    refine ⟨V, h, hxV, b, ?_⟩
    have e : (singCochainPresheafComplex A X).d n (n + 1) = singCochainTermD A X n :=
      CochainComplex.of_d _ _ _
    rw [e]
    exact hb)

section ConstantAugmentation

open scoped Simplicial

/-- The constant `0`-cochain with value `a`. -/
private def constCochain (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (a : A) : (singChains Y).X 0 ⟶
    A :=
  cochainOfFun A Y 0 (fun _ => a)

private lemma cochainEval_constCochain (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (a : A)
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋0⦌)) : cochainEval A Y 0 (constCochain A Y a) σ = a :=
  congrFun ((cochainEquiv A Y 0).right_inv (fun _ => a)) σ

private lemma cochainEval_add (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (n : ℕ)
    (φ ψ : (singChains Y).X n ⟶ A) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    cochainEval A Y n (φ + ψ) σ = cochainEval A Y n φ σ + cochainEval A Y n ψ σ := by
  unfold cochainEval
  rfl

/-- The augmentation of the constant presheaf into the `0`-cochains: `a ↦ (σ ↦ a)`. -/
private def constToCochain (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
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

private lemma constToCochain_comp_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
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
private abbrev constSheaf (A : AddCommGrpCat.{u}) (X : TopCat.{u}) : TopCat.Sheaf AddCommGrpCat.{u}
    X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A

/-- The augmentation `A_X ⟶ 𝒮^0`, as the sheafification of `constToCochain`. -/
private def constAugDeg0 (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    constSheaf A X ⟶ (singCochainSheaves A X).X 0 :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (constToCochain A X)

private lemma constAugDeg0_comp_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
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
private theorem exact_constAugDeg0 (A : AddCommGrpCat.{u}) (X : TopCat.{u})
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
  obtain ⟨V, hV, hxV, a, ha⟩ := restrict_const A hX x W hxW
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

private theorem mono_constAugDeg0 (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
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
       constCochain A _ a :=
     hn.symm.trans (by rfl)
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
private abbrev evalA {n : ℕ} (φ : Simplex Y n → M) : Chain ℤ Y n →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ φ

/-- coboundary of `M`-valued cochains -/
private def cob (n : ℕ) (φ : Simplex Y n → M) : Simplex Y (n + 1) → M :=
  fun σ => ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (σ.comp (face n i))

private lemma evalA_single {n : ℕ} (φ : Simplex Y n → M) (σ : Simplex Y n) :
    evalA φ (single σ 1) = φ σ := by simp

private lemma evalA_bd (n : ℕ) (φ : Simplex Y n → M) (c : Chain ℤ Y (n + 1)) :
    evalA φ (bd ℤ n c) = evalA (cob n φ) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, bd_single,
      map_sum]
    simp [cob]

private lemma evalA_eq_zero_of_mem_small {n : ℕ} {𝒰 : Set (Set Y)} {φ : Simplex Y n → M}
    (h : ∀ σ : Simplex Y n, (∃ U ∈ 𝒰, range σ ⊆ U) → φ σ = 0) {c : Chain ℤ Y n}
    (hc : c ∈ small ℤ n 𝒰) : evalA φ c = 0 := by
  have hc' := (mem_supported ℤ c).1 hc
  rw [Finsupp.linearCombination_apply]
  exact Finset.sum_eq_zero fun σ hσ => by show c σ • φ σ = 0; rw [h σ (hc' hσ), smul_zero]

private lemma smallIndex_eq_zero {𝒰 : Set (Set Y)} (n : ℕ) :
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

private lemma smallHomotopy_eq_zero {𝒰 : Set (Set Y)} (n : ℕ) (σ : Simplex Y n)
    (hσ : ∃ U ∈ 𝒰, range σ ⊆ U) : smallHomotopy ℤ 𝒰 n (single σ 1) = 0 := by
  rw [smallHomotopy_single, smallIndex_eq_zero n σ hσ]
  simp [homotopyUpTo]

private lemma evalA_smallHomotopy_pull {𝒰 : Set (Set Y)} (n : ℕ) (φ : Simplex Y (n + 1) → M)
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
private theorem exists_cob_eq_of_small {𝒰 : Set (Set Y)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U)
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

private abbrev Sx (Y : Type u) [TopologicalSpace Y] (n : ℕ) :=
    MMP.SingularChain.Simplex Y n

private def fnEquiv (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (n : ℕ) :
    ((singChains Y).X n ⟶ A) ≃ (Sx Y n → A) :=
  (cochainEquiv A Y n).trans
    (Equiv.arrowCongr (MMP.SingularCochain.simplexEquiv Y n) (Equiv.refl _))

private lemma fnEquiv_apply (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (n : ℕ)
    (φ : (singChains Y).X n ⟶ A) (τ : Sx Y n) :
    fnEquiv A Y n φ τ = cochainEval A Y n φ ((MMP.SingularCochain.simplexEquiv Y
        n).symm τ) :=
  rfl

private lemma fnEquiv_map (A : AddCommGrpCat.{u}) {Y Z : TopCat.{u}} (f : Z ⟶ Y) (n : ℕ)
    (φ : (singChains Y).X n ⟶ A) (τ : Sx Z n) :
    fnEquiv A Z n ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))).map f).f n ≫ φ) τ = fnEquiv A Y n φ (f.hom.comp τ) := by
  rw [fnEquiv_apply, fnEquiv_apply, cochainEval_map]
  rfl

end CochainModel

section CochainModel2

variable (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ)

private def openVal (V : Opens X) : C(↥V, X) := ⟨Subtype.val, continuous_subtype_val⟩

private def reprFn (V : Opens X) (g : Sx X p → A) : (singCochainTerm A X p).obj (op V) :=
  (fnEquiv A ((Opens.toTopCat X).obj V) p).symm (fun τ => g ((openVal X V).comp τ))

private lemma fnEquiv_res {V W : Opens X} (h : W ≤ V) (φ : (singCochainTerm A X p).obj (op V))
    (τ : Sx ((Opens.toTopCat X).obj W) p) :
    fnEquiv A ((Opens.toTopCat X).obj W) p ((singCochainTerm A X p).map (homOfLE h).op φ) τ =
      fnEquiv A ((Opens.toTopCat X).obj V) p φ (((Opens.toTopCat X).map (homOfLE h)).hom.comp τ) :=
  fnEquiv_map A ((Opens.toTopCat X).map (homOfLE h)) p φ τ

private lemma reprFn_res {V W : Opens X} (h : W ≤ V) (g : Sx X p → A) :
    (singCochainTerm A X p).map (homOfLE h).op (reprFn A X p V g) = reprFn A X p W g := by
  apply (fnEquiv A ((Opens.toTopCat X).obj W) p).injective
  funext τ
  rw [fnEquiv_res]
  simp only [reprFn, Equiv.apply_symm_apply]
  rfl

private def liftOpen (V : Opens X) (σ : Sx X p) (h : Set.range σ ⊆ V) :
    Sx ((Opens.toTopCat X).obj V) p :=
  ⟨fun t => ⟨σ t, h ⟨t, rfl⟩⟩, σ.continuous.subtype_mk _⟩

private lemma liftOpen_openVal_comp (V : Opens X) (τ : Sx ((Opens.toTopCat X).obj V) p)
    (h : Set.range ((openVal X V).comp τ) ⊆ V) :
    liftOpen X p V ((openVal X V).comp τ) h = τ := by ext; rfl

private lemma reprFn_surj (V : Opens X) (φ : (singCochainTerm A X p).obj (op V)) :
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

private lemma reprFn_eq (V : Opens X) (g g' : Sx X p → A) :
    reprFn A X p V g = reprFn A X p V g' ↔ ∀ t : Sx X p, Set.range t ⊆ V → g t = g' t := by
  constructor
  · intro h t ht
    exact congrFun ((fnEquiv A ((Opens.toTopCat X).obj V) p).symm.injective h)
      (liftOpen X p V t ht)
  · intro h
    refine congrArg (fnEquiv A ((Opens.toTopCat X).obj V) p).symm (funext fun τ => ?_)
    exact h ((openVal X V).comp τ) (by rintro _ ⟨t, rfl⟩; exact (τ t).2)

private lemma fnEquiv_add (Y : TopCat.{u}) (n : ℕ) (φ ψ : (singChains Y).X n ⟶ A) :
    fnEquiv A Y n (φ + ψ) = fnEquiv A Y n φ + fnEquiv A Y n ψ := by
  funext τ
  exact cochainEval_add A Y n φ ψ _

private lemma fnEquiv_zero (Y : TopCat.{u}) (n : ℕ) : fnEquiv A Y n 0 = 0 := by
  funext τ
  rw [fnEquiv_apply]
  unfold cochainEval
  erw [Limits.comp_zero]
  rfl

private lemma reprFn_add (V : Opens X) (g g' : Sx X p → A) :
    reprFn A X p V (g + g') = reprFn A X p V g + reprFn A X p V g' := by
  apply (fnEquiv A ((Opens.toTopCat X).obj V) p).injective
  refine Eq.trans ?_ (fnEquiv_add A _ p _ _).symm
  funext τ
  simp only [reprFn, Equiv.apply_symm_apply, Pi.add_apply]

private lemma reprFn_zero (V : Opens X) : reprFn A X p V 0 = 0 := by
  apply (fnEquiv A ((Opens.toTopCat X).obj V) p).injective
  refine Eq.trans ?_ (fnEquiv_zero A _ p).symm
  funext τ
  simp only [reprFn, Equiv.apply_symm_apply, Pi.zero_apply]

private lemma fnEquiv_d (Y : TopCat.{u}) (n : ℕ) (φ : (singChains Y).X n ⟶ A) (τ : Sx Y (n + 1)) :
    fnEquiv A Y (n + 1) ((singChains Y).d (n + 1) n ≫ φ) τ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • fnEquiv A Y n φ (τ.comp
          (MMP.SingularChain.face n i)) := by
  rw [fnEquiv_apply, cochainEval_d]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fnEquiv_apply, MMP.SingularCochain.simplexEquiv_symm_δ]

private lemma reprFn_d (V : Opens X) (g : Sx X p → A) :
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

private abbrev unitNat (F : TopCat.Presheaf AddCommGrpCat.{u} X) : F ⟶ (sheafify F).obj :=
  (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.app F

private lemma stalkTau_germ (F : TopCat.Presheaf AddCommGrpCat.{u} X) (U : Opens X) (x : X) (hx : x
    ∈ U)
    (s : F.obj (op U)) :
    stalkTau x F (F.germ U x hx s) = (sheafify F).presheaf.germ U x hx ((unitNat F).app (op U) s) :=
        by
  unfold stalkTau
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (unitNat F) s

/-- local representatives -/
private lemma exists_local_repr (P : TopCat.Presheaf AddCommGrpCat.{u} X) (V : Opens X)
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
private structure FunModel (A : Type u) [AddCommGroup A] (P : TopCat.Presheaf AddCommGrpCat.{u} X)
    where
  T : Type u
  rng : T → Set X
  rng_nonempty : ∀ t, (rng t).Nonempty
  repr : ∀ V : Opens X, (T → A) → P.obj (op V)
  repr_res : ∀ {V W : Opens X} (h : W ≤ V) (g : T → A), P.map (homOfLE h).op (repr V g) = repr W g
  repr_surj : ∀ (V : Opens X) (φ : P.obj (op V)), ∃ g, repr V g = φ
  repr_eq : ∀ (V : Opens X) (g g' : T → A), repr V g = repr V g' ↔ ∀ t, rng t ⊆ V → g t = g' t

variable {A : Type u} [AddCommGroup A] {P : TopCat.Presheaf AddCommGrpCat.{u} X}

private lemma FunModel.agree (M : FunModel A P) (V : Opens X) (s : (sheafify P).obj.obj (op V))
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

private lemma exists_shrink {Y : Type*} [TopologicalSpace Y] [ParacompactSpace Y] [NormalSpace Y]
    {ι : Type*} (W : ι → Set Y) (hW : ∀ i, IsOpen (W i)) (hc : ⋃ i, W i = Set.univ) :
    ∃ u : ι → Set Y, (∀ i, IsOpen (u i)) ∧ ⋃ i, u i = Set.univ ∧ LocallyFinite u ∧
      ∀ i, closure (u i) ⊆ W i := by
  obtain ⟨v, hvo, hvc, hvl, hvW⟩ := precise_refinement W hW hc
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_subset_iUnion_closure_subset (u := v) (s := Set.univ)
    isClosed_univ hvo (fun x _ => hvl.point_finite x) (by rw [hvc])
  refine ⟨u, hu2, Set.eq_univ_of_univ_subset hu1, hvl.subset fun i => ?_, fun i => ?_⟩
  · exact subset_closure.trans (hu3 i)
  · exact (hu3 i).trans (hvW i)

private lemma FunModel.exists_glue (M : FunModel A P) (V : Opens X) [ParacompactSpace V]
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
      · simp only [F, if_pos hc]; exact (Ni i).isOpen.preimage continuous_subtype_val
      · simp only [F, if_neg hc]; exact isClosed_closure.isOpen_compl
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

private def cochainFunModel (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) :
    FunModel (A : Type u) (singCochainTerm A X p) where
  T := Sx X p
  rng := fun t => Set.range t
  rng_nonempty := fun t => ⟨t (stdSimplex.vertex 0), ⟨_, rfl⟩⟩
  repr := reprFn A X p
  repr_res := reprFn_res A X p
  repr_surj := reprFn_surj A X p
  repr_eq := reprFn_eq A X p

/-- The sheafified singular cochains are flasque on a metrizable space. -/
private theorem singCochainSheaves_isFlasque (A : AddCommGrpCat.{u}) (X : TopCat.{u})
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

private abbrev gammaS (A : AddCommGrpCat.{u}) (X : TopCat.{u}) : CochainComplex AddCommGrpCat.{u}
    ℕ :=
  ((globalSections X).mapHomologicalComplex _).obj (singCochainSheaves A X)

private def singEps (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
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
private def LocZero {A : AddCommGrpCat.{u}} {X : TopCat.{u}} {p : ℕ} (g : Sx X p → A) : Prop :=
  ∃ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) ∧ ⋃₀ 𝒰 = Set.univ ∧
    ∀ t : Sx X p, (∃ U ∈ 𝒰, Set.range t ⊆ U) → g t = 0

private lemma locZero_of_eps_eq_zero (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (g : Sx X p →
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

private lemma eps_eq_zero_of_locZero (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (g : Sx X p →
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
  show (sheafify (singCochainTerm A X p)).presheaf.germ ⊤ x hx
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

private lemma eps_surj (A : AddCommGrpCat.{u}) (X : TopCat.{u}) [MetrizableSpace X] (p : ℕ)
    (s : (gammaS A X).X p) : ∃ g : Sx X p → A, (singEps A X).f p (reprFn A X p ⊤ g) = s := by
  haveI : MetrizableSpace (⊤ : Opens X) := Topology.IsEmbedding.subtypeVal.metrizableSpace
  letI := TopologicalSpace.metrizableSpaceMetric (⊤ : Opens X)
  obtain ⟨φ, hφ⟩ := (cochainFunModel A X p).exists_glue ⊤ s
  obtain ⟨g, rfl⟩ := reprFn_surj A X p ⊤ φ
  exact ⟨g, hφ⟩

private lemma reprFn_sub (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (V : Opens X) (g g' : Sx X
    p → A) :
    reprFn A X p V (g - g') = reprFn A X p V g - reprFn A X p V g' := by
  rw [eq_sub_iff_add_eq, ← reprFn_add, sub_add_cancel]

private lemma reprFn_top_injective (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) {g g' : Sx X p →
    A}
    (h : reprFn A X p ⊤ g = reprFn A X p ⊤ g') : g = g' :=
  funext fun t => (reprFn_eq A X p ⊤ g g').1 h t (fun _ _ => trivial)

private lemma cob_sub (n : ℕ) {A : AddCommGrpCat.{u}} {X : TopCat.{u}} (g g' : Sx X n → A) :
    cob n (g - g') = cob n g - cob n g' := by
  funext σ
  simp [cob, smul_sub, Finset.sum_sub_distrib]

private lemma cob_cob (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (g : Sx X p → A) :
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

private lemma eps_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (x : ((singCochainPresheaf A
    X).obj (op ⊤)).X p) :
    (singEps A X).f (p + 1) (((singCochainPresheaf A X).obj (op ⊤)).d p (p + 1) x) =
      (gammaS A X).d p (p + 1) ((singEps A X).f p x) :=
  (ConcreteCategory.congr_hom ((singEps A X).comm p (p + 1)) x).symm

private lemma eps_surj_cohom (A : AddCommGrpCat.{u}) (X : TopCat.{u}) [MetrizableSpace X] (q : ℕ)
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

private lemma cob_add (n : ℕ) {A : AddCommGrpCat.{u}} {X : TopCat.{u}} (g g' : Sx X n → A) :
    cob n (g + g') = cob n g + cob n g' := by
  funext σ
  simp [cob, smul_add, Finset.sum_add_distrib]

private lemma eps_inj_succ (A : AddCommGrpCat.{u}) (X : TopCat.{u}) [MetrizableSpace X] (m : ℕ)
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

noncomputable section NatCopy

section Pushforward

variable (A : AddCommGrpCat.{u}) {M N : TopCat.{u}} (f : N ⟶ M)

/-- The restriction `f⁻¹ U ⟶ U` of `f` to an open set. -/
private def fRes (U : Opens M) :
    (Opens.toTopCat N).obj ((Opens.map f).obj U) ⟶ (Opens.toTopCat M).obj U :=
  TopCat.ofHom ⟨fun y => ⟨f y.1, y.2⟩, by fun_prop⟩

private lemma fRes_comp {U V : Opens M} (i : V ⟶ U) :
    (Opens.toTopCat N).map ((Opens.map f).map i) ≫ fRes f U = fRes f V ≫ (Opens.toTopCat M).map i :=
        by
  ext y
  rfl

/-- The presheaf map `P_M^p ⟶ f_* P_N^p`, `φ ↦ f^* φ`. -/
private def thetaP (p : ℕ) :
    singCochainTerm A M p ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj (singCochainTerm A
        N p) where
  app U := AddCommGrpCat.ofHom
    { toFun := fun φ => (((singularChainComplexFunctor AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))).map (fRes f U.unop)).f p ≫ φ
      map_zero' := by
        erw [Limits.comp_zero]; rfl
      map_add' := fun a b => by
        erw [Preadditive.comp_add]; rfl }
  naturality U V i := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ => ?_)
    have h := congrArg (fun g => (((singularChainComplexFunctor AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))).map g).f p) (fRes_comp f i.unop)
    simp only [Functor.map_comp, HomologicalComplex.comp_f] at h
    change (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map
        (fRes f V.unop)).f p ≫ ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ))).map ((Opens.toTopCat M).map i.unop)).f p ≫ φ) =
      (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map
        ((Opens.toTopCat N).map ((Opens.map f).map i.unop))).f p ≫ ((((singularChainComplexFunctor
            AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ))).map (fRes f U.unop)).f p ≫ φ)
    erw [← Category.assoc, ← Category.assoc, h]

private instance pushforwardPresheafZero : (TopCat.Presheaf.pushforward AddCommGrpCat.{u}
    f).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

private def thetaPComplex : singCochainPresheafComplex A M ⟶
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj
      (singCochainPresheafComplex A N) where
  f p := thetaP A f p
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have e1 : ∀ (Y : TopCat.{u}), (singCochainPresheafComplex A Y).d i (i + 1) = singCochainTermD A
        Y i :=
      fun Y => CochainComplex.of_d _ _ _
    refine NatTrans.ext (funext fun U => ?_)
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ => ?_)
    have h := (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift
        ℤ))).map
      (fRes f U.unop)).comm (i + 1) i
    change ((singCochainPresheafComplex A N).d i (i + 1)).app (op ((Opens.map f).obj U.unop))
        ((thetaP A f i).app U φ) =
      (thetaP A f (i + 1)).app U (((singCochainPresheafComplex A M).d i (i + 1)).app U φ)
    rw [e1, e1]
    change (singChains _).d (i + 1) i ≫ ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))).map (fRes f U.unop)).f i ≫ φ) =
      (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map
        (fRes f U.unop)).f (i + 1) ≫ ((singChains _).d (i + 1) i ≫ φ)
    erw [← Category.assoc, ← Category.assoc, h]

private def thetaKf (p : ℕ) : sheafify (singCochainTerm A M p) ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (sheafify (singCochainTerm A N p)) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology M) AddCommGrpCat.{u}).homEquiv
    (singCochainTerm A M p) ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (sheafify
        (singCochainTerm A N p)))).symm
    (thetaP A f p ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
      (unitNat (singCochainTerm A N p)))

private lemma thetaKf_unit (p : ℕ) :
    unitNat (singCochainTerm A M p) ≫ (thetaKf A f p).hom =
      thetaP A f p ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
        (unitNat (singCochainTerm A N p)) := by
  have h := (sheafificationAdjunction (Opens.grothendieckTopology M)
      AddCommGrpCat.{u}).homEquiv_unit
    (X := singCochainTerm A M p) (Y := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (sheafify
        (singCochainTerm A N p)))
    (f := thetaKf A f p)
  have h2 := ((sheafificationAdjunction (Opens.grothendieckTopology M) AddCommGrpCat.{u}).homEquiv
    (singCochainTerm A M p) ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (sheafify
        (singCochainTerm A N p)))).apply_symm_apply
    (thetaP A f p ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map (unitNat (singCochainTerm
        A N p)))
  exact h.symm.trans h2

private lemma thetaP_comm (p : ℕ) :
    thetaP A f p ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map (singCochainTermD A N p) =
      singCochainTermD A M p ≫ thetaP A f (p + 1) := by
  have h := (thetaPComplex A f).comm p (p + 1)
  have e1 : ∀ (Y : TopCat.{u}), (singCochainPresheafComplex A Y).d p (p + 1) = singCochainTermD A Y
      p :=
    fun Y => CochainComplex.of_d _ _ _
  change thetaP A f p ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
      ((singCochainPresheafComplex A N).d p (p + 1)) =
    (singCochainPresheafComplex A M).d p (p + 1) ≫ thetaP A f (p + 1) at h
  rwa [e1, e1] at h

private lemma singSheaf_d (X : TopCat.{u}) (p : ℕ) :
    (singCochainSheaves A X).d p (p + 1) =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (singCochainTermD A X
          p) :=
  congrArg (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (CochainComplex.of_d _ _ _)

private lemma unit_comp_singSheaf_d (X : TopCat.{u}) (p : ℕ) :
    unitNat (singCochainTerm A X p) ≫ ((singCochainSheaves A X).d p (p + 1)).hom =
      singCochainTermD A X p ≫ unitNat (singCochainTerm A X (p + 1)) := by
  rw [singSheaf_d]
  exact ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.naturality
    (singCochainTermD A X p)).symm

private lemma sheafify_hom_ext {X : TopCat.{u}} {P : TopCat.Presheaf AddCommGrpCat.{u} X}
    {S : TopCat.Sheaf AddCommGrpCat.{u} X} {u v : sheafify P ⟶ S}
    (h : unitNat P ≫ u.hom = unitNat P ≫ v.hom) : u = v := by
  have e1 := (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).homEquiv_unit
    (X := P) (Y := S) (f := u)
  have e2 := (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).homEquiv_unit
    (X := P) (Y := S) (f := v)
  exact ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv P
      S).injective
    (e1.trans (h.trans e2.symm))

private def thetaK : singCochainSheaves A M ⟶
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj (singCochainSheaves
        A N) where
  f p := thetaKf A f p
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    apply sheafify_hom_ext
    change unitNat (singCochainTerm A M i) ≫ ((thetaKf A f i) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map ((singCochainSheaves A N).d i (i +
            1))).hom =
      unitNat (singCochainTerm A M i) ≫ (((singCochainSheaves A M).d i (i + 1)) ≫ thetaKf A f (i +
          1)).hom
    have hθ := thetaKf_unit A f i
    have hθ' := thetaKf_unit A f (i + 1)
    have hdN := unit_comp_singSheaf_d A N i
    have hdM := unit_comp_singSheaf_d A M i
    have hc := thetaP_comm A f i
    change unitNat (singCochainTerm A M i) ≫ ((thetaKf A f i).hom ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map ((singCochainSheaves A N).d i (i +
            1)).hom) =
      unitNat (singCochainTerm A M i) ≫ (((singCochainSheaves A M).d i (i + 1)).hom ≫ (thetaKf A f
          (i + 1)).hom)
    erw [← Category.assoc, hθ, Category.assoc, ← Functor.map_comp, hdN, Functor.map_comp, ←
        Category.assoc, hc,
      Category.assoc, ← hθ', ← Category.assoc, ← hdM, Category.assoc]

end Pushforward

section ConstCompat

private def constPt (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :=
  (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} Limits.isTerminalTop).unit.app
      A

private lemma constPt_aug (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (a : A) :
    ((constPt A X ≫ (globalSections X).map (constAugDeg0 A X)).hom a) =
      (singEps A X).f 0 (constCochain A ((Opens.toTopCat X).obj ⊤) a) := by
  unfold constPt
  simp only [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj_unit_app]
  have hn := congrArg (fun t => t.app (op ⊤))
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.naturality
        (constToCochain A X))
  have hn' := ConcreteCategory.congr_hom hn.symm a
  rw [Category.id_comp]
  exact hn'

variable {M N : TopCat.{u}} (f : N ⟶ M)

/-- The comparison `f⁻¹ A_M ⟶ A_N` of the statement. -/
private def toConstDef (A : AddCommGrpCat.{u}) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj (constSheaf A M) ⟶ constSheaf A N :=
  (((constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{u}
      Limits.isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).homEquiv
      A (constSheaf A N)).symm
    ((constantSheafAdj (Opens.grothendieckTopology N) AddCommGrpCat.{u}
        Limits.isTerminalTop).unit.app A ≫
      (constSheaf A N).obj.map (homOfLE le_top).op)

/-- The adjoint `A_M ⟶ f_* A_N` of the comparison. -/
private def thetaF (A : AddCommGrpCat.{u}) : constSheaf A M ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (constSheaf A N) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app (constSheaf A M) ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (toConstDef f A)

private lemma constPt_thetaF (A : AddCommGrpCat.{u}) :
    constPt A M ≫ (globalSections M).map (thetaF f A) =
      constPt A N ≫ (constSheaf A N).obj.map (homOfLE le_top).op := by
  have h0 := ((((constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{u}
      Limits.isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).homEquiv
      A (constSheaf A N))).apply_symm_apply
    (constPt A N ≫ (constSheaf A N).obj.map (homOfLE le_top).op)
  have e : ∀ u : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj (constSheaf A M) ⟶ constSheaf A N,
      (((constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{u}
        Limits.isTerminalTop).comp
          (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).homEquiv A (constSheaf A
              N)) u =
        constPt A M ≫ (globalSections M).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app (constSheaf A
              M) ≫
            (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map u) := by
    intro u
    erw [Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply, Adjunction.homEquiv_unit]
    rfl
  exact (e _).symm.trans h0

private lemma const_theta (A : AddCommGrpCat.{u}) (a : A) :
    (thetaKf A f 0).hom.app (op ⊤) ((singEps A M).f 0 (constCochain A ((Opens.toTopCat M).obj ⊤) a))
        =
      (singEps A N).f 0 (constCochain A ((Opens.toTopCat N).obj ⊤) a) := by
  let x0 : (singCochainTerm A M 0).obj (op ⊤) := constCochain A ((Opens.toTopCat M).obj ⊤) a
  have hθ := ConcreteCategory.congr_hom (congrArg (fun t => t.app (op ⊤)) (thetaKf_unit A f 0)) x0
  have key : (thetaP A f 0).app (op ⊤) (constCochain A ((Opens.toTopCat M).obj ⊤) a) =
      constCochain A ((Opens.toTopCat N).obj ⊤) a := by
    refine cochainEval_injective A _ 0 (funext fun σ => ?_)
    change cochainEval A _ 0 ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))).map (fRes f ⊤)).f 0 ≫ constCochain A ((Opens.toTopCat M).obj ⊤)
          a) σ = _
    rw [cochainEval_map, cochainEval_constCochain]
    erw [cochainEval_constCochain]
  change (thetaKf A f 0).hom.app (op ⊤) ((unitNat (singCochainTerm A M 0)).app (op ⊤)
      (constCochain A ((Opens.toTopCat M).obj ⊤) a)) = (unitNat (singCochainTerm A N 0)).app (op ⊤)
      (constCochain A ((Opens.toTopCat N).obj ⊤) a)
  erw [hθ]
  exact congrArg (fun x => (unitNat (singCochainTerm A N 0)).app (op ⊤) x) key

private lemma map_homOfLE_top (A : AddCommGrpCat.{u}) (x : ((constSheaf A N).obj.obj (op ⊤))) :
    (constSheaf A N).obj.map (homOfLE le_top : (Opens.map f).obj ⊤ ⟶ ⊤).op x = x := by
  have : (homOfLE le_top : (Opens.map f).obj ⊤ ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [this]
  simp
  rfl

private lemma constAugDeg0_theta (A : AddCommGrpCat.{u}) :
    constAugDeg0 A M ≫ thetaKf A f 0 =
      thetaF f A ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (constAugDeg0 A N) := by
  let adj := constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{u} Limits.isTerminalTop
  have e1 := adj.homEquiv_unit (X := A) (Y := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
    ((singCochainSheaves A N).X 0)) (f := constAugDeg0 A M ≫ thetaKf A f 0)
  have e2 := adj.homEquiv_unit (X := A) (Y := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
    ((singCochainSheaves A N).X 0)) (f := thetaF f A ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        f).map (constAugDeg0 A N))
  refine (adj.homEquiv A ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
    ((singCochainSheaves A N).X 0))).injective (e1.trans (Eq.trans ?_ e2.symm))
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
  have hL := constPt_aug A M a
  have hR := constPt_aug A N a
  have hT := ConcreteCategory.congr_hom (constPt_thetaF f A) a
  change (thetaKf A f 0).hom.app (op ⊤) ((constAugDeg0 A M).hom.app (op ⊤) ((constPt A M).hom a)) =
    (constAugDeg0 A N).hom.app (op ⊤) ((thetaF f A).hom.app (op ⊤) ((constPt A M).hom a))
  have hL' : (constAugDeg0 A M).hom.app (op ⊤) ((constPt A M).hom a) =
      (singEps A M).f 0 (constCochain A ((Opens.toTopCat M).obj ⊤) a) := hL
  have hT'' : (thetaF f A).hom.app (op ⊤) ((constPt A M).hom a) = (constPt A N).hom a := by
    refine hT.trans ?_
    exact map_homOfLE_top f A _
  rw [hL', hT'']
  erw [const_theta f A a]
  exact hR.symm

end ConstCompat

end NatCopy

noncomputable section Comparison

attribute [local instance] CategoryTheory.hasExt_of_enoughInjectives

/-- The integers as an abelian group. -/
private abbrev Zc : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ

variable (M : TopCat.{0})

/-- Sheaves of abelian groups on `M`. -/
private abbrev Sh : Type 1 := Sheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}

/-- The sheafified integral singular cochains. -/
private abbrev KS : CochainComplex (Sh M) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).mapHomologicalComplex _).obj
    (singCochainPresheafComplex Zc M)

/-- The constant sheaf `ℤ_M`. -/
private abbrev ZM : Sh M := (constantSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).obj Zc

/-- The augmentation `ℤ_M ⟶ 𝒮⁰`. -/
private abbrev aug0 : ZM M ⟶ (KS M).X 0 :=
  (presheafToSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).map (constToCochain Zc M)

/-- The sheaf of `1`-cocycles. -/
private abbrev Z1 : Sh M := kernel ((KS M).d 1 2)

/-- The sheaf of `2`-cocycles. -/
private abbrev Z2 : Sh M := kernel ((KS M).d 2 3)

private noncomputable def g1 : (KS M).X 0 ⟶ Z1 M := kernel.lift _ ((KS M).d 0 1) ((KS M).d_comp_d 0 1 2)

private noncomputable def g2 : (KS M).X 1 ⟶ Z2 M := kernel.lift _ ((KS M).d 1 2) ((KS M).d_comp_d 1 2 3)

private lemma g1_ι : g1 M ≫ kernel.ι _ = (KS M).d 0 1 := kernel.lift_ι _ _ _

private lemma g2_ι : g2 M ≫ kernel.ι _ = (KS M).d 1 2 := kernel.lift_ι _ _ _

private lemma aug0_d : aug0 M ≫ (KS M).d 0 1 = 0 := constAugDeg0_comp_d Zc M

private lemma w1 : aug0 M ≫ g1 M = 0 := by
  rw [← cancel_mono (kernel.ι ((KS M).d 1 2)), Category.assoc, g1_ι, zero_comp]
  exact aug0_d M

private lemma w2 : kernel.ι ((KS M).d 1 2) ≫ g2 M = 0 := by
  rw [← cancel_mono (kernel.ι ((KS M).d 2 3)), Category.assoc, g2_ι, zero_comp]
  exact kernel.condition _

/-- `0 ⟶ ℤ_M ⟶ 𝒮⁰ ⟶ Z¹ ⟶ 0`. -/
private noncomputable abbrev S1 : ShortComplex (Sh M) := ShortComplex.mk (aug0 M) (g1 M) (w1 M)

/-- `0 ⟶ Z¹ ⟶ 𝒮¹ ⟶ Z² ⟶ 0`. -/
private noncomputable abbrev S2 : ShortComplex (Sh M) :=
  ShortComplex.mk (kernel.ι ((KS M).d 1 2)) (g2 M) (w2 M)

variable {M}

private lemma KS_exactAt (hM : LocallyContractibleSpace M) (n : ℕ) : (KS M).ExactAt (n + 1) :=
  singCochainSheaves_exactAt Zc M hM n

private lemma S1_shortExact (hM : LocallyContractibleSpace M) : (S1 M).ShortExact := by
  have hex : (ShortComplex.mk (aug0 M) ((KS M).d 0 1) (aug0_d M)).Exact :=
    exact_constAugDeg0 Zc M hM
  have : Mono (aug0 M) := mono_constAugDeg0 Zc M
  refine ShortComplex.ShortExact.mk' ?_ inferInstance ?_
  · let φ : S1 M ⟶ ShortComplex.mk (aug0 M) ((KS M).d 0 1) (aug0_d M) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι _, comm₂₃ := (Category.id_comp _).trans (g1_ι M).symm }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hex
  · have h1 := ((KS M).exactAt_iff' 0 1 2 (by simp) (by simp)).1 (KS_exactAt hM 0)
    exact h1.epi_kernelLift

private lemma S2_shortExact (hM : LocallyContractibleSpace M) : (S2 M).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ inferInstance ?_
  · let φ : S2 M ⟶ ShortComplex.mk (kernel.ι ((KS M).d 1 2)) ((KS M).d 1 2) (kernel.condition _) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι _, comm₂₃ := (Category.id_comp _).trans (g2_ι M).symm }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
  · have h1 := ((KS M).exactAt_iff' 1 2 3 (by simp) (by simp)).1 (KS_exactAt hM 1)
    exact h1.epi_kernelLift

section psi

open CategoryTheory.Abelian Stacks.SupportedVanishing

/-- The global section of `𝒮^p` of a singular cochain. -/
private def epsG (p : ℕ) (g : Sx M p → ℤ) : ToType (((KS M).X p).obj.obj (op ⊤)) :=
  (singEps Zc M).f p (reprFn Zc M p ⊤ g)

private lemma epsG_d (p : ℕ) (g : Sx M p → ℤ) :
    ((KS M).d p (p + 1)).hom.app (op ⊤) (epsG p g) = epsG (p + 1) (cob p g) := by
  have e1 := eps_d Zc M p (reprFn Zc M p ⊤ g)
  erw [reprFn_d] at e1
  exact e1.symm

private lemma epsG_add (p : ℕ) (g g' : Sx M p → ℤ) : epsG p (g + g') = epsG p g + epsG p g' := by
  simp only [epsG]
  erw [reprFn_add]
  exact map_add _ _ _

private lemma epsG_zero (p : ℕ) : epsG (M := M) p 0 = 0 := by
  simp only [epsG]
  erw [reprFn_zero]
  exact map_zero _

/-- The morphism `ℤ_M ⟶ 𝒮^p` of a singular cochain. -/
private def epsH (p : ℕ) (g : Sx M p → ℤ) : constZ M ⟶ (KS M).X p :=
  (homConstAddEquiv _).symm (epsG p g)

private lemma homConstAddEquiv_epsH (p : ℕ) (g : Sx M p → ℤ) :
    homConstAddEquiv _ (epsH p g) = epsG p g := by
  simp [epsH]

private lemma epsH_d (p : ℕ) (g : Sx M p → ℤ) :
    epsH p g ≫ (KS M).d p (p + 1) = epsH (p + 1) (cob p g) := by
  apply (homConstAddEquiv _).injective
  rw [homConstAddEquiv_comp, homConstAddEquiv_epsH, homConstAddEquiv_epsH]
  exact epsG_d p g

private lemma epsH_add (p : ℕ) (g g' : Sx M p → ℤ) : epsH p (g + g') = epsH p g + epsH p g' := by
  simp only [epsH, epsG_add, map_add]

private lemma epsH_zero (p : ℕ) : epsH (M := M) p 0 = 0 := by
  simp only [epsH, epsG_zero, map_zero]

private lemma epsH_cocycle (z : Sx M 2 → ℤ) (hz : cob 2 z = 0) :
    epsH 2 z ≫ (KS M).d 2 3 = 0 := by
  rw [epsH_d, hz, epsH_zero]

/-- The morphism `ℤ_M ⟶ Z²` of a singular `2`-cocycle. -/
private def zhat (z : Sx M 2 → ℤ) (hz : cob 2 z = 0) : constZ M ⟶ Z2 M :=
  kernel.lift _ (epsH 2 z) (epsH_cocycle z hz)

private lemma zhat_ι (z : Sx M 2 → ℤ) (hz : cob 2 z = 0) :
    zhat z hz ≫ kernel.ι _ = epsH 2 z := kernel.lift_ι _ _ _

private lemma zhat_add (z z' : Sx M 2 → ℤ) (hz : cob 2 z = 0) (hz' : cob 2 z' = 0)
    (h : cob 2 (z + z') = 0) : zhat (z + z') h = zhat z hz + zhat z' hz' := by
  rw [← cancel_mono (kernel.ι ((KS M).d 2 3)), Preadditive.add_comp, zhat_ι, zhat_ι, zhat_ι,
    epsH_add]

private lemma zhat_cob (m : Sx M 1 → ℤ) (h : cob 2 (cob 1 m) = 0) :
    zhat (cob 1 m) h = epsH 1 m ≫ g2 M := by
  rw [← cancel_mono (kernel.ι ((KS M).d 2 3)), zhat_ι, Category.assoc, g2_ι, epsH_d]

variable (hM : LocallyContractibleSpace M)

/-- The class in `Ext²(ℤ_M, ℤ_M)` of a singular `2`-cocycle. -/
private def psi (z : Sx M 2 → ℤ) (hz : cob 2 z = 0) : Ext (constZ M) (ZM M) 2 :=
  ((Ext.mk₀ (zhat z hz)).comp (S2_shortExact hM).extClass (zero_add 1)).comp
    (S1_shortExact hM).extClass (show 1 + 1 = 2 from rfl)

private lemma psi_add (z z' : Sx M 2 → ℤ) (hz : cob 2 z = 0) (hz' : cob 2 z' = 0)
    (h : cob 2 (z + z') = 0) : psi hM (z + z') h = psi hM z hz + psi hM z' hz' := by
  simp only [psi, zhat_add z z' hz hz' h, Ext.mk₀_add, Ext.add_comp]

private lemma psi_cob (m : Sx M 1 → ℤ) (h : cob 2 (cob 1 m) = 0) : psi hM (cob 1 m) h = 0 := by
  have h0 : (Ext.mk₀ (g2 M)).comp (S2_shortExact hM).extClass (zero_add 1) = 0 :=
    (S2_shortExact hM).comp_extClass
  simp only [psi, zhat_cob, ← Ext.mk₀_comp_mk₀]
  rw [Ext.comp_assoc_of_second_deg_zero, h0, Ext.comp_zero, Ext.zero_comp]

end psi

section psiIso

open CategoryTheory.Abelian Stacks.SupportedVanishing MMP MMP.SingularCochain

variable [MetrizableSpace M] (hM : LocallyContractibleSpace M)

private lemma ext_KS_subsingleton (p k : ℕ) :
    Subsingleton (Ext (constZ M) ((KS M).X p) (k + 1)) := by
  haveI : TopCat.Sheaf.IsFlasque ((KS M).X p) := singCochainSheaves_isFlasque Zc M p
  exact subsingleton_ext_of_isFlasque k _

private lemma psi_surjective (e : Ext (constZ M) (ZM M) 2) :
    ∃ (z : Sx M 2 → ℤ) (hz : cob 2 z = 0), psi hM z hz = e := by
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
  simp only [psi, hs, hy, hx₃]

private lemma exists_cob_eq_of_psi_eq_zero (z : Sx M 2 → ℤ) (hz : cob 2 z = 0)
    (h : psi hM z hz = 0) : ∃ m : Sx M 1 → ℤ, cob 1 m = z := by
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

private lemma cob_eq_coboundary (n : ℕ) (g : Sx M n → ℤ) : cob n g = coboundary ℤ n g := by
  funext σ
  rw [coboundary_apply]
  simp only [cob, zsmul_eq_mul, Int.cast_id]

private lemma cob_of_mem_relCocycles {z : Sx M 2 → ℤ} (hz : z ∈ relCocycles ℤ (∅ : Set M) 2) :
    cob 2 z = 0 := by
  rw [cob_eq_coboundary]
  exact hz.2

/-- `psi` on relative cocycles. -/
private def psiCoc : relCocycles ℤ (∅ : Set M) 2 →+ Ext (constZ M) (ZM M) 2 where
  toFun z := psi hM z.1 (cob_of_mem_relCocycles z.2)
  map_zero' := by
    have h0 : cob 2 (0 : Sx M 2 → ℤ) = 0 := by rw [cob_eq_coboundary, map_zero]
    have := psi_add hM 0 0 h0 h0 (by rw [add_zero]; exact h0)
    simp only [add_zero] at this
    exact add_eq_left.1 this.symm
  map_add' z z' := psi_add hM z.1 z'.1 _ _ _

/-- `psi` on relative cohomology. -/
private def psiBar : relCohomology ℤ (∅ : Set M) 2 →ₗ[ℤ] Ext (constZ M) (ZM M) 2 :=
  ((relCoboundaries ℤ (∅ : Set M) 2).comap (relCocycles ℤ (∅ : Set M) 2).subtype).liftQ
    (psiCoc hM).toIntLinearMap (by
      rintro ⟨z, hz⟩ hb
      obtain ⟨m, -, hm⟩ := hb
      change psi hM z _ = 0
      subst hm
      have : coboundary ℤ 1 m = cob 1 m := (cob_eq_coboundary 1 m).symm
      revert hz
      rw [this]
      intro hz
      exact psi_cob hM m _)

private lemma psiBar_mk (z : relCocycles ℤ (∅ : Set M) 2) :
    psiBar hM (Submodule.Quotient.mk z) = psi hM z.1 (cob_of_mem_relCocycles z.2) := rfl

private lemma psiBar_bijective : Function.Bijective (psiBar hM) := by
  refine ⟨?_, fun e => ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, psiBar_mk] at hx
    obtain ⟨m, hm⟩ := exists_cob_eq_of_psi_eq_zero hM _ _ hx
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨m, fun σ hσ => absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
      by rw [← cob_eq_coboundary, hm]; rfl⟩
  · obtain ⟨z, hz, rfl⟩ := psi_surjective hM e
    have hz' : z ∈ relCocycles ℤ (∅ : Set M) 2 :=
      ⟨fun σ hσ => absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
        LinearMap.mem_ker.2 (by rw [← cob_eq_coboundary]; exact hz)⟩
    exact ⟨Submodule.Quotient.mk ⟨z, hz'⟩, rfl⟩

/-- **The comparison isomorphism** `Ext²(ℤ_M, ℤ_M) ≃ H²_sing(M; ℤ)`. -/
private def phi : Ext (constZ M) (ZM M) 2 ≃+ relativeSingularCohomology ℤ (.of ℤ ℤ) M ∅ 2 :=
  (LinearEquiv.ofBijective (psiBar hM) (psiBar_bijective hM)).symm.toAddEquiv.trans
    (relativeSingularCohomologyEquiv ℤ (∅ : Set M) 2).symm.toAddEquiv

private lemma phi_symm_mk (z : relCocycles ℤ (∅ : Set M) 2) :
    (phi hM).symm ((relativeSingularCohomologyEquiv ℤ (∅ : Set M) 2).symm
      (Submodule.Quotient.mk z)) = psi hM z.1 (cob_of_mem_relCocycles z.2) := by
  simp [phi, psiBar_mk]

end psiIso

end Comparison

section CechConnecting

open CategoryTheory.Abelian

open Stacks.Cohomology.CechOne

variable {X : TopCat.{0}}

/-- The additivity of global sections, in the spelling the comparison lemmas use. -/
private abbrev sectionsAdditive :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).Additive :=
  inferInstanceAs (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op ⊤)).Additive

attribute [local instance] sectionsAdditive

/-- A `1`-cycle of the global sections of the chosen injective resolution, read as a map out of
the constant sheaf, is killed by the next differential. -/
private theorem sectionsCoyonedaIso_inv_iCycles_comp_d
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (x : ToType (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution F).cocomplex).cycles 1)) :
    (Stacks.Thickenings.sectionsCoyonedaIso X).inv.app _
        (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
          (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution F).cocomplex).iCycles 1 x) ≫
      (injectiveResolution F).cocomplex.d 1 2 = 0 := by
  have h1 := ConcreteCategory.congr_hom ((Stacks.Thickenings.sectionsCoyonedaIso X).inv.naturality
    ((injectiveResolution F).cocomplex.d 1 2)) ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).iCycles 1 x)
  have h2 := ConcreteCategory.congr_hom ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).iCycles_d 1 2) x
  refine h1.symm.trans ?_
  change (Stacks.Thickenings.sectionsCoyonedaIso X).inv.app _ ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).d 1 2 ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).iCycles 1 x)) = 0
  have h3 : ConcreteCategory.hom ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).d 1 2) (ConcreteCategory.hom ((((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).iCycles 1) x) = 0 := h2
  rw [h3]
  exact map_zero _

/-- `sheafCohomologyOneExtEquiv` is the inverse of the degree-one comparison
`extFunctorObjIsoRightDerived`. -/
private theorem sheafCohomologyOneExtEquiv_hom_eq_extFunctorObjIsoRightDerived_inv
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :
    (Stacks.Thickenings.sheafCohomologyOneExtEquiv X F).hom =
      (ModuleSheafCohomology.extFunctorObjIsoRightDerived
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤))
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (ULift.{0} ℤ))) (Stacks.Thickenings.sectionsCoyonedaIso X).symm 1).inv.app
        F := by
  unfold Stacks.Thickenings.sheafCohomologyOneExtEquiv
    ModuleSheafCohomology.extFunctorObjIsoRightDerived
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, NatTrans.comp_app]
  congr 1

/-- The comparison `H¹(X, F) ≃ Ext¹(ℤ_X, F)` sends the class of a `1`-cocycle of the global
sections of the chosen injective resolution of `F` to the `Ext` class of that cocycle. -/
private theorem sheafCohomologyOneExtEquiv_resolutionClass
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (x : ToType (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution F).cocomplex).cycles 1)) :
    (Stacks.Thickenings.sheafCohomologyOneExtEquiv X F).hom
        (((injectiveResolution F).isoRightDerivedObj ((sheafSections (Opens.grothendieckTopology X)
            AddCommGrpCat.{0}).obj (op ⊤)) 1).inv
          (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
            (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution F).cocomplex).homologyπ 1 x)) =
      (injectiveResolution F).extMk
        ((Stacks.Thickenings.sectionsCoyonedaIso X).inv.app _
          (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
            (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution F).cocomplex).iCycles 1 x)) 2 rfl
          (sectionsCoyonedaIso_inv_iCycles_comp_d F x) := by
  let α := (Stacks.Thickenings.sectionsCoyonedaIso X).symm
  have h := Stacks.Cohomology.ModuleComparison.extFunctorObjIsoRightDerived_succ_hom_app_comp
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤))
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ULift.{0} ℤ))) α F 0 (by simp) (by simp)
  let y := HomologicalComplex.cyclesMap
    ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app
      (injectiveResolution F).cocomplex) 1 x
  have hy : HomologicalComplex.cyclesMap ((NatTrans.mapHomologicalComplex α.inv
      (ComplexShape.up ℕ)).app (injectiveResolution F).cocomplex) 1 y = x := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.cyclesMap_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomologicalComplex_comp, α.hom_inv_id, NatTrans.mapHomologicalComplex_id,
      NatTrans.id_app, HomologicalComplex.cyclesMap_id, ConcreteCategory.id_apply]
  have h' := ConcreteCategory.congr_hom h y
  set w := (ModuleSheafCohomology.extLeftHomologyData (injectiveResolution F)
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ULift.{0} ℤ))) 0).cyclesIso.hom
        (((((preadditiveCoyoneda.obj (op ((constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))))).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex).cyclesIsoSc' 0 1 2
              (by simp) (by simp)).hom y) with hw
  have h2 : ((injectiveResolution F).isoRightDerivedObj ((sheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)) 1).inv
        (((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
          (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution F).cocomplex).homologyπ 1 x) =
      (ModuleSheafCohomology.extFunctorObjIsoRightDerived
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤))
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (ULift.{0} ℤ))) α 1).hom.app F
        (ModuleSheafCohomology.extCyclesMap (injectiveResolution F)
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
            (AddCommGrpCat.of (ULift.{0} ℤ))) 0 w) := by
    rw [← hy]
    exact h'.symm
  rw [h2]
  rw [sheafCohomologyOneExtEquiv_hom_eq_extFunctorObjIsoRightDerived_inv]
  refine (Iso.hom_inv_id_app_apply _ _ _).trans ?_
  refine (ModuleSheafCohomology.extCyclesMap_apply _ _ _ w).trans ?_
  congr 1
  have e1 := ConcreteCategory.congr_hom
    (ModuleSheafCohomology.extLeftHomologyData (injectiveResolution F) ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))) 0).cyclesIso_hom_comp_i
    (((((preadditiveCoyoneda.obj (op ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))))).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex).cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom y)
  have e2 := ConcreteCategory.congr_hom
    ((((preadditiveCoyoneda.obj (op ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))))).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex).cyclesIsoSc'_hom_iCycles 0 1 2 (by simp) (by simp)) y
  have e3 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app
      (injectiveResolution F).cocomplex) 1) x
  exact e1.trans (e2.trans e3)

/-- **The connecting map on Čech classes.** For a short exact sequence `0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0`
and a global section `s` of `S₃`, lift `s` locally to a Čech `0`-cochain `e` of `S₂`; the
Čech `1`-cocycle `ω` of `S₁` with `f ω = δ e` has as `Ext¹` class the image of `s` under the
extension class of the sequence. -/
private theorem sheafCohomologyOneExtEquiv_cechClass_eq_comp_extClass {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
    (s : @Quiver.Hom (TopCat.Sheaf AddCommGrpCat.{0} X) _ (Stacks.SupportedVanishing.constZ X) S.X₃)
    {I : Type} (Ui : I → Opens X) (hUi : (⊤ : Opens X) = ⨆ i, Ui i)
    (e : CechCochains.Cochain Ui S.X₂.presheaf 0)
    (he : ∀ i : Fin 1 → I, S.g.hom.app (op (CechCochains.inter Ui i)) (e i) =
      S.X₃.presheaf.map (homOfLE le_top).op (Stacks.SupportedVanishing.homConstAddEquiv S.X₃ s))
    (ω : CechCochains.cocycles1 Ui S.X₁.presheaf)
    (hω : ∀ i : Fin 2 → I, S.f.hom.app (op (CechCochains.inter Ui i)) (ω.val i) =
      CechCochains.cechD Ui S.X₂.presheaf 0 e i) :
    (Stacks.Thickenings.sheafCohomologyOneExtEquiv X S.X₁).hom
        (cechH1ToRightDerivedSections X ⊤ Ui hUi S.X₁ (CechCochains.cls Ui S.X₁.presheaf ω)) =
      (Ext.mk₀ s).comp hS.extClass (zero_add 1) := by
  classical
  have := hS.mono_f
  have := hS.epi_g
  let J := injectiveResolution S.X₁
  let ι0 : S.X₁ ⟶ J.cocomplex.X 0 :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 S.X₁).inv ≫ J.ι.f 0
  have hι0d : ι0 ≫ J.cocomplex.d 0 1 = 0 := by
    simp only [ι0, Category.assoc, InjectiveResolution.ι_f_zero_comp_complex_d, comp_zero]
  let β : S.X₂ ⟶ J.cocomplex.X 0 := Injective.factorThru ι0 S.f
  have hβ : S.f ≫ β = ι0 := Injective.comp_factorThru _ _
  have w1 : S.f ≫ (β ≫ J.cocomplex.d 0 1) = 0 := by rw [← Category.assoc, hβ, hι0d]
  let γ : S.X₃ ⟶ J.cocomplex.X 1 := hS.gIsCokernel.desc (CokernelCofork.ofπ _ w1)
  have hγ : S.g ≫ γ = β ≫ J.cocomplex.d 0 1 := hS.gIsCokernel.fac _ WalkingParallelPair.one
  have hγd : γ ≫ J.cocomplex.d 1 2 = 0 := by
    rw [← cancel_epi S.g, reassoc_of% hγ, HomologicalComplex.d_comp_d, comp_zero, comp_zero]
  -- the Ext side
  have hmono : Mono ι0 := mono_comp _ _
  let T := ShortComplex.mk ι0 (cokernel.π ι0) (cokernel.condition _)
  have hT : T.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  let j : cokernel ι0 ⟶ J.cocomplex.X 1 := cokernel.desc _ _ hι0d
  have hj : cokernel.π ι0 ≫ j = J.cocomplex.d 0 1 := cokernel.π_desc _ _ _
  have hTJ := extClass_eq_extMk J (cokernel.π ι0) (cokernel.condition _) hT j hj
  have w2 : S.f ≫ (β ≫ cokernel.π ι0) = 0 := by
    rw [← Category.assoc, hβ, cokernel.condition]
  let τ₃ : S.X₃ ⟶ cokernel ι0 := hS.gIsCokernel.desc (CokernelCofork.ofπ _ w2)
  have hτ₃ : S.g ≫ τ₃ = β ≫ cokernel.π ι0 := hS.gIsCokernel.fac _ WalkingParallelPair.one
  have hτj : τ₃ ≫ j = γ := by
    rw [← cancel_epi S.g, reassoc_of% hτ₃, hj, hγ]
  let fST : S ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := β
      τ₃ := τ₃
      comm₁₂ := by simpa [T] using hβ.symm
      comm₂₃ := hτ₃.symm }
  have hnat := hS.extClass_naturality hT fST
  rw [show fST.τ₁ = 𝟙 _ from rfl, Ext.comp_mk₀_id] at hnat
  have hR : (Ext.mk₀ s).comp hS.extClass (zero_add 1) =
      J.extMk (-(s ≫ γ)) 2 rfl (by
        rw [Preadditive.neg_comp, Category.assoc, neg_eq_zero, hγd, comp_zero]) := by
    rw [hnat, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hTJ,
      InjectiveResolution.mk₀_comp_extMk]
    congr 1
    rw [Preadditive.comp_neg, Category.assoc, hτj]
  rw [hR]
  -- the Čech side: an injective-resolution representative of `ω`
  set t := Stacks.SupportedVanishing.homConstAddEquiv S.X₃ s with ht
  have hcyc : ConcreteCategory.hom ((abelianResolutionSections X ⊤ J).d 1 (1 + 1))
      (-(γ.hom.app (op ⊤) t)) = 0 := by
    rw [map_neg, neg_eq_zero, abelianResolutionSections_d_apply]
    exact sheaf_comp_app_apply_eq_zero X γ (J.cocomplex.d 1 2) hγd ⊤ t
  let r : CechOneResolutionRepresentative X ⊤ Ui hUi S.X₁ J ω :=
    { b := push Ui β.hom 0 e
      cycle := mkCycles (abelianResolutionSections X ⊤ J) 1 (-(γ.hom.app (op ⊤) t)) hcyc
      coboundary := fun i => by
        rw [← push_cechD, push_apply, ← hω i]
        exact (sheaf_comp_app_apply_congr X S.f β (𝟙 _) ι0 (by rw [hβ, Category.id_comp]) _ _)
      restriction := fun i => by
        rw [iCycles_mkCycles, map_neg, push_apply]
        congr 1
        refine (restr_app γ.hom _ t).trans ?_
        change γ.hom.app _ (S.X₃.presheaf.map (homOfLE le_top).op t) = _
        rw [← he i]
        exact sheaf_comp_app_apply_congr X S.g γ β (J.cocomplex.d 0 1) hγ _ _ }
  rw [cechH1ToRightDerivedSections_apply X ⊤ Ui hUi S.X₁ J ω r]
  refine (sheafCohomologyOneExtEquiv_resolutionClass S.X₁ r.cycle).trans ?_
  congr 1
  have e1 : (abelianResolutionSections X ⊤ J).iCycles 1 r.cycle = -(γ.hom.app (op ⊤) t) :=
    iCycles_mkCycles _ _ _ hcyc
  have e2 := Stacks.SupportedVanishing.homConstAddEquiv_comp (B := S.X₃) (B' := J.cocomplex.X 1)
    s γ
  change (Stacks.Thickenings.sectionsCoyonedaIso X).inv.app _
    ((abelianResolutionSections X ⊤ J).iCycles 1 r.cycle) = _
  rw [e1, map_neg, ← e2]
  congr 1
  have key := Iso.hom_inv_id_app_apply (Stacks.Thickenings.sectionsCoyonedaIso X) (J.cocomplex.X 1)
  exact key _

end CechConnecting

noncomputable section Kappa

open CategoryTheory.Abelian Stacks.SupportedVanishing MMP
  MMP.SingularChain MMP.SingularChain MMP.SingularCochain MMP.SingularCochain

attribute [local instance] CategoryTheory.hasExt_of_enoughInjectives

variable {M : TopCat.{0}}

/-- Evaluation of `0`-cochains at points, on presheaves. -/
private def evP : singCochainTerm Zc M 0 ⟶ (funSheaf M ℂ).obj where
  app V := AddCommGrpCat.ofHom
    { toFun := fun φ x =>
        ((fnEquiv Zc ((Opens.toTopCat M).obj V.unop) 0 φ (ContinuousMap.const _ x) : ℤ) : ℂ)
      map_zero' := by
        funext x
        erw [fnEquiv_zero]
        simp only [Pi.zero_apply, Int.cast_zero]
      map_add' := fun φ ψ => by
        funext x
        erw [fnEquiv_add]
        simp only [Pi.add_apply, Int.cast_add] }
  naturality V W i := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ => funext fun x => ?_)
    exact congrArg (fun n : ℤ => (n : ℂ))
      (fnEquiv_map Zc ((Opens.toTopCat M).map i.unop) 0 φ (ContinuousMap.const _ x))

private lemma evP_app (V : (Opens M)ᵒᵖ) (φ : (singCochainTerm Zc M 0).obj V) (x : V.unop) :
    (evP.app V φ : V.unop → ℂ) x =
      ((fnEquiv Zc ((Opens.toTopCat M).obj V.unop) 0 φ (ContinuousMap.const _ x) : ℤ) : ℂ) := rfl

private lemma fnEquiv_constCochain (Y : TopCat.{0}) (n : ℤ) (τ : Sx Y 0) :
    fnEquiv Zc Y 0 (constCochain Zc Y n) τ = n := by
  rw [fnEquiv_apply, cochainEval_constCochain]

private lemma evP_reprFn (V : Opens M) (g : Sx M 0 → ℤ) (x : V) :
    (evP.app (op V) (reprFn Zc M 0 V g) : V → ℂ) x = (g (ContinuousMap.const _ x.1) : ℂ) := by
  change ((fnEquiv Zc _ 0 ((fnEquiv Zc _ 0).symm _) _ : ℤ) : ℂ) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Evaluation `𝒮⁰ ⟶ ℂ^M` of `0`-cochains at points. -/
private def ev0 : (KS M).X 0 ⟶ funSheaf M ℂ :=
  ((sheafificationAdjunction (Opens.grothendieckTopology M) AddCommGrpCat.{0}).homEquiv
    (singCochainTerm Zc M 0) (funSheaf M ℂ)).symm evP

private lemma unit_ev0 : unitNat (singCochainTerm Zc M 0) ≫ (ev0 (M := M)).hom = evP :=
  ((sheafificationAdjunction (Opens.grothendieckTopology M) AddCommGrpCat.{0}).homEquiv_unit
    _ _ ev0).symm.trans (Equiv.apply_symm_apply _ evP)

private lemma ev0_unit_reprFn (V : Opens M) (g : Sx M 0 → ℤ) (x : V) :
    (ev0.hom.app (op V) ((unitNat (singCochainTerm Zc M 0)).app (op V) (reprFn Zc M 0 V g)) :
      V → ℂ) x = (g (ContinuousMap.const _ x.1) : ℂ) := by
  rw [← evP_reprFn, ← unit_ev0]
  rfl

private lemma aug0_ev0 : aug0 M ≫ ev0 = constFun M := by
  let J := Opens.grothendieckTopology M
  let adj1 := constantPresheafAdj AddCommGrpCat.{0} (isTerminalTop : IsTerminal (⊤ : Opens M))
  let adj2 := sheafificationAdjunction J AddCommGrpCat.{0}
  let c : (Functor.const (Opens M)ᵒᵖ).obj (AddCommGrpCat.of ℤ) ⟶ (funSheaf M ℂ).obj :=
    (adj1.homEquiv (AddCommGrpCat.of ℤ) (funSheaf M ℂ).obj).symm (constGlobal M)
  have hc : constFun M = (adj2.homEquiv _ _).symm c := by
    have := congrArg (fun F => (F (AddCommGrpCat.of ℤ) (funSheaf M ℂ)).symm (constGlobal M))
      (Adjunction.comp_homEquiv adj1 adj2)
    exact this
  have h1 : aug0 M ≫ ev0 = (adj2.homEquiv _ _).symm (constToCochain Zc M ≫ evP) :=
    (adj2.homEquiv_naturality_left_symm (Y := funSheaf M ℂ) (constToCochain Zc M) (evP (M := M))).symm
  have h2 : constToCochain Zc M ≫ evP = c := by
    refine NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun n =>
      funext fun x => ?_))
    have e1 : ∀ m : ℤ, (c.app U m : U.unop → ℂ) x = (m : ℂ) := fun m => rfl
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply]
    erw [evP_app]
    refine Eq.trans ?_ (e1 n).symm
    exact congrArg (fun m : ℤ => (m : ℂ)) (fnEquiv_constCochain _ n _)
  rw [hc, h1, h2]

variable (hM : LocallyContractibleSpace M)

private lemma aug0_ev0_π : aug0 M ≫ ev0 ≫ cokernel.π (constFun M) = 0 := by
  rw [← Category.assoc, aug0_ev0, cokernel.condition]

/-- The map `Z¹ ⟶ ℂ^M / ℤ_M` induced by evaluation. -/
private def kappa : Z1 M ⟶ quotSheaf M :=
  (S1_shortExact hM).gIsCokernel.desc (CokernelCofork.ofπ _ (aug0_ev0_π (M := M)))

private lemma g1_kappa : g1 M ≫ kappa hM = ev0 ≫ cokernel.π (constFun M) :=
  (S1_shortExact hM).gIsCokernel.fac _ WalkingParallelPair.one

private lemma extClass_S1 : (S1_shortExact hM).extClass =
    (Ext.mk₀ (kappa hM)).comp (quotSeq_shortExact M).extClass (zero_add 1) := by
  let f : S1 M ⟶ ShortComplex.mk (constFun M) (cokernel.π (constFun M)) (cokernel.condition _) :=
    { τ₁ := 𝟙 _
      τ₂ := ev0
      τ₃ := kappa hM
      comm₁₂ := (Category.id_comp _).trans aug0_ev0.symm
      comm₂₃ := (g1_kappa hM).symm }
  have h := (S1_shortExact hM).extClass_naturality (quotSeq_shortExact M) f
  rw [show f.τ₁ = 𝟙 _ from rfl, Ext.comp_mk₀_id] at h
  exact h

private lemma psi_eq_comp (z : Sx M 2 → ℤ) (hz : cob 2 z = 0) :
    psi hM z hz = (((Ext.mk₀ (zhat z hz)).comp (S2_shortExact hM).extClass (zero_add 1)).comp
      (Ext.mk₀ (kappa hM)) (add_zero 1)).comp (quotSeq_shortExact M).extClass
        (show 1 + 1 = 2 from rfl) := by
  rw [psi, extClass_S1, Ext.comp_assoc_of_second_deg_zero]

end Kappa

noncomputable section Kappa2

open CategoryTheory.Abelian Stacks.SupportedVanishing MMP
  MMP.SingularChain MMP.SingularChain MMP.SingularCochain MMP.SingularCochain

attribute [local instance] CategoryTheory.hasExt_of_enoughInjectives

variable {M : TopCat.{0}}

/-- The local section of `𝒮^p` over `V` of a singular cochain. -/
private abbrev locS (p : ℕ) (V : Opens M) (g : Sx M p → ℤ) : ToType (((KS M).X p).obj.obj (op V)) :=
  (unitNat (singCochainTerm Zc M p)).app (op V) (reprFn Zc M p V g)

private lemma locS_res (p : ℕ) {V W : Opens M} (h : W ≤ V) (g : Sx M p → ℤ) :
    ((KS M).X p).obj.map (homOfLE h).op (locS p V g) = locS p W g := by
  refine (ConcreteCategory.congr_hom ((unitNat (singCochainTerm Zc M p)).naturality
    (homOfLE h).op) _).symm.trans ?_
  exact congrArg _ (reprFn_res Zc M p h g)

private lemma locS_sub (p : ℕ) (V : Opens M) (g g' : Sx M p → ℤ) :
    locS p V (g - g') = locS p V g - locS p V g' := by
  simp only [locS]
  erw [reprFn_sub]
  exact map_sub _ _ _

private lemma locS_zero (p : ℕ) (V : Opens M) : locS (M := M) p V 0 = 0 := by
  simp only [locS]
  erw [reprFn_zero]
  exact map_zero _

private lemma locS_congr (p : ℕ) (V : Opens M) {g g' : Sx M p → ℤ}
    (h : ∀ t : Sx M p, Set.range t ⊆ V → g t = g' t) : locS p V g = locS p V g' := by
  simp only [locS]
  rw [(reprFn_eq Zc M p V g g').2 h]

private lemma KS_d_eq (p : ℕ) : (KS M).d p (p + 1) =
    (presheafToSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).map
      (singCochainTermD Zc M p) :=
  congrArg (presheafToSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).map
    (show (singCochainPresheafComplex Zc M).d p (p + 1) = singCochainTermD Zc M p from
      CochainComplex.of_d _ _ _)

private lemma KS_d_locS (p : ℕ) (V : Opens M) (g : Sx M p → ℤ) :
    ((KS M).d p (p + 1)).hom.app (op V) (locS p V g) = locS (p + 1) V (cob p g) := by
  rw [KS_d_eq]
  have h := (sheafificationAdjunction (Opens.grothendieckTopology M) AddCommGrpCat.{0}).unit.naturality
    (singCochainTermD Zc M p)
  have h2 := ConcreteCategory.congr_hom (congrArg (fun t => t.app (op V)) h) (reprFn Zc M p V g)
  refine h2.symm.trans ?_
  exact congrArg _ (reprFn_d Zc M p V g)

private lemma app_injective {F G : Sh M} (f : F ⟶ G) [Mono f] (U : Opens M) :
    Function.Injective (f.hom.app (op U)) := by
  have : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance

private lemma comp_app_apply {F G H : Sh M} (f : F ⟶ G) (g : G ⟶ H) (U : Opens M)
    (x : ToType (F.obj.obj (op U))) :
    (f ≫ g).hom.app (op U) x = g.hom.app (op U) (f.hom.app (op U) x) := rfl

private lemma hom_app_map {F G : Sh M} (f : F ⟶ G) {V W : Opens M} (h : W ≤ V)
    (x : ToType (F.obj.obj (op V))) :
    f.hom.app (op W) (F.obj.map (homOfLE h).op x) = G.obj.map (homOfLE h).op (f.hom.app (op V) x) :=
  ConcreteCategory.congr_hom (f.hom.naturality (homOfLE h).op) x

private lemma cechD_zero_apply {F : TopCat.Presheaf AddCommGrpCat.{0} M} {I : Type}
    (Ui : I → Opens M) (e : CechCochains.Cochain Ui F 0) (i : Fin 2 → I) :
    CechCochains.cechD Ui F 0 e i =
      CechCochains.restr F (CechCochains.inter_le_omit Ui i 0) (e (i ∘ (0 : Fin 2).succAbove)) -
      CechCochains.restr F (CechCochains.inter_le_omit Ui i 1) (e (i ∘ (1 : Fin 2).succAbove)) := by
  change ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • CechCochains.restr _ _ (e (i ∘ j.succAbove)) = _
  rw [Fin.sum_univ_two]
  simp [sub_eq_add_neg]

variable (hM : LocallyContractibleSpace M)

/-- **The class of a singular `2`-cocycle is the Čech class of its integer primitives.** -/
private theorem psi_eq_quotExtClass [MetrizableSpace M] (z : Sx M 2 → ℤ) (hz : cob 2 z = 0)
    {I : Type} (Ui : I → Opens M) (hUi : (⊤ : Opens M) = ⨆ i, Ui i) (w : I → Sx M 1 → ℤ)
    (hw : ∀ i (σ : Sx M 2), Set.range σ ⊆ Ui i → z σ = coboundary ℤ 1 (w i) σ)
    (c : CechCochains.cocycles1 Ui (quotSheaf M).obj) (hc : IsKappaCocycle Ui w c) :
    psi hM z hz = quotExtClass M Ui hUi c := by
  classical
  have hwc : ∀ i (V : Opens M), V ≤ Ui i → ∀ σ : Sx M 2, Set.range σ ⊆ V → cob 1 (w i) σ = z σ :=
    fun i V hV σ hσ => by rw [cob_eq_coboundary, hw i σ (hσ.trans hV)]
  have hinter : ∀ {p : ℕ} (i : Fin p → I) (k : Fin p), CechCochains.inter Ui i ≤ Ui (i k) :=
    fun i k => iInf_le (fun k => Ui (i k)) k
  -- the local lifts of the class of `z`
  let e : CechCochains.Cochain Ui ((KS M).X 1).obj 0 := fun i =>
    locS 1 (CechCochains.inter Ui i) (w (i 0))
  have he : ∀ i : Fin 1 → I, (g2 M).hom.app (op (CechCochains.inter Ui i)) (e i) =
      (Z2 M).obj.map (homOfLE le_top).op (homConstAddEquiv (Z2 M) (zhat z hz)) := by
    intro i
    apply app_injective (kernel.ι ((KS M).d 2 3))
    have h1 : (kernel.ι ((KS M).d 2 3)).hom.app (op ⊤) (homConstAddEquiv (Z2 M) (zhat z hz)) =
        locS 2 ⊤ z := by
      rw [← homConstAddEquiv_comp, zhat_ι, homConstAddEquiv_epsH]
      rfl
    rw [← comp_app_apply, g2_ι, KS_d_locS]
    erw [hom_app_map, h1, locS_res]
    exact locS_congr 2 _ (hwc (i 0) _ (hinter i 0))
  have hx : ∀ i : Fin 2 → I, CechCochains.cechD Ui _ 0 e i =
      locS 1 (CechCochains.inter Ui i) (w (i 1) - w (i 0)) := by
    intro i
    rw [cechD_zero_apply, locS_sub]
    simp only [CechCochains.restr, e]
    erw [locS_res, locS_res]
    rfl
  have hgx : ∀ i : Fin 2 → I,
      (g2 M).hom.app (op (CechCochains.inter Ui i)) (CechCochains.cechD Ui _ 0 e i) = 0 := by
    intro i
    apply app_injective (kernel.ι ((KS M).d 2 3))
    rw [← comp_app_apply, g2_ι, hx, map_zero, KS_d_locS, ← locS_zero 2 (CechCochains.inter Ui i)]
    refine locS_congr 2 _ fun t ht => ?_
    rw [cob_sub (A := Zc), Pi.sub_apply, hwc (i 1) _ (hinter i 1) t ht, hwc (i 0) _ (hinter i 0) t ht,
      sub_self]
    rfl
  have hex : ∀ i : Fin 2 → I, ∃ t, (kernel.ι ((KS M).d 1 2)).hom.app (op (CechCochains.inter Ui i)) t =
      CechCochains.cechD Ui _ 0 e i :=
    fun i => TopCat.Sheaf.sections_exact_of_left_exact (S := S2 M) (S2_shortExact hM).exact
      (S2_shortExact hM).mono_f _ (hgx i)
  choose ω' hω' using hex
  have hωcoc : ω' ∈ CechCochains.cocycles1 Ui (Z1 M).obj := by
    refine (CechCochains.mem_cocycles1_iff _ _ _).2 ?_
    funext i
    apply app_injective (kernel.ι ((KS M).d 1 2))
    have hpush : Stacks.Cohomology.CechOne.push Ui (kernel.ι ((KS M).d 1 2)).hom 1 ω' =
        CechCochains.cechD Ui _ 0 e :=
      funext fun i => (Stacks.Cohomology.CechOne.push_apply (P := (Z1 M).obj) Ui _ 1 ω' i).trans
        (hω' i)
    have h := congrArg (fun f => f i)
      (Stacks.Cohomology.CechOne.push_cechD Ui (kernel.ι ((KS M).d 1 2)).hom 1 ω')
    simp only [Stacks.Cohomology.CechOne.push_apply] at h
    erw [h, hpush, CechCochains.cechD_cechD]
    exact (map_zero _).symm
  let ω : CechCochains.cocycles1 Ui (Z1 M).obj := ⟨ω', hωcoc⟩
  have hκω : ∀ i : Fin 2 → I,
      c.1 i = (kappa hM).hom.app (op (CechCochains.inter Ui i)) (ω.1 i) := by
    intro i
    refine TopCat.Presheaf.section_ext (quotSheaf M) _ _ _ fun y hy => ?_
    obtain ⟨V, hV, hyV, a, ha_edge, ha_c⟩ := hc i y hy
    rw [← TopCat.Presheaf.germ_res_apply (quotSheaf M).obj (homOfLE hV) y hyV,
      ← TopCat.Presheaf.germ_res_apply (quotSheaf M).obj (homOfLE hV) y hyV]
    congr 1
    let a' : Sx M 0 → ℤ := fun σ => if h : σ (stdSimplex.vertex 0) ∈ V then a ⟨_, h⟩ else 0
    have ha' : ∀ (σ : Sx M 0) (p : V), σ (stdSimplex.vertex 0) = p.1 → a' σ = a p := by
      intro σ p hp
      simp only [a']
      rw [dif_pos (by rw [hp]; exact p.2)]
      exact congrArg a (Subtype.ext hp)
    have hω_V : (Z1 M).obj.map (homOfLE hV).op (ω' i) = (g1 M).hom.app (op V) (locS 0 V a') := by
      apply app_injective (kernel.ι ((KS M).d 1 2))
      erw [hom_app_map, hω', hx, locS_res]
      rw [← comp_app_apply, g1_ι, KS_d_locS]
      refine locS_congr 1 V fun τ hτ => ?_
      rw [Pi.sub_apply, ha_edge τ hτ]
      show _ = ∑ k : Fin 2, ((-1 : ℤ) ^ (k : ℕ)) • a' (τ.comp (face 0 k))
      rw [Fin.sum_univ_two, ha' (τ.comp (face 0 0)) ⟨_, hτ ⟨stdSimplex.vertex 1, rfl⟩⟩
        (by rw [ContinuousMap.comp_apply, face00_vertex]),
        ha' (τ.comp (face 0 1)) ⟨_, hτ ⟨stdSimplex.vertex 0, rfl⟩⟩
        (by rw [ContinuousMap.comp_apply, face01_vertex])]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
      rw [sub_eq_add_neg]
    erw [ha_c, ← hom_app_map (kappa hM)]
    erw [hω_V]
    rw [← comp_app_apply, g1_kappa, comp_app_apply]
    congr 1
    funext y
    erw [ev0_unit_reprFn]
    exact congrArg (fun m : ℤ => (m : ℂ)) (ha' _ y rfl).symm
  have hcrux : (Ext.mk₀ (zhat z hz)).comp (S2_shortExact hM).extClass (zero_add 1) =
      (Stacks.Thickenings.sheafCohomologyOneExtEquiv M (Z1 M)).hom
        (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections M ⊤ Ui hUi (Z1 M)
          (CechCochains.cls Ui (Z1 M).obj ω)) :=
    (sheafCohomologyOneExtEquiv_cechClass_eq_comp_extClass (S2_shortExact hM) (zhat z hz) Ui hUi e he ω hω').symm
  have hn := sheafCohomologyOneExtEquiv_naturality (kappa hM)
    (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections M ⊤ Ui hUi (Z1 M)
      (CechCochains.cls Ui (Z1 M).obj ω))
  have hc2 := Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections_naturality M ⊤ Ui hUi
    (kappa hM) ω c hκω
  rw [psi_eq_comp, hcrux]
  erw [hn, hc2]
  rfl

end Kappa2

noncomputable section NatZ

open CategoryTheory.Abelian Stacks.SupportedVanishing MMP
  MMP.SingularChain MMP.SingularChain MMP.SingularCochain MMP.SingularCochain

attribute [local instance] CategoryTheory.hasExt_of_enoughInjectives

variable {W Z : TopCat.{0}} (f : Z ⟶ W)

/-- The comparison `ℤ_Z ⟶ f⁻¹ ℤ_W` of the statement. -/
private def alphaC (A : AddCommGrpCat.{0}) :
    (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj A ⟶
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj
        ((constantSheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0}).obj A) :=
  ((constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0} isTerminalTop).homEquiv A _).symm
    ((constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0} isTerminalTop).unit.app A ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app
        ((constantSheaf _ _).obj A)).hom.app (op ⊤))

private lemma homEquiv_alphaC (A : AddCommGrpCat.{0}) :
    (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0} isTerminalTop).homEquiv A _
      (alphaC f A) =
    (constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0} isTerminalTop).unit.app A ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app
        ((constantSheaf _ _).obj A)).hom.app (op ⊤) :=
  Equiv.apply_symm_apply _ _

private lemma restr_top_eq_id (A : AddCommGrpCat.{0}) :
    (constSheaf A Z).obj.map (homOfLE le_top : (Opens.map f).obj ⊤ ⟶ ⊤).op = 𝟙 _ := by
  ext x
  exact map_homOfLE_top f A x

private lemma constPt_thetaF' (A : AddCommGrpCat.{0}) :
    constPt A W ≫ (globalSections W).map (thetaF f A) = constPt A Z :=
  (constPt_thetaF f A).trans (by rw [restr_top_eq_id]; exact Category.comp_id _)

private lemma compHomEquiv_eq (A : AddCommGrpCat.{0}) (G : TopCat.Sheaf AddCommGrpCat.{0} Z)
    (u : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj (constSheaf A W) ⟶ G) :
    ((constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0} isTerminalTop).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)).homEquiv A G u =
      constPt A W ≫ (globalSections W).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app (constSheaf A W) ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map u) := by
  erw [Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply, Adjunction.homEquiv_unit]
  rfl

private lemma toConstDef_alphaC (A : AddCommGrpCat.{0}) : toConstDef f A ≫ alphaC f A = 𝟙 _ := by
  apply (((constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0} isTerminalTop).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)).homEquiv _ _).injective
  rw [compHomEquiv_eq, compHomEquiv_eq]
  have hα : constPt A Z ≫ ((sheafSections (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj
      (op ⊤)).map (alphaC f A) = constPt A W ≫ (globalSections W).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app
          (constSheaf A W)) :=
    (((constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0}
      isTerminalTop).homEquiv_unit _ _ _).symm.trans (homEquiv_alphaC f A))
  have h1 : constPt A W ≫ (globalSections W).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app (constSheaf A W) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (toConstDef f A ≫ alphaC f A)) =
      (constPt A W ≫ (globalSections W).map (thetaF f A)) ≫
        (globalSections W).map ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (alphaC f A)) := by
    simp only [Functor.map_comp, Category.assoc, thetaF]
    erw [Functor.map_comp (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f) (toConstDef f A)
      (alphaC f A), Functor.map_comp]
  rw [h1, constPt_thetaF']
  refine hα.trans ?_
  rw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

/-- The pullback functor on sheaves of abelian groups, on `Sheaf J`. -/
private def pullbackFun : Sh W ⥤ Sh Z := TopCat.Sheaf.pullback AddCommGrpCat.{0} f

/-- The pushforward functor on sheaves of abelian groups, on `Sheaf J`. -/
private def pushforwardFun : Sh Z ⥤ Sh W := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f

private def adjp : pullbackFun f ⊣ pushforwardFun f := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f

private lemma pullbackFun_additive : (pullbackFun f).Additive :=
  inferInstanceAs (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).Additive

private lemma pullbackFun_preservesFiniteLimits : PreservesFiniteLimits (pullbackFun f) :=
  inferInstanceAs (PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f))

private lemma pullbackFun_preservesFiniteColimits : PreservesFiniteColimits (pullbackFun f) :=
  inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f))

/-- The comparison `f⁻¹ 𝒮_W^p ⟶ 𝒮_Z^p`, adjoint to `thetaKf`. -/
private def thetaL (p : ℕ) : (pullbackFun f).obj ((KS W).X p) ⟶ (KS Z).X p :=
  ((adjp f).homEquiv _ _).symm (thetaKf Zc f p)

private lemma homEquiv_thetaL (p : ℕ) :
    (adjp f).homEquiv _ _ (thetaL f p) = thetaKf Zc f p :=
  Equiv.apply_symm_apply _ _

private lemma thetaL_d (p q : ℕ) (hpq : p + 1 = q) :
    (pullbackFun f).map ((KS W).d p q) ≫ thetaL f q = thetaL f p ≫ (KS Z).d p q := by
  subst hpq
  apply ((adjp f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, homEquiv_thetaL,
    homEquiv_thetaL]
  exact ((thetaK Zc f).comm p (p + 1)).symm

private lemma Fι_θ_d (p : ℕ) :
    ((pullbackFun f).map (kernel.ι ((KS W).d (p + 1) (p + 2))) ≫ thetaL f (p + 1)) ≫
      (KS Z).d (p + 1) (p + 2) = 0 := by
  haveI := pullbackFun_additive f
  rw [Category.assoc, ← thetaL_d f (p + 1) (p + 2) rfl, ← Category.assoc, ← Functor.map_comp,
    kernel.condition, Functor.map_zero, zero_comp]

/-- The induced map on `1`-cocycles. -/
private def thetaZ1 : (pullbackFun f).obj (Z1 W) ⟶ Z1 Z := kernel.lift _ _ (Fι_θ_d f 0)

/-- The induced map on `2`-cocycles. -/
private def thetaZ2 : (pullbackFun f).obj (Z2 W) ⟶ Z2 Z := kernel.lift _ _ (Fι_θ_d f 1)

private lemma thetaZ1_ι : thetaZ1 f ≫ kernel.ι ((KS Z).d 1 2) =
    (pullbackFun f).map (kernel.ι ((KS W).d 1 2)) ≫ thetaL f 1 :=
  kernel.lift_ι _ _ _

private lemma thetaZ2_ι : thetaZ2 f ≫ kernel.ι ((KS Z).d 2 3) =
    (pullbackFun f).map (kernel.ι ((KS W).d 2 3)) ≫ thetaL f 2 :=
  kernel.lift_ι _ _ _

/-- The comparison `f⁻¹ ℤ_W ⟶ ℤ_Z`, on `Sheaf J`. -/
private def toConstZ : (pullbackFun f).obj (ZM W) ⟶ ZM Z := toConstDef f Zc

private lemma homEquiv_toConstZ : (adjp f).homEquiv _ _ (toConstZ f) = thetaF f Zc :=
  Adjunction.homEquiv_unit _ _ _ _

private lemma aug0_thetaKf : aug0 W ≫ thetaKf Zc f 0 = thetaF f Zc ≫ (pushforwardFun f).map (aug0 Z) :=
  constAugDeg0_theta f Zc

/-- The pullback of `0 ⟶ ℤ ⟶ 𝒮⁰ ⟶ Z¹ ⟶ 0` maps to the sequence on `Z`. -/
private def mapS1 : haveI := pullbackFun_additive f; (S1 W).map (pullbackFun f) ⟶ S1 Z :=
  haveI := pullbackFun_additive f
  { τ₁ := toConstZ f
    τ₂ := thetaL f 0
    τ₃ := thetaZ1 f
    comm₁₂ := by
      apply ((adjp f).homEquiv _ _).injective
      change (adjp f).homEquiv _ _ (toConstZ f ≫ aug0 Z) =
        (adjp f).homEquiv _ _ ((pullbackFun f).map (aug0 W) ≫ thetaL f 0)
      rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
        homEquiv_toConstZ, homEquiv_thetaL]
      exact (aug0_thetaKf f).symm
    comm₂₃ := by
      change thetaL f 0 ≫ g1 Z = (pullbackFun f).map (g1 W) ≫ thetaZ1 f
      rw [← cancel_mono (kernel.ι ((KS Z).d 1 2)), Category.assoc, Category.assoc, thetaZ1_ι, g1_ι,
        ← Category.assoc, ← Functor.map_comp, g1_ι]
      exact (thetaL_d f 0 1 rfl).symm }

/-- The pullback of `0 ⟶ Z¹ ⟶ 𝒮¹ ⟶ Z² ⟶ 0` maps to the sequence on `Z`. -/
private def mapS2 : haveI := pullbackFun_additive f; (S2 W).map (pullbackFun f) ⟶ S2 Z :=
  haveI := pullbackFun_additive f
  { τ₁ := thetaZ1 f
    τ₂ := thetaL f 1
    τ₃ := thetaZ2 f
    comm₁₂ := thetaZ1_ι f
    comm₂₃ := by
      change thetaL f 1 ≫ g2 Z = (pullbackFun f).map (g2 W) ≫ thetaZ2 f
      rw [← cancel_mono (kernel.ι ((KS Z).d 2 3)), Category.assoc, Category.assoc, thetaZ2_ι, g2_ι,
        ← Category.assoc, ← Functor.map_comp, g2_ι]
      exact (thetaL_d f 1 2 rfl).symm }

/-- The comparison `ℤ_Z ⟶ f⁻¹ ℤ_W` of the statement, on `Sheaf J`. -/
private def alphaZ (A : AddCommGrpCat.{0}) :
    (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj A ⟶
      (pullbackFun f).obj ((constantSheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0}).obj A) :=
  alphaC f A

private lemma toConstZ_alphaZ : toConstZ f ≫ alphaZ f Zc = 𝟙 _ := toConstDef_alphaC f Zc

private lemma homConst_alphaZ {G : Sh Z} (g : (pullbackFun f).obj (constZ W) ⟶ G) :
    homConstAddEquiv G (alphaZ f (AddCommGrpCat.of (ULift ℤ)) ≫ g) =
      homConstAddEquiv ((pushforwardFun f).obj G) ((adjp f).homEquiv _ _ g) := by
  have h : (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0} isTerminalTop).homEquiv
      _ G (alphaZ f (AddCommGrpCat.of (ULift ℤ)) ≫ g) =
      (constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0} isTerminalTop).homEquiv
        _ ((pushforwardFun f).obj G) ((adjp f).homEquiv _ _ g) := by
    rw [Adjunction.homEquiv_naturality_right]
    erw [homEquiv_alphaC]
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    rfl
  change (((sheafSections _ _).obj (op ⊤)).obj G).uliftZMultiplesAddEquiv
      ((constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0} isTerminalTop).homAddEquiv
        _ G (alphaZ f (AddCommGrpCat.of (ULift ℤ)) ≫ g)) =
    (((sheafSections _ _).obj (op ⊤)).obj ((pushforwardFun f).obj G)).uliftZMultiplesAddEquiv
      ((constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0} isTerminalTop).homAddEquiv
        _ ((pushforwardFun f).obj G) ((adjp f).homEquiv _ _ g))
  rw [Adjunction.homAddEquiv_apply, Adjunction.homAddEquiv_apply, h]
  rfl

private lemma thetaP_reprFn (p : ℕ) (g : Sx W p → ℤ) :
    (thetaP Zc f p).app (op ⊤) (reprFn Zc W p ⊤ g) =
      reprFn Zc Z p ⊤ (fun τ => g (f.hom.comp τ)) := by
  apply (fnEquiv Zc ((Opens.toTopCat Z).obj ⊤) p).injective
  funext τ
  have h1 := fnEquiv_map Zc (fRes f ⊤) p (reprFn Zc W p ⊤ g) τ
  erw [h1]
  simp only [reprFn, Equiv.apply_symm_apply]
  rfl

private lemma thetaKf_epsG (p : ℕ) (g : Sx W p → ℤ) :
    (thetaKf Zc f p).hom.app (op ⊤) (epsG p g) = epsG p (fun τ => g (f.hom.comp τ)) := by
  have hθ := ConcreteCategory.congr_hom (congrArg (fun t => t.app (op ⊤)) (thetaKf_unit Zc f p))
    (reprFn Zc W p ⊤ g)
  change (thetaKf Zc f p).hom.app (op ⊤) ((unitNat (singCochainTerm Zc W p)).app (op ⊤)
    (reprFn Zc W p ⊤ g)) = _
  erw [hθ]
  exact congrArg (fun x => (unitNat (singCochainTerm Zc Z p)).app (op ⊤) x) (thetaP_reprFn f p g)

private lemma zhat_nat (z : Sx W 2 → ℤ) (hz : cob 2 z = 0)
    (hz' : cob 2 (fun τ : Sx Z 2 => z (f.hom.comp τ)) = 0) :
    alphaZ f (AddCommGrpCat.of (ULift ℤ)) ≫ (pullbackFun f).map (zhat z hz) ≫ thetaZ2 f =
      zhat (fun τ => z (f.hom.comp τ)) hz' := by
  rw [← cancel_mono (kernel.ι ((KS Z).d 2 3)), Category.assoc, Category.assoc, thetaZ2_ι,
    ← Category.assoc ((pullbackFun f).map _), ← Functor.map_comp, zhat_ι, zhat_ι]
  apply (homConstAddEquiv _).injective
  rw [homConst_alphaZ, homConstAddEquiv_epsH, Adjunction.homEquiv_naturality_left, homEquiv_thetaL]
  refine (homConstAddEquiv_comp (B' := (pushforwardFun f).obj ((KS Z).X 2)) (epsH 2 z)
    (thetaKf Zc f 2)).trans ?_
  rw [homConstAddEquiv_epsH]
  exact thetaKf_epsG f 2 z

private lemma Ext_comp_assoc_first0 {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y Z T : C}
    {a b c : ℕ} (α : Ext X Y 0) (β : Ext Y Z a) (γ : Ext Z T b) (h : a + b = c) :
    (α.comp β (zero_add a)).comp γ h = α.comp (β.comp γ h) (zero_add c) :=
  Ext.comp_assoc α β γ (zero_add a) h (by omega)

private theorem psi_natural (hW : LocallyContractibleSpace W) (hZ : LocallyContractibleSpace Z)
    (z : Sx W 2 → ℤ) (hz : cob 2 z = 0) (hz' : cob 2 (fun τ : Sx Z 2 => z (f.hom.comp τ)) = 0) :
    haveI := pullbackFun_additive f
    haveI := pullbackFun_preservesFiniteLimits f
    haveI := pullbackFun_preservesFiniteColimits f
    ((Ext.mk₀ (alphaZ f (AddCommGrpCat.of (ULift ℤ)))).comp ((psi hW z hz).mapExactFunctor (pullbackFun f))
      (zero_add 2)).comp (Ext.mk₀ (toConstZ f)) (add_zero 2) =
      psi hZ (fun τ => z (f.hom.comp τ)) hz' := by
  haveI := pullbackFun_additive f
  haveI := pullbackFun_preservesFiniteLimits f
  haveI := pullbackFun_preservesFiniteColimits f
  have n1 : ((S1_shortExact hW).map_of_exact (pullbackFun f)).extClass.comp (Ext.mk₀ (toConstZ f))
      (add_zero 1) = (Ext.mk₀ (thetaZ1 f)).comp (S1_shortExact hZ).extClass (zero_add 1) :=
    ((S1_shortExact hW).map_of_exact (pullbackFun f)).extClass_naturality (S1_shortExact hZ) (mapS1 f)
  have n2 : ((S2_shortExact hW).map_of_exact (pullbackFun f)).extClass.comp (Ext.mk₀ (thetaZ1 f))
      (add_zero 1) = (Ext.mk₀ (thetaZ2 f)).comp (S2_shortExact hZ).extClass (zero_add 1) :=
    ((S2_shortExact hW).map_of_exact (pullbackFun f)).extClass_naturality (S2_shortExact hZ) (mapS2 f)
  simp only [psi, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_extClass]
  conv_lhs => rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, n1,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero, n2,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, ← Ext_comp_assoc_first0,
    ← Ext_comp_assoc_first0, Ext.mk₀_comp_mk₀, zhat_nat f z hz hz']

private lemma mem_relCocycles_of_cob {Y : TopCat.{0}} [MetrizableSpace Y] {z : Sx Y 2 → ℤ}
    (hz : cob 2 z = 0) : z ∈ relCocycles ℤ (∅ : Set Y) 2 :=
  ⟨fun σ hσ => absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
    LinearMap.mem_ker.2 (by rw [← cob_eq_coboundary]; exact hz)⟩

private theorem phi_natural [MetrizableSpace W] [MetrizableSpace Z] (hW : LocallyContractibleSpace W)
    (hZ : LocallyContractibleSpace Z) (e : Ext (constZ W) (ZM W) 2) :
    haveI := pullbackFun_additive f
    haveI := pullbackFun_preservesFiniteLimits f
    haveI := pullbackFun_preservesFiniteColimits f
    (Ext.mk₀ (alphaZ f (AddCommGrpCat.of (ULift ℤ)))).comp (e.mapExactFunctor (pullbackFun f)) (zero_add 2) =
      ((phi hZ).symm ((relativeSingularCohomology.map ℤ (.of ℤ ℤ) f (Set.empty_subset _) 2).hom
        (phi hW e))).comp (Ext.mk₀ (alphaZ f Zc)) (add_zero 2) := by
  haveI := pullbackFun_additive f
  haveI := pullbackFun_preservesFiniteLimits f
  haveI := pullbackFun_preservesFiniteColimits f
  obtain ⟨z, hz, rfl⟩ := psi_surjective hW e
  have hz' : cob 2 (fun τ : Sx Z 2 => z (f.hom.comp τ)) = 0 := by
    funext τ
    exact congrFun hz (f.hom.comp τ)
  have hPhi : phi hW (psi hW z hz) = (relativeSingularCohomologyEquiv ℤ (∅ : Set W) 2).symm
      (Submodule.Quotient.mk ⟨z, mem_relCocycles_of_cob hz⟩) := by
    rw [← phi_symm_mk hW ⟨z, mem_relCocycles_of_cob hz⟩, AddEquiv.apply_symm_apply]
  have hmap : (relativeSingularCohomology.map ℤ (.of ℤ ℤ) f (Set.empty_subset _) 2).hom
      ((relativeSingularCohomologyEquiv ℤ (∅ : Set W) 2).symm
        (Submodule.Quotient.mk ⟨z, mem_relCocycles_of_cob hz⟩)) =
      (relativeSingularCohomologyEquiv ℤ (∅ : Set Z) 2).symm
        (Submodule.Quotient.mk ⟨_, mem_relCocycles_of_cob hz'⟩) := by
    apply (relativeSingularCohomologyEquiv ℤ (∅ : Set Z) 2).injective
    refine (relativeSingularCohomologyEquiv_map (R := ℤ) f (A := (∅ : Set W))
      (Set.empty_subset _) 2 _).trans ?_
    rw [LinearEquiv.apply_symm_apply, relCohomologyMap_mk, LinearEquiv.apply_symm_apply]
    rfl
  rw [hPhi, hmap, phi_symm_mk hZ, ← psi_natural f hW hZ z hz hz', Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, toConstZ_alphaZ, Ext.comp_mk₀_id]

end NatZ

end TopologicalComparison

section TopologicalSide

open CategoryTheory.Abelian MMP.SingularChain MMP.SingularCochain

private theorem topological_side :
    let α : ∀ {Z W : TopCat.{0}} (f : Z ⟶ W) (M : AddCommGrpCat.{0}),
        (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj M ⟶
          (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj
            ((constantSheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0}).obj M) :=
      fun {Z W} f M ↦ ((constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0}
          isTerminalTop).homEquiv M _).symm
        ((constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0} isTerminalTop).unit.app M ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app
            ((constantSheaf _ _).obj M)).hom.app (op ⊤))
    ∃ φ : ∀ (M : TopCat.{0}), MetrizableSpace M → LocallyContractibleSpace M →
        (Sheaf.H.{0} (ZSh M) 2 ≃+ relativeSingularCohomology ℤ (.of ℤ ℤ) M ∅ 2),
      (∀ {Z W : TopCat.{0}} (hZ : MetrizableSpace Z) (hZ' : LocallyContractibleSpace Z)
        (hW : MetrizableSpace W) (hW' : LocallyContractibleSpace W) (f : Z ⟶ W)
        (e : Sheaf.H.{0} (ZSh W) 2),
        (Ext.mk₀ (α f (.of (ULift ℤ)))).comp
            ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapExtAddHom _ _ 2 e) (zero_add 2) =
          ((φ Z hZ hZ').symm ((relativeSingularCohomology.map ℤ (.of ℤ ℤ) f
              (Set.empty_subset _) 2).hom (φ W hW hW' e))).comp
            (Ext.mk₀ (α f (.of ℤ))) (add_zero 2)) ∧
      ∃ ε₀ : ℤˣ, ∀ (M : TopCat.{0}) (hM : MetrizableSpace M) (hM' : LocallyContractibleSpace M)
        (z : Simplex M 2 → ℤ) (hz : z ∈ relCocycles ℤ (∅ : Set M) 2)
        {I : Type} (Ui : I → Opens M) (hUi : (⊤ : Opens M) = ⨆ i, Ui i)
        (w : I → Simplex M 1 → ℤ)
        (_ : ∀ i (σ : Simplex M 2), Set.range σ ⊆ Ui i → z σ = coboundary ℤ 1 (w i) σ)
        (c : CechCochains.cocycles1 Ui (quotSheaf M).obj), IsKappaCocycle Ui w c →
        (φ M hM hM').symm ((relativeSingularCohomologyEquiv ℤ (∅ : Set M) 2).symm
            (Submodule.Quotient.mk ⟨z, hz⟩)) =
          (ε₀ : ℤ) • quotExtClass M Ui hUi c := by
  intro α
  refine ⟨fun M hM hM' => @phi M hM hM', fun {Z W} hZ hZ' hW hW' f e => ?_, 1,
    fun M hM hM' z hz I Ui hUi w hw c hc => ?_⟩
  · exact @phi_natural W Z f hW hZ hW' hZ' e
  · rw [@phi_symm_mk M hM hM' ⟨z, hz⟩, Units.val_one, one_smul]
    exact @psi_eq_quotExtClass M hM' hM z _ I Ui hUi w hw c hc

end TopologicalSide

/-- The analytic space of a projective scheme over `ℂ` is metrizable and locally contractible. -/
private theorem metrizable_locallyContractible_analyticSpace {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) :
    MetrizableSpace (analyticSpace sX) ∧ LocallyContractibleSpace (analyticSpace sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : IsComplexScheme X := MMP.Analytic.isComplexScheme_of_isProjective X hX.isProjective
  obtain ⟨hb, N, F, hF⟩ := UnderlyingSpace.hasBasis_contractible_and_exists_isClosedEmbedding X
  let h : analyticSpace sX ≃ₜ UnderlyingSpace ℂ X := homeomorphUnderlyingSpace (X := X)
  have hbasis : ∀ p : analyticSpace sX, (𝓝 p).HasBasis
      (fun V : Set (analyticSpace sX) ↦ IsOpen V ∧ p ∈ V ∧ ContractibleSpace V) id := fun p ↦
    ⟨fun t ↦ ⟨fun ht ↦ by
      have : h.symm ⁻¹' t ∈ 𝓝 (h p) :=
        h.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using ht)
      obtain ⟨V, ⟨hVo, hpV, hV⟩, hVt⟩ := (hb (h p)).mem_iff.1 this
      refine ⟨h.symm '' V, ⟨h.symm.isOpenMap V hVo, ⟨h p, hpV, by simp⟩,
        (h.symm.image V).symm.contractibleSpace⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hVt hy, fun ⟨W, ⟨hWo, hpW, _⟩, hWt⟩ ↦ Filter.mem_of_superset (hWo.mem_nhds hpW) hWt⟩⟩
  refine ⟨(hF.comp h.isClosedEmbedding).isEmbedding.metrizableSpace, ?_⟩
  haveI : StronglyLocallyContractibleSpace (analyticSpace sX) :=
    ⟨fun p ↦ (hbasis p).to_hasBasis (fun V ⟨hVo, hpV, hV⟩ ↦ ⟨V, ⟨hVo.mem_nhds hpV, hV⟩, le_rfl⟩)
      (fun V ⟨hV, _⟩ ↦ by
        obtain ⟨W, ⟨hWo, hpW, hW⟩, hWV⟩ := (hbasis p).mem_iff.1 hV
        exact ⟨W, ⟨hWo, hpW, hW⟩, hWV⟩)⟩
  exact StronglyLocallyContractibleSpace.locallyContractible

private theorem analytic_geometry :
    ∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX),
        haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX
        let J := Opens.grothendieckTopology (space sX)
        let O : Sheaf J AddCommGrpCat.{0} :=
          (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
        let Ou : Sheaf J AddCommGrpCat.{0} :=
          Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
        let ZA : Sheaf J AddCommGrpCat.{0} :=
          (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
        ∀ (ι : ZA ⟶ O) (e : O ⟶ Ou) (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact),
          (∀ (W : Opens (space sX)) (n : ℤ),
            (show (structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
              ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
          (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
            (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
            (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
            (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
            (g' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
              (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
            s.1 x c = Chart.StalkRing.mk c.1 _ g →
            ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
              (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ g') →
          ∀ (L : SheafOfModules (ringCatSheaf sX))
            (hL : Stacks.SheafOfModules.IsInvertible (analytification sX).sheaf.obj
              (ringCatSheaf sX).property L)
            (E : space sX → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
            [TopologicalSpace (TotalSpace ℂ E)] [∀ x, TopologicalSpace (E x)]
            [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]
            (val : ∀ V : Opens (space sX), L.val.obj (op V) → ∀ x : V, E x),
            (∀ (V : Opens (space sX)) (t : L.val.obj (op V)),
              Continuous fun x : V ↦ (⟨x.1, val V t x⟩ : TotalSpace ℂ E)) →
            (∀ (V : Opens (space sX)) (t t' : L.val.obj (op V)),
              val V (t + t') = val V t + val V t') →
            (∀ (V W : Opens (space sX)) (h : W ≤ V) (t : L.val.obj (op V)) (x : W),
              val W (L.val.map (homOfLE h).op t) x = val V t ⟨x.1, h x.2⟩) →
            (∀ (V : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op V))
              (t : L.val.obj (op V)) (x : V)
              (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U})
              (g : holGerms (c.1.coords ⟨x.1, c.2⟩)),
              s.1 x c = Chart.StalkRing.mk c.1 _ g →
              val V ((show (ringCatSheaf sX).obj.obj (op V) from s) • t) x =
                Germ.value (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) • val V t x) →
            (∀ x : space sX, ∃ (V : Opens (space sX)) (t : L.val.obj (op V)) (hx : x ∈ V),
              val V t ⟨x, hx⟩ ≠ 0) →
            ∀ (lam : Ou ⟶ quotSheaf (space sX)),
              e ≫ lam = valueMap sX ≫ cokernel.π (constFun (space sX)) →
            ∃ (I : Type) (Ui : I → Opens (space sX)) (hUi : (⊤ : Opens (space sX)) = ⨆ i, Ui i)
              (sec : ∀ i, (Stacks.Cohomology.Generators.generatorTorsorOfInvertible
                (analytification sX) L hL).toTorsor.F.obj (Ui i))
              (g : CechCochains.cocycles1 Ui (Stacks.Cohomology.Generators.unitsSheaf
                (analytification sX)).obj),
              Stacks.Cohomology.SheafTorsor.IsTransitionCocycle
                (Stacks.Cohomology.Generators.generatorTorsorOfInvertible
                  (analytification sX) L hL).toTorsor Ui sec g ∧
              ∃ (h : CechCochains.Cochain Ui (quotSheaf (space sX)).obj 0)
                (c : CechCochains.cocycles1 Ui (quotSheaf (space sX)).obj),
                (∀ i, c.1 i = CechCochains.cechD Ui (quotSheaf (space sX)).obj 0 h i -
                  lam.hom.app (op (CechCochains.inter Ui i)) (g.1 i)) ∧
              ∃ wc : I → MMP.SingularChain.Simplex (space sX) 1 → ℤ,
                (∀ i (σ : MMP.SingularChain.Simplex (space sX) 2),
                  Set.range σ ⊆ Ui i →
                    ComplexLineBundle.obstructionCocycle E σ =
                      MMP.SingularCochain.coboundary ℤ 1 (wc i) σ) ∧
                IsKappaCocycle Ui wc c := by
  intro X sX hX J O Ou ZA ι e w hS hι he L hL E _ _ _ _ _ _ val h1 h2 h3 h4 h5 lam hlam
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX
  haveI : Epi e := hS.epi_g
  classical
  let T := Stacks.Cohomology.Generators.generatorTorsorOfInvertible (analytification sX) L hL
  have hgen := fun x => exists_generator_ne_zero sX L hL E val h3 h4 h5 x
  choose U0 hU0 s0 hs0 using hgen
  let f0 : ∀ x, ∀ y : U0 x, E y := fun x y => val (U0 x) (T.sectionsEquiv (U0 x) (s0 x)).val y
  have hlog := fun x => exists_frameCoord_log (trivializationAt ℂ E x) (U0 x) (f0 x) (h1 _ _)
    (hU0 x) (FiberBundle.mem_baseSet_trivializationAt ℂ E x) (hs0 x)
  choose U1 hxU1 hU10 hU1e Lg hLgc hLg using hlog
  have hUi : (⊤ : Opens (space sX)) = ⨆ x, U1 x := by
    ext y
    simp only [Opens.coe_top, Opens.coe_iSup, Set.mem_univ, Set.mem_iUnion, true_iff]
    exact ⟨y, hxU1 y⟩
  let sec : ∀ x, T.F.obj (U1 x) := fun x => T.F.res (hU10 x) (s0 x)
  let g := Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle T.toTorsor U1 sec
  have hg := Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_spec T.toTorsor U1 sec
  have hw := fun x => exists_obstructionCocycle_eq_coboundary (E := E) (trivializationAt ℂ E x)
  choose wc hwc1 hwc2 using hw
  let hfun : ∀ x, space sX → ℂ := fun x z =>
    (Lg x z - Complex.log (ComplexLineBundle.vertexCoord (E := E) (trivializationAt ℂ E x) z)) /
      (2 * Real.pi * Complex.I)
  let h : CechCochains.Cochain U1 (quotSheaf (space sX)).obj 0 := fun i =>
    (cokernel.π (constFun (space sX))).hom.app (op (CechCochains.inter U1 i))
      (show CechCochains.inter U1 i → ℂ from fun z => hfun (i 0) z)
  let lamg := Stacks.Cohomology.CechOne.push U1 lam.hom 1 g.1
  have hlamg : CechCochains.cechD U1 (quotSheaf (space sX)).obj 1 lamg = 0 :=
    Stacks.Cohomology.CechOne.cechD_push U1 lam.hom 1 g.1 g.2
  let c : CechCochains.cocycles1 U1 (quotSheaf (space sX)).obj :=
    ⟨CechCochains.cechD U1 (quotSheaf (space sX)).obj 0 h - lamg, by
      rw [CechCochains.mem_cocycles1_iff, map_sub, CechCochains.cechD_cechD, hlamg, sub_zero]⟩
  refine ⟨space sX, U1, hUi, sec, g, hg, h, c, fun i => rfl, wc,
    fun x σ hσ => hwc2 x σ (hσ.trans (hU1e x)), ?_⟩
  intro i y hy
  have hi0 : CechCochains.inter U1 i ≤ U1 (i 0) := iInf_le (fun k => U1 (i k)) 0
  have hi1 : CechCochains.inter U1 i ≤ U1 (i 1) := iInf_le (fun k => U1 (i k)) 1
  obtain ⟨V, hVW, hyV, φ, hφc, hφexp, hφlam⟩ := exists_local_log_lam sX e he lam hlam (g.1 i) hy
  -- the generators on the overlap are the frames `f0`
  have hgen : ∀ (k : Fin 2) (z : CechCochains.inter U1 i), val (CechCochains.inter U1 i)
      (T.sectionsEquiv _ (T.F.res (iInf_le (fun k => U1 (i k)) k) (sec (i k)))).val z =
        f0 (i k) ⟨z.1, hU10 _ (iInf_le (fun k => U1 (i k)) k z.2)⟩ := by
    intro k z
    rw [T.sectionsEquiv_restrict, T.sectionsEquiv_restrict]
    exact (h3 _ _ _ _ z).trans (h3 _ _ _ _ _)
  have hfr : ∀ z (hz : z ∈ V), f0 (i 1) ⟨z, hU10 _ (hi1 (hVW hz))⟩ =
      Complex.exp (2 * Real.pi * Complex.I * φ z) • f0 (i 0) ⟨z, hU10 _ (hi0 (hVW hz))⟩ := by
    intro z hz
    have hact := val_act_eq sX L hL E val h4 _ _ (g.1 i) (hg i) ⟨z, hVW hz⟩
    have e1 := hgen 1 ⟨z, hVW hz⟩
    have e0 := hgen 0 ⟨z, hVW hz⟩
    refine e1.symm.trans (hact.trans ?_)
    rw [← hφexp z hz]
    exact congrArg _ e0
  have hLi : ∀ x, ∀ y ∈ U1 x, Complex.exp (Lg x y) =
      frameCoord (trivializationAt ℂ E x) (U1 x) (fun z => f0 x ⟨z.1, hU10 x z.2⟩) y := by
    intro x y hy
    rw [hLg x y hy, frameCoord_of_mem _ _ _ (hU10 x hy), frameCoord_of_mem _ _ _ hy]
  obtain ⟨a, ha_edge, ha_val⟩ := exists_int_primitive (ei := trivializationAt ℂ E (i 0))
    (ej := trivializationAt ℂ E (i 1)) (Ui := U1 (i 0)) (Uj := U1 (i 1))
    (fun z => f0 (i 0) ⟨z.1, hU10 _ z.2⟩) (fun z => f0 (i 1) ⟨z.1, hU10 _ z.2⟩)
    (hLi (i 0)) (hLi (i 1)) V (hVW.trans hi0) (hVW.trans hi1)
    (fun z hz => hU1e _ (hi0 (hVW hz))) (fun z hz => hU1e _ (hi1 (hVW hz)))
    ((hLgc _).mono fun z hz => hi0 (hVW hz)) ((hLgc _).mono fun z hz => hi1 (hVW hz)) hφc
    (fun z hz => hfr z hz) (hwc1 (i 0)) (hwc1 (i 1))
  refine ⟨V, hVW, hyV, a, fun τ hτ => ha_edge τ hτ, ?_⟩
  have hnat : ∀ {W W' : Opens (space sX)} (hW : W' ≤ W) (F : W → ℂ),
      (quotSheaf (space sX)).obj.map (homOfLE hW).op
        ((cokernel.π (constFun (space sX))).hom.app (op W) F) =
      (cokernel.π (constFun (space sX))).hom.app (op W') (show W' → ℂ from
        fun z => F ⟨z.1, hW z.2⟩) := fun hW F =>
    (ConcreteCategory.congr_hom ((cokernel.π (constFun (space sX))).hom.naturality
      (homOfLE hW).op) F).symm
  change (quotSheaf (space sX)).obj.map (homOfLE hVW).op
    (CechCochains.cechD U1 (quotSheaf (space sX)).obj 0 h i -
      lam.hom.app (op (CechCochains.inter U1 i)) (g.1 i)) = _
  rw [map_sub, hφlam, cechD_zero_apply, map_sub]
  simp only [CechCochains.restr, h]
  rw [hnat, hnat, hnat, hnat]
  have hsub : ∀ F G : (funSheaf (space sX) ℂ).obj.obj (op V),
      (cokernel.π (constFun (space sX))).hom.app (op V) F -
        (cokernel.π (constFun (space sX))).hom.app (op V) G =
      (cokernel.π (constFun (space sX))).hom.app (op V) (F - G) := fun F G => (map_sub _ F G).symm
  refine ((congrArg (· - _) (hsub _ _)).trans (hsub _ _)).trans (congrArg _ ?_)
  refine funext fun z => ?_
  change _ = ((a z : ℤ) : ℂ)
  rw [ha_val z]
  rfl

/-- The class of a torsor under `U`, pushed along `lam : U ⟶ quotSheaf M` and followed by the
connecting map of `0 ⟶ ℤ ⟶ ℂ^M ⟶ quotSheaf M ⟶ 0`, is minus the class of any Čech cocycle `c`
cohomologous to minus the image under `lam` of a transition cocycle of the torsor. -/
private theorem sheafCohomologyOneExtEquiv_torsorClass_comp_eq_neg_quotExtClass
    {M : TopCat.{0}} {U : Sheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}}
    (T : Stacks.Cohomology.SheafTorsor.Torsor M U) (lam : U ⟶ quotSheaf M) {I : Type}
    (Ui : I → Opens M) (hUi : (⊤ : Opens M) = ⨆ i, Ui i) (s : ∀ i, T.F.obj (Ui i))
    (g : CechCochains.cocycles1 Ui U.obj)
    (hg : Stacks.Cohomology.SheafTorsor.IsTransitionCocycle T Ui s g)
    (h : CechCochains.Cochain Ui (quotSheaf M).obj 0)
    (c : CechCochains.cocycles1 Ui (quotSheaf M).obj)
    (hc : ∀ i, c.1 i = CechCochains.cechD Ui (quotSheaf M).obj 0 h i -
      lam.hom.app (op (CechCochains.inter Ui i)) (g.1 i)) :
    ((Stacks.Thickenings.sheafCohomologyOneExtEquiv M U).hom
        (Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne M U ⟦T⟧)).comp
      ((Ext.mk₀ lam).comp (quotSeq_shortExact M).extClass (zero_add 1))
      (show 1 + 1 = 2 from rfl) =
    ((-1 : ℤˣ) : ℤ) • quotExtClass M Ui hUi c := by
  refine (Ext.comp_assoc_of_second_deg_zero _ _ _ _).symm.trans ?_
  refine (congrArg (fun y => Ext.comp y _ _) (sheafCohomologyOneExtEquiv_naturality lam _)).trans ?_
  rw [rightDerived_map_torsorClass_eq_neg T lam Ui hUi s g hg h c hc]
  refine (congrArg (fun z => Ext.comp z (quotSeq_shortExact M).extClass
    (show 1 + 1 = 2 from rfl)) (map_neg (ConcreteCategory.hom
      (Stacks.Thickenings.sheafCohomologyOneExtEquiv M (quotSheaf M)).hom) _)).trans ?_
  rw [Ext.neg_comp, quotExtClass]
  simp

/-- `picardObstruction_classOf` for the analytification of a proper scheme over `ℂ`. -/
private theorem picardObstruction_classOf_analytification {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX]
    (ι : ZSh (space sX) ⟶ (sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX))
    (e : (sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX) ⟶
        Stacks.Cohomology.Generators.unitsSheaf (analytification sX))
    (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact)
    (L : SheafOfModules (ringCatSheaf sX))
    (hL : Stacks.SheafOfModules.IsInvertible (analytification sX).sheaf.obj
      (ringCatSheaf sX).property L) :
    picardObstruction (analytification sX) hS
        (Stacks.SheafOfModules.Picard.classOf _ _ L hL) =
      ((Stacks.Thickenings.sheafCohomologyOneExtEquiv (space sX)
          (Stacks.Cohomology.Generators.unitsSheaf (analytification sX))).hom
        (Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne (space sX)
          (Stacks.Cohomology.Generators.unitsSheaf (analytification sX))
          ⟦(Stacks.Cohomology.Generators.generatorTorsorOfInvertible
            (analytification sX) L hL).toTorsor⟧)).comp
        hS.extClass (show 1 + 1 = 2 from rfl) :=
  picardObstruction_classOf (analytification sX) hS L hL

/-- The exponential obstruction of `L`, computed from a units logarithm `lam` and the Čech data
of a trivializing cover: minus the class of the cocycle `c`. -/
private theorem picardObstruction_eq_neg_quotExtClass {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX]
    (ι : ZSh (space sX) ⟶ (sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX))
    (e : (sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX) ⟶
        Stacks.Cohomology.Generators.unitsSheaf (analytification sX))
    (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact)
    (L : SheafOfModules (ringCatSheaf sX))
    (hL : Stacks.SheafOfModules.IsInvertible (analytification sX).sheaf.obj
      (ringCatSheaf sX).property L)
    (lam : Stacks.Cohomology.Generators.unitsSheaf (analytification sX) ⟶ quotSheaf (space sX))
    (hext : hS.extClass =
      (Ext.mk₀ lam).comp (quotSeq_shortExact (space sX)).extClass (zero_add 1))
    {I : Type} (Ui : I → Opens (space sX)) (hUi : (⊤ : Opens (space sX)) = ⨆ i, Ui i)
    (sec : ∀ i, (Stacks.Cohomology.Generators.generatorTorsorOfInvertible
      (analytification sX) L hL).toTorsor.F.obj (Ui i))
    (g : CechCochains.cocycles1 Ui (Stacks.Cohomology.Generators.unitsSheaf
      (analytification sX)).obj)
    (hg : Stacks.Cohomology.SheafTorsor.IsTransitionCocycle
      (Stacks.Cohomology.Generators.generatorTorsorOfInvertible
        (analytification sX) L hL).toTorsor Ui sec g)
    (h : CechCochains.Cochain Ui (quotSheaf (space sX)).obj 0)
    (c : CechCochains.cocycles1 Ui (quotSheaf (space sX)).obj)
    (hc' : ∀ i, c.1 i = CechCochains.cechD Ui (quotSheaf (space sX)).obj 0 h i -
      lam.hom.app (op (CechCochains.inter Ui i)) (g.1 i)) :
    picardObstruction (analytification sX) hS
        (Stacks.SheafOfModules.Picard.classOf _ _ L hL) =
      ((-1 : ℤˣ) : ℤ) • quotExtClass (space sX) Ui hUi c := by
  refine (picardObstruction_classOf_analytification sX ι e w hS L hL).trans ?_
  rw [hext]
  have hG := sheafCohomologyOneExtEquiv_torsorClass_comp_eq_neg_quotExtClass
    (M := space sX) (U := Stacks.Cohomology.Generators.unitsSheaf (analytification sX))
    (Stacks.Cohomology.Generators.generatorTorsorOfInvertible (analytification sX) L hL).toTorsor
    lam Ui hUi sec g hg h c hc'
  exact hG

private theorem analytic_side :
    ∃ ε₁ : ℤˣ, ∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX),
        haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX
        let J := Opens.grothendieckTopology (space sX)
        let O : Sheaf J AddCommGrpCat.{0} :=
          (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
        let Ou : Sheaf J AddCommGrpCat.{0} :=
          Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
        let ZA : Sheaf J AddCommGrpCat.{0} :=
          (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
        ∀ (ι : ZA ⟶ O) (e : O ⟶ Ou) (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact),
          (∀ (W : Opens (space sX)) (n : ℤ),
            (show (structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
              ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
          (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
            (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
            (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
            (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
            (g' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
              (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
            s.1 x c = Chart.StalkRing.mk c.1 _ g →
            ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
              (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ g') →
          ∀ (L : SheafOfModules (ringCatSheaf sX))
            (hL : Stacks.SheafOfModules.IsInvertible (analytification sX).sheaf.obj
              (ringCatSheaf sX).property L)
            (E : space sX → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
            [TopologicalSpace (TotalSpace ℂ E)] [∀ x, TopologicalSpace (E x)]
            [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]
            (val : ∀ V : Opens (space sX), L.val.obj (op V) → ∀ x : V, E x),
            (∀ (V : Opens (space sX)) (t : L.val.obj (op V)),
              Continuous fun x : V ↦ (⟨x.1, val V t x⟩ : TotalSpace ℂ E)) →
            (∀ (V : Opens (space sX)) (t t' : L.val.obj (op V)),
              val V (t + t') = val V t + val V t') →
            (∀ (V W : Opens (space sX)) (h : W ≤ V) (t : L.val.obj (op V)) (x : W),
              val W (L.val.map (homOfLE h).op t) x = val V t ⟨x.1, h x.2⟩) →
            (∀ (V : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op V))
              (t : L.val.obj (op V)) (x : V)
              (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U})
              (g : holGerms (c.1.coords ⟨x.1, c.2⟩)),
              s.1 x c = Chart.StalkRing.mk c.1 _ g →
              val V ((show (ringCatSheaf sX).obj.obj (op V) from s) • t) x =
                Germ.value (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) • val V t x) →
            (∀ x : space sX, ∃ (V : Opens (space sX)) (t : L.val.obj (op V)) (hx : x ∈ V),
              val V t ⟨x, hx⟩ ≠ 0) →
            ∃ (I : Type) (Ui : I → Opens (space sX)) (hUi : (⊤ : Opens (space sX)) = ⨆ i, Ui i)
              (wc : I → MMP.SingularChain.Simplex (space sX) 1 → ℤ),
              (∀ i (σ : MMP.SingularChain.Simplex (space sX) 2),
                Set.range σ ⊆ Ui i →
                  ComplexLineBundle.obstructionCocycle E σ =
                    MMP.SingularCochain.coboundary ℤ 1 (wc i) σ) ∧
              ∃ c : CechCochains.cocycles1 Ui (quotSheaf (space sX)).obj,
                IsKappaCocycle Ui wc c ∧
                picardObstruction (analytification sX) hS
                    (Stacks.SheafOfModules.Picard.classOf _ _ L hL) =
                  (ε₁ : ℤ) • quotExtClass (space sX) Ui hUi c := by
  refine ⟨-1, ?_⟩
  intro X sX hX J O Ou ZA ι e w hS hι he L hL E _ _ _ _ _ _ val h1 h2 h3 h4 h5
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX
  obtain ⟨lam, hlam, hext⟩ := exists_unitsLog sX ι e w hS hι
  obtain ⟨I, Ui, hUi, sec, g, hg, h, c, hc', wc, hwc, hc⟩ :=
    analytic_geometry sX hX ι e w hS hι he L hL E val h1 h2 h3 h4 h5 lam hlam
  exact ⟨I, Ui, hUi, wc, hwc, c, hc,
    picardObstruction_eq_neg_quotExtClass sX ι e w hS L hL lam hext Ui hUi sec g hg h c hc'⟩

end MMP.Proof_lem_mmp_projective_logarithm_first_chern

namespace MMP.Analytic

open MMP.Proof_lem_mmp_projective_logarithm_first_chern

/-- **The exponential obstruction is the topological first Chern class.** There are comparison
isomorphisms `φ : H²(X^an, ℤ_{X^an}) ≃ H²(X(ℂ), ∅; ℤ)` for the projective schemes `X` over `ℂ`,
natural for pullback along morphisms over `ℂ`, and a sign `ε ∈ ℤˣ`, such that for every
projective `X` over `ℂ`, every invertible sheaf `L` on the analytification `X^an` and every
complex topological line bundle `E` on `X(ℂ)` underlying `L`, the image under `φ` of the
exponential obstruction `MMP.Analytic.picardObstruction` of `L` is `ε` times the first Chern
class `MMP.Analytic.analyticFirstChernClass E`. Here `E` underlies `L` through `val`, sending a
section of `L` over `V` to a continuous section of `E` over `V`, additively, compatibly with
restriction, with `val (s • t) x = s(x) • val t x` for an analytic function `s` with value `s(x)`
at `x`, and with `val t x ≠ 0` for some local section `t` near each point `x`. -/
@[mmp "lem_mmp_projective_logarithm_first_chern"]
public theorem exists_addEquiv_picardObstruction_eq_firstChernClass :
    let α : ∀ {Z W : TopCat.{0}} (f : Z ⟶ W) (M : AddCommGrpCat.{0}),
        (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).obj M ⟶
          (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj
            ((constantSheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0}).obj M) :=
      fun {Z W} f M ↦ ((constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0}
          isTerminalTop).homEquiv M _).symm
        ((constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0}
            isTerminalTop).unit.app M ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app
            ((constantSheaf _ _).obj M)).hom.app (op ⊤))
    ∃ φ : ∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)), IsProjectiveMorphism sX →
        (Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (analyticSpace sX))
            AddCommGrpCat.{0}).obj (.of ℤ)) 2 ≃+
          relativeSingularCohomology ℤ (.of ℤ ℤ) (analyticSpace sX) ∅ 2),
      (∀ {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
        (hX : IsProjectiveMorphism sX) (hY : IsProjectiveMorphism sY) (g : X ⟶ Y)
        (hg : g ≫ sY = sX)
        (e : Sheaf.H.{0} ((constantSheaf (Opens.grothendieckTopology (analyticSpace sY))
            AddCommGrpCat.{0}).obj (.of ℤ)) 2),
        (Ext.mk₀ (α (analyticMap g hg) (.of (ULift ℤ)))).comp
            ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).mapExtAddHom _ _ 2 e)
            (zero_add 2) =
          ((φ sX hX).symm ((relativeSingularCohomology.map ℤ (.of ℤ ℤ) (analyticMap g hg)
              (Set.empty_subset _) 2).hom (φ sY hY e))).comp
            (Ext.mk₀ (α (analyticMap g hg) (.of ℤ))) (add_zero 2)) ∧
      ∃ ε : ℤˣ, ∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX),
        haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX
        let J := Opens.grothendieckTopology (space sX)
        let O : Sheaf J AddCommGrpCat.{0} :=
          (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
        let Ou : Sheaf J AddCommGrpCat.{0} :=
          Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
        let ZA : Sheaf J AddCommGrpCat.{0} :=
          (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
        ∀ (ι : ZA ⟶ O) (e : O ⟶ Ou) (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact),
          (∀ (W : Opens (space sX)) (n : ℤ),
            (show (structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
              ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
          (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
            (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
            (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
            (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
            (g' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
              (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
            s.1 x c = Chart.StalkRing.mk c.1 _ g →
            ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
              (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ g') →
          ∀ (L : SheafOfModules (ringCatSheaf sX))
            (hL : Stacks.SheafOfModules.IsInvertible (analytification sX).sheaf.obj
              (ringCatSheaf sX).property L)
            (E : space sX → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
            [TopologicalSpace (TotalSpace ℂ E)] [∀ x, TopologicalSpace (E x)]
            [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]
            (val : ∀ V : Opens (space sX), L.val.obj (op V) → ∀ x : V, E x),
            (∀ (V : Opens (space sX)) (t : L.val.obj (op V)),
              Continuous fun x : V ↦ (⟨x.1, val V t x⟩ : TotalSpace ℂ E)) →
            (∀ (V : Opens (space sX)) (t t' : L.val.obj (op V)),
              val V (t + t') = val V t + val V t') →
            (∀ (V W : Opens (space sX)) (h : W ≤ V) (t : L.val.obj (op V)) (x : W),
              val W (L.val.map (homOfLE h).op t) x = val V t ⟨x.1, h x.2⟩) →
            (∀ (V : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op V))
              (t : L.val.obj (op V)) (x : V)
              (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U})
              (g : holGerms (c.1.coords ⟨x.1, c.2⟩)),
              s.1 x c = Chart.StalkRing.mk c.1 _ g →
              val V ((show (ringCatSheaf sX).obj.obj (op V) from s) • t) x =
                Germ.value (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) • val V t x) →
            (∀ x : space sX, ∃ (V : Opens (space sX)) (t : L.val.obj (op V)) (hx : x ∈ V),
              val V t ⟨x, hx⟩ ≠ 0) →
            φ sX hX (picardObstruction (analytification sX) hS
                (Stacks.SheafOfModules.Picard.classOf _ _ L hL)) =
              ε • (relativeSingularCohomology.map ℤ (.of ℤ ℤ) (𝟙 (analyticSpace sX))
                (Set.empty_subset _) 2).hom (analyticFirstChernClass E) := by
  intro α
  obtain ⟨φT, hnat, ε₀, hT⟩ := topological_side
  obtain ⟨ε₁, hA⟩ := analytic_side
  refine ⟨fun sX hX ↦ φT _ (metrizable_locallyContractible_analyticSpace sX hX).1
      (metrizable_locallyContractible_analyticSpace sX hX).2,
    fun sX sY hX hY g hg e ↦ hnat _ _ _ _ (analyticMap g hg) e, ε₀ * ε₁, ?_⟩
  intro X sX hX J O Ou ZA ι e w hS hι he L hL E _ _ _ _ _ _ val h1 h2 h3 h4 h5
  obtain ⟨I, Ui, hUi, wc, hwc, c, hc, hpic⟩ := hA sX hX ι e w hS hι he L hL E val h1 h2 h3 h4 h5
  have hm := metrizable_locallyContractible_analyticSpace sX hX
  have hz : ComplexLineBundle.obstructionCocycle E ∈
      MMP.SingularCochain.relCocycles ℤ (∅ : Set (analyticSpace sX)) 2 :=
    ⟨fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
      LinearMap.mem_ker.2 (ComplexLineBundle.coboundary_obstructionCocycle (E := E))⟩
  have key := hT _ hm.1 hm.2 _ hz Ui hUi wc hwc c hc
  have hQ : quotExtClass (space sX) Ui hUi c = (ε₀ : ℤ) • (φT _ hm.1 hm.2).symm
      ((MMP.SingularCochain.relativeSingularCohomologyEquiv ℤ
        (∅ : Set (analyticSpace sX)) 2).symm (Submodule.Quotient.mk ⟨_, hz⟩)) := by
    rw [key, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  have hc1 : (relativeSingularCohomology.map ℤ (.of ℤ ℤ) (𝟙 (analyticSpace sX))
      (Set.empty_subset _) 2).hom (analyticFirstChernClass E) =
      (MMP.SingularCochain.relativeSingularCohomologyEquiv ℤ
        (∅ : Set (analyticSpace sX)) 2).symm (Submodule.Quotient.mk ⟨_, hz⟩) := by
    apply (MMP.SingularCochain.relativeSingularCohomologyEquiv ℤ
      (∅ : Set (analyticSpace sX)) 2).injective
    refine (MMP.SingularCochain.relativeSingularCohomologyEquiv_map (R := ℤ)
      (𝟙 (analyticSpace sX)) (A := (Set.univᶜ : Set (analyticSpace sX))) (Set.empty_subset _) 2
      (analyticFirstChernClass E)).trans ?_
    rw [LinearEquiv.apply_symm_apply]
    simp only [analyticFirstChernClass, firstChernClass, cohomologyWithSupports.ofCocycle,
      LinearEquiv.apply_symm_apply, MMP.SingularCochain.relCohomologyMap_mk]
    rfl
  change (φT _ hm.1 hm.2) _ = _
  rw [hpic, hQ, hc1, smul_smul, map_zsmul, AddEquiv.apply_symm_apply, Units.smul_def]
  push_cast
  ring_nf

end MMP.Analytic
