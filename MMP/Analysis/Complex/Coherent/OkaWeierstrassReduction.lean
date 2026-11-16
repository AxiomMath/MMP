module

public import MMP.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocal
public import MMP.Algebra.Category.ModuleCat.Sheaf.FreeSections
public import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
public import MMP.Analysis.Complex.HolomorphicCompactConvergence

/-!
# Oka coherence: sections, presentations and the Weierstrass reduction

Kernels and epimorphisms of sheaves of modules described through sections, finite presentations
and coherent modules, the reduction of relation modules to one row, pullback along restriction to
opens, holomorphic functions read in charts, and the algebra of holomorphic germs in the
Weierstrass case of Oka's coherence theorem: division, preparation at moving centres, polynomial
relations and their finite generation.
-/

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicGeometry MMP.Analytic
open scoped Manifold ContDiff

namespace MMP.Analytic.OkaCoherence

/-! ### Kernels and epimorphisms of sheaves of modules, in terms of sections -/

section Site

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- An element of `P` over `Y`, as a section of the restriction `P|_Y`. -/
noncomputable def overSection (P : SheafOfModules.{0} R) {Y : C} (x : P.val.obj (op Y)) :
    (P.over Y).sections :=
  PresheafOfModules.sectionsMk (fun U => P.val.map U.unop.hom.op x) fun {U U'} f => by
    change P.val.map f.unop.left.op (P.val.map U.unop.hom.op x) = P.val.map U'.unop.hom.op x
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w f.unop]

/-- The inclusion of a kernel of sheaves of modules is injective on sections. -/
theorem kernel_ι_app_injective {M N : SheafOfModules.{0} R} (g : M ⟶ N) (X : Cᵒᵖ) :
    Function.Injective ((kernel.ι g).val.app X) := by
  have : Mono ((SheafOfModules.evaluation R X).map (kernel.ι g)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

/-- A section killed by `g` comes from the kernel of `g`. -/
theorem exists_kernel_ι_app_eq {M N : SheafOfModules.{0} R} (g : M ⟶ N) (X : Cᵒᵖ)
    (m : M.val.obj X) (hm : g.val.app X m = 0) :
    ∃ k, (kernel.ι g).val.app X k = m := by
  let F := SheafOfModules.evaluation R X
  let e : F.obj (kernel g) ≅ kernel (F.map g) := PreservesKernel.iso F g
  have he : e.hom ≫ kernel.ι (F.map g) = F.map (kernel.ι g) := by simp [e]
  let k0 : ((kernel (F.map g) : ModuleCat _) : Type) :=
    (ModuleCat.kernelIsoKer (F.map g)).inv ⟨m, hm⟩
  refine ⟨e.inv k0, ?_⟩
  have h1 : (kernel.ι (F.map g)) k0 = m := by
    simp only [k0]
    rw [← ConcreteCategory.comp_apply, ModuleCat.kernelIsoKer_inv_kernel_ι]
    rfl
  rw [← h1]
  change (F.map (kernel.ι g)) (e.inv k0) = _
  rw [← he, ← ConcreteCategory.comp_apply, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- Sections of the kernel of `g` are killed by `g`. -/
theorem kernel_condition_app {M N : SheafOfModules.{0} R} (g : M ⟶ N) (X : Cᵒᵖ)
    (k : (kernel g).val.obj X) : g.val.app X ((kernel.ι g).val.app X k) = 0 := by
  change (kernel.ι g ≫ g).val.app X k = 0
  rw [kernel.condition]; rfl

/-- A morphism of sheaves of modules which is locally surjective on sections is an epimorphism. -/
theorem epi_of_locally_surjective {P Q : SheafOfModules.{0} R} (φ : P ⟶ Q)
    (h : ∀ (X : C) (q : Q.val.obj (op X)), ∃ S ∈ J X, ∀ (Y : C) (f : Y ⟶ X), S f →
      ∃ p : P.val.obj (op Y), φ.val.app (op Y) p = Q.val.map f.op q) : Epi φ := by
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map φ) := by
    refine ⟨fun {X} q => ?_⟩
    obtain ⟨S, hS, hf⟩ := h X q
    refine J.superset_covering ?_ hS
    intro Y f hf'
    exact hf Y f hf'
  have : Epi ((SheafOfModules.toSheaf R).map φ) := inferInstance
  exact (SheafOfModules.toSheaf R).epi_of_epi_map this

/-- The morphism from a free module given by sections sends `eᵢ` to the `i`-th section. -/
theorem freeHomEquiv_symm_app_freeSection {P : SheafOfModules.{0} R} {I : Type}
    (t : I → P.sections) (i : I) (X : Cᵒᵖ) :
    (P.freeHomEquiv.symm t).val.app X ((SheafOfModules.freeSection (R := R) i).1 X) =
      (t i).1 X := by
  have := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection (M := P) t i
  exact congrArg (fun s : P.sections => s.1 X) this

/-- The kernel of `g : M ⟶ N` is of finite type if, over each member of a family covering the
terminal object, finitely many sections of `M` killed by `g` locally generate every section
killed by `g`. -/
theorem isFiniteType_kernel_of_local {M N : SheafOfModules.{0} R} (g : M ⟶ N)
    [HasPullbacks C]
    {I : Type} {Y : I → C} (hY : J.CoversTop Y)
    (s : I → ℕ) (r : ∀ i, Fin (s i) → M.val.obj (op (Y i)))
    (hr : ∀ i k, g.val.app _ (r i k) = 0)
    (hgen : ∀ i (Z : C) (z : Z ⟶ Y i) (m : M.val.obj (op Z)), g.val.app _ m = 0 →
      ∃ S ∈ J Z, ∀ (W : C) (f : W ⟶ Z), S f → ∃ c : Fin (s i) → R.obj.obj (op W),
        M.val.map f.op m = ∑ k, c k • M.val.map (f ≫ z).op (r i k)) :
    SheafOfModules.IsFiniteType.{0} (kernel g) := by
  refine MMP.isFiniteType_of_coversTop (kernel g) hY fun i => ?_
  choose kk hkk using fun k => exists_kernel_ι_app_eq g _ (r i k) (hr i k)
  let t : Fin (s i) → ((kernel g).over (Y i)).sections := fun k => overSection _ (kk k)
  have hepi : Epi (((kernel g).over (Y i)).freeHomEquiv.symm t) := by
    refine epi_of_locally_surjective _ fun U q => ?_
    obtain ⟨S, hS, hSc⟩ := hgen i U.left U.hom ((kernel.ι g).val.app _ q)
      (kernel_condition_app g _ q)
    refine ⟨(Sieve.overEquiv U).symm S, ?_, fun W f hf => ?_⟩
    · rw [GrothendieckTopology.mem_over_iff]; simpa using hS
    · rw [Sieve.overEquiv_symm_iff] at hf
      obtain ⟨c, hc⟩ := hSc W.left f.left hf
      let e : Fin (s i) → (SheafOfModules.free (R := R.over (Y i)) (Fin (s i))).val.obj (op W) :=
        fun k => (SheafOfModules.freeSection (R := (R.over (Y i))) k).1 (op W)
      let c' : Fin (s i) → (R.over (Y i)).obj.obj (op W) := c
      refine ⟨∑ k, c' k • e k, ?_⟩
      apply kernel_ι_app_injective g
      rw [map_sum]
      simp only [map_smul]
      have he : ∀ k, (((kernel g).over (Y i)).freeHomEquiv.symm t).val.app (op W) (e k) =
          (t k).1 (op W) := fun k => freeHomEquiv_symm_app_freeSection t k (op W)
      simp only [he]
      change (kernel.ι g).val.app (op W.left)
          (∑ k, c k • ((kernel g).val.map W.hom.op (kk k) : (kernel g).val.obj (op W.left))) =
        (kernel.ι g).val.app (op W.left) ((kernel g).val.map f.left.op q)
      erw [map_sum]
      simp only [map_smul]
      erw [PresheafOfModules.naturality_apply]
      rw [hc, Over.w f]
      refine Finset.sum_congr rfl fun k _ => ?_
      erw [map_smul, PresheafOfModules.naturality_apply, hkk]
      rfl
  haveI : HasBinaryProducts (Over (Y i)) := Over.ConstructProducts.over_binaryProduct_of_pullback
  let G : ((kernel g).over (Y i)).GeneratingSections := ⟨Fin (s i), t, hepi⟩
  haveI : G.IsFiniteType := ⟨inferInstanceAs (Finite (Fin (s i)))⟩
  exact ⟨⟨G.localGeneratorsData, ⟨fun _ => ⟨inferInstanceAs (Finite (Fin (s i)))⟩⟩⟩⟩

/-- The value of a section at an object. -/
abbrev secAt {P : SheafOfModules.{0} R} (s : P.sections) (X : Cᵒᵖ) : P.val.obj X := s.1 X

/-- The tautological section `eᵢ` of a free module over `X`. -/
noncomputable abbrev freeElt {I : Type} (i : I) (X : Cᵒᵖ) :
    (SheafOfModules.free (R := R) I).val.obj X :=
  (SheafOfModules.freeSection (R := R) i).1 X

/-- Restriction of the tautological sections of a free module. -/
theorem free_map_freeElt {I : Type} (i : I) {X X' : Cᵒᵖ} (h : X ⟶ X') :
    (SheafOfModules.free (R := R) I).val.map h (freeElt i X) = freeElt i X' :=
  PresheafOfModules.sections_property _ h

/-- Restriction of a linear combination of tautological sections. -/
theorem free_map_sum_smul {I : Type} [Fintype I] {X X' : Cᵒᵖ} (h : X ⟶ X')
    (a : I → R.obj.obj X) :
    (SheafOfModules.free (R := R) I).val.map h (∑ i, a i • freeElt i X) =
      ∑ i, R.obj.map h (a i) • freeElt i X' := by
  erw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [PresheafOfModules.map_smul, free_map_freeElt]
  rfl

/-- Comparing linear combinations of tautological sections by their coefficients. -/
theorem free_sum_smul_eq_sum_smul {p s : ℕ} {X : Cᵒᵖ} (a : Fin p → R.obj.obj X)
    (c : Fin s → R.obj.obj X) (b : Fin s → Fin p → R.obj.obj X)
    (h : ∀ i, a i = ∑ k, c k * b k i) :
    ∑ i, a i • freeElt (R := R) i X = ∑ k, c k • ∑ i, b k i • freeElt (R := R) i X := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, h]

/-- The morphism from a free module given by sections, on a linear combination. -/
theorem freeHomEquiv_symm_app_sum {P : SheafOfModules.{0} R} {I : Type} [Fintype I]
    (t : I → P.sections) (X : Cᵒᵖ) (a : I → R.obj.obj X) :
    (P.freeHomEquiv.symm t).val.app X (∑ i, a i • freeElt i X) = ∑ i, a i • secAt (t i) X := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  exact congrArg _ (freeHomEquiv_symm_app_freeSection t i X)

/-- The value of a section of a restriction `N|_Z` at `U : Over Z`. -/
lemma over_section_eq {N : SheafOfModules.{0} R} {Z : C} (σ : (N.over Z).sections)
    (U : Over Z) : secAt σ (op U) = N.val.map U.hom.op (secAt σ (op (Over.mk (𝟙 Z)))) :=
  (PresheafOfModules.sections_property σ (Over.homMk (U := U) (V := Over.mk (𝟙 Z)) U.hom
    (by simp)).op).symm

/-- The unit module is generated by its unit section. -/
theorem isFiniteType_unit [HasBinaryProducts C] :
    SheafOfModules.IsFiniteType.{0} (SheafOfModules.unit R) := by
  let t : Unit → (SheafOfModules.unit R).sections := fun _ =>
    (SheafOfModules.unit R).unitHomEquiv (𝟙 _)
  have hepi : Epi ((SheafOfModules.unit R).freeHomEquiv.symm t) := by
    refine epi_of_locally_surjective _ fun X q => ⟨⊤, J.top_mem X, fun Y f _ => ?_⟩
    refine ⟨(R.obj.map f.op q : R.obj.obj (op Y)) • freeElt (R := R) () (op Y), ?_⟩
    rw [map_smul]
    erw [freeHomEquiv_symm_app_freeSection t () (op Y)]
    exact mul_one (R.obj.map f.op q : R.obj.obj (op Y))
  let G : (SheafOfModules.unit R).GeneratingSections := ⟨Unit, t, hepi⟩
  haveI : G.IsFiniteType := ⟨inferInstanceAs (Finite Unit)⟩
  exact ⟨⟨G.localGeneratorsData, ⟨fun _ => ⟨inferInstanceAs (Finite Unit)⟩⟩⟩⟩

end Site

/-! ### Restriction of sections of a sheaf of rings, and relations among them -/

section Top

open TopologicalSpace

variable {T : TopCat.{0}} {A : TopCat.Sheaf RingCat.{0} T}

/-- Restriction of a section of `A` along an inclusion of opens. -/
abbrev res {U U' : Opens T} (h : U' ≤ U) (a : A.obj.obj (op U)) : A.obj.obj (op U') :=
  A.obj.map (homOfLE h).op a

/-- Restriction is transitive. -/
lemma res_res {U U' U'' : Opens T} (h : U' ≤ U) (h' : U'' ≤ U') (a : A.obj.obj (op U)) :
    res (A := A) h' (res h a) = res (h'.trans h) a := by
  simp only [res]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction is multiplicative. -/
lemma res_mul {U U' : Opens T} (h : U' ≤ U) (a b : A.obj.obj (op U)) :
    res (A := A) h (a * b) = res h a * res h b :=
  map_mul (A.obj.map (homOfLE h).op).hom a b

/-- Restriction is additive. -/
lemma res_sum {U U' : Opens T} (h : U' ≤ U) {s : ℕ} (a : Fin s → A.obj.obj (op U)) :
    res (A := A) h (∑ k, a k) = ∑ k, res h (a k) :=
  map_sum (A.obj.map (homOfLE h).op).hom a _

/-- Restriction commutes with negation. -/
lemma res_neg {U U' : Opens T} (h : U' ≤ U) (a : A.obj.obj (op U)) :
    res (A := A) h (-a) = -res h a :=
  map_neg (A.obj.map (homOfLE h).op).hom a

/-- A section of `A` over `Z.left`, seen as a section of `A|_V` over `Z`. -/
abbrev toOver {V : Opens T} (Z : Over V) (a : A.obj.obj (op Z.left)) :
    (A.over V).obj.obj (op Z) :=
  a

/-- The relations among `p` vectors of `A(V)^q` are locally finitely generated: near every
point there are finitely many relations which locally generate all relations over smaller
opens. -/
def RelationsLocallyFinite (A : TopCat.Sheaf RingCat.{0} T) (q : ℕ) : Prop :=
  ∀ (V : Opens T) (p : ℕ) (F : Fin p → Fin q → A.obj.obj (op V)) (x : T), x ∈ V →
    ∃ (W : Opens T) (hWV : W ≤ V), x ∈ W ∧ ∃ (s : ℕ) (r : Fin s → Fin p → A.obj.obj (op W)),
      (∀ k j, ∑ i, r k i * res hWV (F i j) = 0) ∧
      ∀ (U : Opens T) (hUW : U ≤ W) (a : Fin p → A.obj.obj (op U)),
        (∀ j, ∑ i, a i * res (hUW.trans hWV) (F i j) = 0) →
        ∀ y ∈ U, ∃ (U' : Opens T) (hU' : U' ≤ U), y ∈ U' ∧ ∃ c : Fin s → A.obj.obj (op U'),
          ∀ i, res hU' (a i) = ∑ k, c k * res (hU'.trans hUW) (r k i)

end Top

/-! ### Coherent modules and finite presentations -/

section FreeCoordinates

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- The `k`-th coordinate of the tautological section `eⱼ`. -/
theorem freeProj_freeElt {I : Type} [DecidableEq I] {X : Cᵒᵖ} (j k : I) :
    (MMP.freeProj (R := R) k).val.app X (freeElt j X) =
      (show (SheafOfModules.unit R).val.obj X from
        if j = k then (1 : R.obj.obj X) else 0) := by
  have h1 := MMP.ιFree_val_app (R := R) (I := I) j X 1
  rw [one_smul] at h1
  have h2 : freeElt (R := R) (I := I) j X =
      (SheafOfModules.ιFree (R := R) j).val.app X (1 : R.obj.obj X) := h1.symm
  rw [h2]
  change ((SheafOfModules.ιFree j ≫ MMP.freeProj k).val.app X) (1 : R.obj.obj X) = _
  rw [MMP.ιFree_freeProj]
  by_cases h : j = k
  · simp only [h, if_true]
    rfl
  · simp only [h, if_false]
    rfl

/-- The coordinates of a linear combination of tautological sections. -/
theorem freeProj_sum_smul {I : Type} [Fintype I] [DecidableEq I] {X : Cᵒᵖ}
    (a : I → R.obj.obj X) (k : I) :
    (MMP.freeProj (R := R) k).val.app X (∑ j, a j • freeElt j X) = a k := by
  rw [map_sum]
  simp only [map_smul, freeProj_freeElt]
  change ∑ j, a j * (if j = k then (1 : R.obj.obj X) else 0) = a k
  simp

/-- A section of a free module of finite rank is the combination of its coordinates. -/
theorem eq_sum_freeProj_smul {I : Type} [Fintype I] [DecidableEq I] {X : Cᵒᵖ}
    (x : (SheafOfModules.free (R := R) I).val.obj X) :
    x = ∑ j, (show R.obj.obj X from (MMP.freeProj (R := R) j).val.app X x) • freeElt j X := by
  obtain ⟨a, rfl⟩ := MMP.exists_eq_sum_smul_freeSection X x
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact (freeProj_sum_smul a j).symm

/-- Linear combinations of tautological sections with the same value have the same
coefficients. -/
theorem coeff_eq_of_sum_smul_eq {I : Type} [Fintype I] [DecidableEq I] {X : Cᵒᵖ}
    {a b : I → R.obj.obj X}
    (h : ∑ j, a j • freeElt (R := R) j X = ∑ j, b j • freeElt (R := R) j X) (k : I) :
    a k = b k := by
  rw [← freeProj_sum_smul a k, h, freeProj_sum_smul]

/-- An epimorphism of sheaves of modules is locally surjective on sections. -/
lemma exists_local_lift {M' N : SheafOfModules.{0} R} (π : M' ⟶ N) [Epi π] {V : C}
    (n : N.val.obj (op V)) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), S g →
      ∃ t : M'.val.obj (op W), π.val.app (op W) t = N.val.map g.op n :=
  Stacks.SheafOfModules.EpiMono.exists_covering_of_epi π n

/-- Regrouping a double linear combination. -/
lemma sum_smul_sum_smul {S N : Type} [Ring S] [AddCommGroup N] [Module S N] {I L : Type}
    [Fintype I] [Fintype L] (d : I → S) (x : I → L → S) (v : L → N) :
    ∑ k, d k • ∑ l, x k l • v l = ∑ l, (∑ k, d k * x k l) • v l := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

end FreeCoordinates

section Rows

open TopologicalSpace

variable {T : TopCat.{0}} {A : TopCat.Sheaf RingCat.{0} T}

/-- Restriction along `U ≤ U` is the identity. -/
lemma res_self {U : Opens T} (h : U ≤ U) (a : A.obj.obj (op U)) : res (A := A) h a = a := by
  simp only [res]
  rw [show homOfLE h = 𝟙 U from Subsingleton.elim _ _, op_id, A.obj.map_id]
  rfl

/-- Restriction sends `1` to `1`. -/
lemma res_one {U U' : Opens T} (h : U' ≤ U) : res (A := A) h 1 = 1 :=
  map_one (A.obj.map (homOfLE h).op).hom

/-- Restriction sends `0` to `0`. -/
lemma res_zero {U U' : Opens T} (h : U' ≤ U) : res (A := A) h 0 = 0 :=
  map_zero (A.obj.map (homOfLE h).op).hom

/-- Relations among vectors of length `0`: every vector is a relation. -/
theorem relationsLocallyFinite_zero : RelationsLocallyFinite A 0 := by
  classical
  intro V p F x hx
  refine ⟨V, le_rfl, hx, p, fun k i => if k = i then 1 else 0, fun k j => j.elim0,
    fun U hUW a _ y hy => ⟨U, le_rfl, hy, a, fun i => ?_⟩⟩
  rw [res_self, Finset.sum_eq_single i]
  · simp only [if_true, res_one, mul_one]
  · intro k _ hk
    simp only [if_neg hk, res_zero, mul_zero]
  · simp

/-- **Reduction to one row** for relations among sections of a sheaf of rings. -/
theorem relationsLocallyFinite_succ {q : ℕ} (h1 : RelationsLocallyFinite A 1)
    (hq : RelationsLocallyFinite A q) : RelationsLocallyFinite A (q + 1) := by
  intro V p F x hx
  obtain ⟨W₁, hW₁V, hx₁, s₁, r, hr, hgr⟩ := h1 V p (fun i _ => F i (Fin.last q)) x hx
  let G : Fin s₁ → Fin q → A.obj.obj (op W₁) := fun k j =>
    ∑ i, r k i * res hW₁V (F i j.castSucc)
  obtain ⟨W₂, hW₂W₁, hx₂, s₂, t, ht, hgt⟩ := hq W₁ s₁ G x hx₁
  refine ⟨W₂, hW₂W₁.trans hW₁V, hx₂, s₂, fun l i => ∑ k, t l k * res hW₂W₁ (r k i),
    fun l j => ?_, fun U hUW a ha y hy => ?_⟩
  · have key : ∑ i, (∑ k, t l k * res hW₂W₁ (r k i)) * res (hW₂W₁.trans hW₁V) (F i j) =
        ∑ k, t l k * res hW₂W₁ (∑ i, r k i * res hW₁V (F i j)) := by
      simp only [res_sum, res_mul, res_res, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    rw [key]
    induction j using Fin.lastCases with
    | last => simp [hr _ 0, res_zero]
    | cast j => exact ht l j
  · obtain ⟨U₁, hU₁U, hy₁, c, hc⟩ :=
      hgr U (hUW.trans hW₂W₁) a (fun _ => ha (Fin.last q)) y hy
    have hcG : ∀ j, ∑ k, c k * res (hU₁U.trans (hUW.trans hW₂W₁)) (G k j) = 0 := by
      intro j
      have e : ∑ k, c k * res (hU₁U.trans (hUW.trans hW₂W₁)) (G k j) =
          res hU₁U (∑ i, a i * res (hUW.trans (hW₂W₁.trans hW₁V)) (F i j.castSucc)) := by
        simp only [G, res_sum, res_mul, res_res, hc, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      rw [e, ha j.castSucc, res_zero]
    obtain ⟨U₂, hU₂U₁, hy₂, d, hd⟩ := hgt U₁ (hU₁U.trans hUW) c hcG y hy₁
    refine ⟨U₂, hU₂U₁.trans hU₁U, hy₂, d, fun i => ?_⟩
    have e1 : res (hU₂U₁.trans hU₁U) (a i) = res hU₂U₁ (res hU₁U (a i)) := (res_res _ _ _).symm
    rw [e1, hc i]
    simp only [res_sum, res_mul, res_res, hd, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

/-- Relations among vectors of any length are locally finitely generated once relations among
sections are. -/
theorem relationsLocallyFinite_of_one (h1 : RelationsLocallyFinite A 1) (q : ℕ) :
    RelationsLocallyFinite A q := by
  induction q with
  | zero => exact relationsLocallyFinite_zero
  | succ q ih => exact relationsLocallyFinite_succ h1 ih

end Rows

section ModuleCriterion

open TopologicalSpace

variable {T : TopCat.{0}} {A : TopCat.Sheaf RingCat.{0} T}

/-- Restriction of a section of a sheaf of modules along an inclusion of opens. -/
noncomputable abbrev mres {M : SheafOfModules.{0} A} {U U' : Opens T} (h : U' ≤ U)
    (m : M.val.obj (op U)) : M.val.obj (op U') :=
  M.val.map (homOfLE h).op m

/-- The relations among finitely many sections of a sheaf of modules `M` are locally finitely
generated. -/
def ModuleRelationsLocallyFinite (M : SheafOfModules.{0} A) : Prop :=
  ∀ (V : Opens T) (p : ℕ) (f : Fin p → M.val.obj (op V)) (x : T), x ∈ V →
    ∃ (W : Opens T) (hWV : W ≤ V), x ∈ W ∧ ∃ (s : ℕ) (r : Fin s → Fin p → A.obj.obj (op W)),
      (∀ k, ∑ i, r k i • mres (M := M) hWV (f i) = 0) ∧
      ∀ (U : Opens T) (hUW : U ≤ W) (a : Fin p → A.obj.obj (op U)),
        ∑ i, a i • mres (M := M) (hUW.trans hWV) (f i) = 0 →
        ∀ y ∈ U, ∃ (U' : Opens T) (hU' : U' ≤ U), y ∈ U' ∧ ∃ c : Fin s → A.obj.obj (op U'),
          ∀ i, res hU' (a i) = ∑ k, c k * res (hU'.trans hUW) (r k i)

/-- **A criterion for coherence of a sheaf of modules.** -/
theorem isCoherentModule_of_relations {M : SheafOfModules.{0} A}
    (hM : SheafOfModules.IsFiniteType.{0} M) (h : ModuleRelationsLocallyFinite M) :
    IsCoherentModule M := by
  refine ⟨hM, fun V p σ => ?_⟩
  let g := (M.over V).freeHomEquiv.symm σ
  let f : Fin p → M.val.obj (op V) := fun i => secAt (σ i) (op (Over.mk (𝟙 V)))
  have hg : ∀ (Z : Over V) (a : Fin p → A.obj.obj (op Z.left)),
      g.val.app (op Z) (∑ i, toOver Z (a i) • freeElt (R := A.over V) i (op Z)) =
        ∑ i, a i • mres (M := M) Z.hom.le (f i) := by
    intro Z a
    rw [freeHomEquiv_symm_app_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [over_section_eq]
    rfl
  choose W hWV hxW s r hr hgen using fun x : V => h V p f x.1 x.2
  let Y : V → Over V := fun x => Over.mk (homOfLE (hWV x))
  refine isFiniteType_kernel_of_local g (Y := Y) ?_ s
    (fun x k => ∑ i, toOver (Y x) (r x k i) •
      freeElt (R := A.over V) i (op (Y x))) (fun x k => ?_) ?_
  · intro U
    rw [GrothendieckTopology.mem_over_iff]
    intro y hy
    let x : V := ⟨y, U.hom.le hy⟩
    refine ⟨U.left ⊓ W x, homOfLE inf_le_left, ?_, ⟨hy, hxW x⟩⟩
    rw [Sieve.overEquiv_iff, Sieve.mem_ofObjects_iff]
    exact ⟨x, ⟨Over.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _)⟩⟩
  · exact (hg (Y x) (r x k)).trans (hr x k)
  · intro x Z z m hm
    obtain ⟨a, rfl⟩ := MMP.exists_eq_sum_smul_freeSection (op Z) m
    have hZW : Z.left ≤ W x := z.left.le
    let a' : Fin p → A.obj.obj (op Z.left) := a
    have hm' : ∑ i, a' i • mres (M := M) (hZW.trans (hWV x)) (f i) = 0 :=
      (hg Z a').symm.trans hm
    choose U' hU' hyU' c hc using hgen x Z.left hZW a' hm'
    let S : Sieve Z :=
      { arrows := fun W' _ => ∃ y : Z.left, W'.left ≤ U' y.1 y.2
        downward_closed := fun {W' W''} _ ⟨y, hy⟩ g => ⟨y, g.left.le.trans hy⟩ }
    refine ⟨S, ?_, ?_⟩
    · rw [GrothendieckTopology.mem_over_iff]
      intro y hy
      refine ⟨U' y hy, homOfLE (hU' y hy), ?_, hyU' y hy⟩
      rw [Sieve.overEquiv_iff]
      exact ⟨⟨y, hy⟩, le_rfl⟩
    · rintro W' φ ⟨⟨y, hy⟩, hle⟩
      refine ⟨fun k => toOver W' (res hle (c y hy k)), (free_map_sum_smul φ.op a).trans ?_⟩
      simp only [free_map_sum_smul]
      refine free_sum_smul_eq_sum_smul _ _ _ fun i => ?_
      have key := congrArg (res (A := A) hle) (hc y hy i)
      rw [res_res, res_sum] at key
      simp only [res_mul, res_res] at key
      exact key

/-- **A criterion for coherence of a sheaf of rings.** A sheaf of rings whose relations among
finitely many sections are locally finitely generated is coherent. -/
theorem isCoherentRing_of_relationsLocallyFinite (h1 : RelationsLocallyFinite A 1) :
    IsCoherentRing A :=
  isCoherentModule_of_relations isFiniteType_unit fun V p f x hx => by
    obtain ⟨W, hWV, hxW, s, r, hr, hg⟩ := h1 V p (fun i _ => f i) x hx
    exact ⟨W, hWV, hxW, s, r, fun k => hr k 0, fun U hUW a ha => hg U hUW a fun _ => ha⟩

end ModuleCriterion

section Presentations

open TopologicalSpace

variable {T : TopCat.{0}} {A : TopCat.Sheaf RingCat.{0} T}

/-- Restriction of sections of a sheaf of modules is transitive. -/
lemma mres_mres {M : SheafOfModules.{0} A} {U U' U'' : Opens T} (h : U' ≤ U)
    (h' : U'' ≤ U') (m : M.val.obj (op U)) :
    mres (M := M) h' (mres h m) = mres (h'.trans h) m := by
  simp only [mres]
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- Restriction of a scalar multiple is the product of the restrictions. -/
lemma mres_smul {M : SheafOfModules.{0} A} {U U' : Opens T} (h : U' ≤ U)
    (a : A.obj.obj (op U)) (m : M.val.obj (op U)) :
    mres (M := M) h (a • m) = res h a • mres h m :=
  M.val.map_smul _ a m

/-- Restriction of sections of a sheaf of modules commutes with finite sums. -/
lemma mres_sum {M : SheafOfModules.{0} A} {U U' : Opens T} (h : U' ≤ U) {ι : Type}
    (s : Finset ι) (m : ι → M.val.obj (op U)) :
    mres (M := M) h (∑ i ∈ s, m i) = ∑ i ∈ s, mres h (m i) :=
  map_sum (M.val.map (homOfLE h).op).hom m s

/-- Restriction of sections of a sheaf of modules sends `0` to `0`. -/
lemma mres_zero {M : SheafOfModules.{0} A} {U U' : Opens T} (h : U' ≤ U) :
    mres (M := M) h 0 = 0 :=
  map_zero (M.val.map (homOfLE h).op).hom

/-- Reindexing generating sections along an equivalence keeps them generating. -/
lemma epi_freeHomEquiv_symm_comp {C : Type} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {M : SheafOfModules.{0} R} {I I' : Type} [Fintype I]
    [Fintype I'] (t : I → M.sections) (e : I' ≃ I) [Epi (M.freeHomEquiv.symm t)] :
    Epi (M.freeHomEquiv.symm (t ∘ e)) := by
  classical
  refine epi_of_locally_surjective _ fun X q => ?_
  obtain ⟨S, hS, hSc⟩ := exists_local_lift (M.freeHomEquiv.symm t) q
  refine ⟨S, hS, fun Y f hf => ?_⟩
  obtain ⟨u, hu⟩ := hSc f hf
  obtain ⟨c, rfl⟩ := MMP.exists_eq_sum_smul_freeSection _ u
  refine ⟨∑ j, c (e j) • freeElt j (op Y), ?_⟩
  rw [freeHomEquiv_symm_app_sum] at hu ⊢
  rw [← hu]
  exact Equiv.sum_comp e (fun l => c l • secAt (t l) (op Y))

/-- **Local generation by generating sections.** -/
lemma exists_local_combination {X0 : Opens T} {M : SheafOfModules.{0} A}
    (G : (M.over X0).GeneratingSections) [Fintype G.I] [DecidableEq G.I] (Z : Over X0)
    (m : M.val.obj (op Z.left)) (y : T) (hy : y ∈ Z.left) :
    ∃ (Z' : Opens T) (hZ' : Z' ≤ Z.left), y ∈ Z' ∧ ∃ c : G.I → A.obj.obj (op Z'),
      mres hZ' m = ∑ l, c l • mres (M := M) (hZ'.trans Z.hom.le)
        (secAt (G.s l) (op (Over.mk (𝟙 X0)))) := by
  haveI := G.epi
  obtain ⟨S, hS, hSc⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi G.π (V := Z) m
  rw [GrothendieckTopology.mem_over_iff] at hS
  obtain ⟨W, w, hw, hyW⟩ := hS y hy
  rw [Sieve.overEquiv_iff] at hw
  obtain ⟨u, hu⟩ := hSc _ hw
  obtain ⟨c, rfl⟩ := MMP.exists_eq_sum_smul_freeSection _ u
  refine ⟨W, w.le, hyW, c, ?_⟩
  have h1 : G.π.val.app (op (Over.mk (w ≫ Z.hom))) (∑ l, c l • freeElt l _) =
      ∑ l, c l • secAt (G.s l) (op (Over.mk (w ≫ Z.hom))) :=
    freeHomEquiv_symm_app_sum G.s _ c
  refine hu.symm.trans (h1.trans (Finset.sum_congr rfl fun l _ => ?_))
  erw [over_section_eq]
  rfl

section Relations

variable {X0 : Opens T} {M : SheafOfModules.{0} A} (P : (M.over X0).Presentation)
  [Fintype P.generators.I] [DecidableEq P.generators.I] [Fintype P.relations.I]

/-- The value at `X0` of the generators of a presentation. -/
noncomputable abbrev genTop (l : P.generators.I) : M.val.obj (op X0) :=
  secAt (P.generators.s l) (op (Over.mk (𝟙 X0)))

/-- The coordinates of the relations of a presentation. -/
noncomputable abbrev relCoord (e : P.relations.I) (l : P.generators.I) :
    A.obj.obj (op X0) :=
  (show (A.over X0).obj.obj (op (Over.mk (𝟙 X0))) from
    (MMP.freeProj l).val.app (op (Over.mk (𝟙 X0)))
      ((kernel.ι P.generators.π).val.app (op (Over.mk (𝟙 X0)))
        (secAt (P.relations.s e) (op (Over.mk (𝟙 X0))))))

/-- The relations of a presentation are relations among the generators. -/
lemma sum_relCoord_smul_genTop (e : P.relations.I) :
    ∑ l, relCoord P e l • genTop P l = 0 := by
  have h0 := kernel_condition_app P.generators.π (op (Over.mk (𝟙 X0)))
    (secAt (P.relations.s e) (op (Over.mk (𝟙 X0))))
  rw [eq_sum_freeProj_smul ((kernel.ι P.generators.π).val.app _ _),
    freeHomEquiv_symm_app_sum] at h0
  exact h0

/-- The relations of a presentation, as sections of the free module, in coordinates. -/
lemma kernel_ι_relations (e : P.relations.I) (Y : Over X0) :
    (kernel.ι P.generators.π).val.app (op Y) (secAt (P.relations.s e) (op Y)) =
      ∑ l, toOver Y (res Y.hom.le (relCoord P e l)) • freeElt (R := A.over X0) l (op Y) := by
  have hs := PresheafOfModules.sections_property (P.relations.s e)
    (Over.homMk (U := Y) (V := Over.mk (𝟙 X0)) Y.hom (by simp)).op
  have hs' : secAt (P.relations.s e) (op Y) =
      (kernel P.generators.π).val.map (Over.homMk (U := Y) (V := Over.mk (𝟙 X0)) Y.hom
        (by simp)).op (secAt (P.relations.s e) (op (Over.mk (𝟙 X0)))) := hs.symm
  rw [hs', PresheafOfModules.naturality_apply,
    eq_sum_freeProj_smul ((kernel.ι P.generators.π).val.app _ _), free_map_sum_smul]
  rfl

/-- **The relations of a presentation generate all relations among the generators, locally.** -/
lemma exists_local_relCoord (Z : Over X0) (c : P.generators.I → A.obj.obj (op Z.left))
    (hc : ∑ l, c l • mres (M := M) Z.hom.le (genTop P l) = 0) (y : T) (hy : y ∈ Z.left) :
    ∃ (Z' : Opens T) (hZ' : Z' ≤ Z.left), y ∈ Z' ∧ ∃ d : P.relations.I → A.obj.obj (op Z'),
      ∀ l, res hZ' (c l) = ∑ e, d e * res (hZ'.trans Z.hom.le) (relCoord P e l) := by
  classical
  have hw : P.generators.π.val.app (op Z)
      (∑ l, toOver Z (c l) • freeElt (R := A.over X0) l (op Z)) = 0 := by
    rw [freeHomEquiv_symm_app_sum]
    refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) hc
    erw [over_section_eq]
    rfl
  obtain ⟨k, hk⟩ := exists_kernel_ι_app_eq P.generators.π (op Z) _ hw
  haveI := P.relations.epi
  obtain ⟨S, hS, hSc⟩ := exists_local_lift P.relations.π (V := Z) k
  rw [GrothendieckTopology.mem_over_iff] at hS
  obtain ⟨W, wf, hw', hyW⟩ := hS y hy
  rw [Sieve.overEquiv_iff] at hw'
  obtain ⟨v, hv⟩ := hSc _ hw'
  obtain ⟨d, rfl⟩ := MMP.exists_eq_sum_smul_freeSection _ v
  refine ⟨W, wf.le, hyW, d, fun l => ?_⟩
  have hrel := fun e => kernel_ι_relations P e (Over.mk (wf ≫ Z.hom))
  have hv' : ∑ e, d e • secAt (P.relations.s e) (op (Over.mk (wf ≫ Z.hom))) =
      (kernel P.generators.π).val.map (Over.homMk (U := Over.mk (wf ≫ Z.hom)) (V := Z) wf).op k :=
    (freeHomEquiv_symm_app_sum P.relations.s _ d).symm.trans hv
  have h1 := congrArg ((kernel.ι P.generators.π).val.app (op (Over.mk (wf ≫ Z.hom)))) hv'
  have hL : (kernel.ι P.generators.π).val.app (op (Over.mk (wf ≫ Z.hom)))
      (∑ e, d e • secAt (P.relations.s e) (op (Over.mk (wf ≫ Z.hom)))) =
        ∑ e, d e • ∑ l, toOver (Over.mk (wf ≫ Z.hom)) (res (wf.le.trans Z.hom.le)
          (relCoord P e l)) • freeElt (R := A.over X0) l (op (Over.mk (wf ≫ Z.hom))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_smul, hrel e]
  have hR : (kernel.ι P.generators.π).val.app (op (Over.mk (wf ≫ Z.hom)))
      ((kernel P.generators.π).val.map (Over.homMk (U := Over.mk (wf ≫ Z.hom)) (V := Z) wf).op k) =
        ∑ l, toOver (Over.mk (wf ≫ Z.hom)) (res wf.le (c l)) •
          freeElt (R := A.over X0) l (op (Over.mk (wf ≫ Z.hom))) := by
    rw [PresheafOfModules.naturality_apply, hk, free_map_sum_smul]
    rfl
  let d' : P.relations.I → A.obj.obj (op W) := d
  have h2 : ∑ l, toOver (Over.mk (wf ≫ Z.hom))
        (∑ e, d' e * res (wf.le.trans Z.hom.le) (relCoord P e l)) •
          freeElt (R := A.over X0) l (op (Over.mk (wf ≫ Z.hom))) =
      ∑ l, toOver (Over.mk (wf ≫ Z.hom)) (res wf.le (c l)) •
          freeElt (R := A.over X0) l (op (Over.mk (wf ≫ Z.hom))) := by
    refine Eq.trans ?_ (hL.symm.trans (h1.trans hR))
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact Finset.sum_smul.trans (Finset.sum_congr rfl fun e _ => mul_smul _ _ _)
  exact (coeff_eq_of_sum_smul_eq h2 l).symm

end Relations

end Presentations

section FromPresentations

open TopologicalSpace

variable {T : TopCat.{0}} {A : TopCat.Sheaf RingCat.{0} T}

/-- **Module relations from local finite presentations.** If `M` has, near every point, a finite
presentation, and the relations among vectors over `A` are locally finitely generated, the
relations among sections of `M` are locally finitely generated. -/
theorem moduleRelationsLocallyFinite_of_presentation {M : SheafOfModules.{0} A}
    (hA : ∀ q, RelationsLocallyFinite A q)
    (hP : ∀ x : T, ∃ X0 : Opens T, x ∈ X0 ∧ ∃ P : (M.over X0).Presentation,
      Finite P.generators.I ∧ Finite P.relations.I) :
    ModuleRelationsLocallyFinite M := by
  classical
  intro V p f x hx
  obtain ⟨X0, hx0, P, hfg, hfr⟩ := hP x
  haveI := Fintype.ofFinite P.generators.I
  haveI := Fintype.ofFinite P.relations.I
  set b := Fintype.card P.generators.I
  set a := Fintype.card P.relations.I
  let eg : P.generators.I ≃ Fin b := Fintype.equivFin _
  let er : P.relations.I ≃ Fin a := Fintype.equivFin _
  let Z0 : Over X0 := Over.mk (homOfLE (inf_le_right : V ⊓ X0 ≤ X0))
  have hxZ0 : x ∈ Z0.left := ⟨hx, hx0⟩
  choose Zi hZi hxZi ci hci using fun i =>
    exists_local_combination P.generators Z0 (mres (M := M) inf_le_left (f i)) x hxZ0
  let Y1 : Opens T :=
    (V ⊓ X0) ⊓ ⟨⋂ i, (Zi i : Set T), isOpen_iInter_of_finite fun i => (Zi i).isOpen⟩
  have hY1i : ∀ i, Y1 ≤ Zi i := fun i z hz => Set.mem_iInter.1 hz.2 i
  have hY1V : Y1 ≤ V := fun z hz => hz.1.1
  have hY1X0 : Y1 ≤ X0 := fun z hz => hz.1.2
  have hxY1 : x ∈ Y1 := ⟨⟨hx, hx0⟩, Set.mem_iInter.2 hxZi⟩
  let σ : Fin p → Fin b → A.obj.obj (op Y1) := fun i l => res (hY1i i) (ci i (eg.symm l))
  have hσ : ∀ i, mres (M := M) hY1V (f i) =
      ∑ l, σ i l • mres (M := M) hY1X0 (genTop P (eg.symm l)) := by
    intro i
    have h := congrArg (mres (M := M) (hY1i i)) (hci i)
    rw [mres_mres, mres_mres, mres_sum] at h
    simp only [mres_smul, mres_mres] at h
    refine h.trans ?_
    rw [← Equiv.sum_comp eg.symm]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    exact mres_mres (M := M) _ _ _
  let H : Fin (p + a) → Fin b → A.obj.obj (op Y1) := fun m l =>
    Fin.addCases (fun i => σ i l) (fun e => -res hY1X0 (relCoord P (er.symm e) (eg.symm l))) m
  obtain ⟨W2, hW2, hxW2, s, R, hR, hgenR⟩ := hA b Y1 (p + a) H x hxY1
  have hRrel : ∀ k l, ∑ i, R k (Fin.castAdd a i) * res hW2 (σ i l) =
      ∑ e, R k (Fin.natAdd p e) * res (hW2.trans hY1X0) (relCoord P (er.symm e) (eg.symm l)) := by
    intro k l
    have h := hR k l
    rw [Fin.sum_univ_add] at h
    simp only [H, Fin.addCases_left, Fin.addCases_right, res_neg, res_res, mul_neg,
      Finset.sum_neg_distrib] at h
    exact sub_eq_zero.1 ((sub_eq_add_neg _ _).trans h)
  have hfU : ∀ {U : Opens T} (hU : U ≤ Y1) (i : Fin p), mres (M := M) (hU.trans hY1V) (f i) =
      ∑ l, res hU (σ i l) • mres (M := M) (hU.trans hY1X0) (genTop P (eg.symm l)) := by
    intro U hU i
    rw [← mres_mres (M := M) hY1V hU, hσ i, mres_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mres_smul, mres_mres]
  have hrelU : ∀ {U : Opens T} (hU : U ≤ X0) (e : P.relations.I),
      ∑ l, res hU (relCoord P e (eg.symm l)) • mres (M := M) hU (genTop P (eg.symm l)) = 0 := by
    intro U hU e
    have h0 := congrArg (mres (M := M) hU) (sum_relCoord_smul_genTop P e)
    rw [mres_sum, mres_zero] at h0
    rw [← h0, ← Equiv.sum_comp eg.symm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mres_smul]
  refine ⟨W2, hW2.trans hY1V, hxW2, s, fun k i => R k (Fin.castAdd a i), fun k => ?_,
    fun U hUW a' ha' y hy => ?_⟩
  · -- the `rᵏ` are relations
    simp only [hfU hW2, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hRrel]
    simp only [Finset.sum_smul, ← smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [← Finset.smul_sum, hrelU (hW2.trans hY1X0) (er.symm e), smul_zero]
  · -- the `rᵏ` generate
    let ZU : Over X0 := Over.mk (homOfLE (hUW.trans (hW2.trans hY1X0)))
    let c : P.generators.I → A.obj.obj (op U) := fun l' =>
      ∑ i, a' i * res (hUW.trans hW2) (σ i (eg l'))
    have hc : ∑ l', c l' • mres (M := M) ZU.hom.le (genTop P l') = 0 := by
      rw [← ha']
      simp only [hfU (hUW.trans hW2), Finset.smul_sum, smul_smul, c, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => (Fintype.sum_equiv eg.symm _ _ fun l => ?_).symm
      simp only [Equiv.apply_symm_apply]
    obtain ⟨U1, hU1, hy1, d, hd⟩ := exists_local_relCoord P ZU c hc y hy
    let a'' : Fin (p + a) → A.obj.obj (op U1) := fun m =>
      Fin.addCases (fun i => res hU1 (a' i)) (fun e => d (er.symm e)) m
    have hrel'' : ∀ l, ∑ m, a'' m * res (hU1.trans (hUW.trans hW2)) (H m l) = 0 := by
      intro l
      rw [Fin.sum_univ_add]
      simp only [a'', H, Fin.addCases_left, Fin.addCases_right]
      have h1 := hd (eg.symm l)
      simp only [c, Equiv.apply_symm_apply, res_sum, res_mul, res_res] at h1
      simp only [res_neg, res_res, mul_neg, Finset.sum_neg_distrib]
      rw [h1, ← Equiv.sum_comp er.symm, add_neg_eq_zero]
    obtain ⟨U2, hU2, hy2, C, hC⟩ := hgenR U1 (hU1.trans hUW) a'' hrel'' y hy1
    refine ⟨U2, hU2.trans hU1, hy2, C, fun i => ?_⟩
    have h := hC (Fin.castAdd a i)
    simp only [a'', Fin.addCases_left, res_res] at h
    exact h

end FromPresentations

section CoherentPresentation

open TopologicalSpace

variable {T : TopCat.{0}} {A : TopCat.Sheaf RingCat.{0} T}

/-- A point lies in a member of a family covering the terminal object. -/
lemma exists_mem_of_coversTop {I : Type} {X : I → Opens T}
    (hX : (Opens.grothendieckTopology T).CoversTop X) (x : T) : ∃ i, x ∈ X i := by
  obtain ⟨W, f, ⟨i, ⟨g⟩⟩, hxW⟩ := hX ⊤ x trivial
  exact ⟨i, g.le hxW⟩

/-- A point of `V` lies in the underlying open of a member of a family covering `V`. -/
lemma exists_mem_of_coversTop_over {V : Opens T} {I : Type} {X : I → Over V}
    (hX : ((Opens.grothendieckTopology T).over V).CoversTop X) (x : T) (hx : x ∈ V) :
    ∃ i, x ∈ (X i).left := by
  have h := hX (Over.mk (𝟙 V))
  rw [GrothendieckTopology.mem_over_iff] at h
  obtain ⟨W, f, hf, hxW⟩ := h x hx
  rw [Sieve.overEquiv_iff] at hf
  obtain ⟨i, ⟨g⟩⟩ := hf
  exact ⟨i, g.left.le hxW⟩

/-- **Local finite generation.** A sheaf of modules of finite type is generated by finitely many
sections near every point. -/
lemma exists_fin_generators {M : SheafOfModules.{0} A}
    (hM : SheafOfModules.IsFiniteType.{0} M) (x : T) :
    ∃ V : Opens T, x ∈ V ∧ ∃ (p : ℕ) (s : Fin p → (M.over V).sections),
      Epi ((M.over V).freeHomEquiv.symm s) := by
  obtain ⟨σ, hσ⟩ := hM.exists_localGeneratorsData
  obtain ⟨i, hi⟩ := exists_mem_of_coversTop σ.coversTop x
  have := hσ.isFiniteType i
  haveI := Fintype.ofFinite (σ.generators i).I
  haveI := (σ.generators i).epi
  exact ⟨σ.X i, hi, _, _, epi_freeHomEquiv_symm_comp (σ.generators i).s
    (Fintype.equivFin (σ.generators i).I).symm⟩

/-- The section of a sheaf of modules on `Over X0` given by its value at the terminal object. -/
noncomputable def topSection {X0 : Opens T}
    {R : Sheaf ((Opens.grothendieckTopology T).over X0) RingCat.{0}}
    (N : SheafOfModules.{0} R) (x : N.val.obj (op (Over.mk (𝟙 X0)))) : N.sections :=
  PresheafOfModules.sectionsMk
    (fun W => N.val.map (Over.homMk (U := W.unop) (V := Over.mk (𝟙 X0)) W.unop.hom (by simp)).op x)
    fun {W W'} f => by
      rw [← PresheafOfModules.map_comp_apply]
      rw [show (Over.homMk (U := W.unop) (V := Over.mk (𝟙 X0)) W.unop.hom (by simp)).op ≫ f =
        (Over.homMk (U := W'.unop) (V := Over.mk (𝟙 X0)) W'.unop.hom (by simp)).op from
        Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))]

/-- The value of `topSection N x` at `W` is the restriction of `x` to `W`. -/
lemma topSection_apply {X0 : Opens T}
    {R : Sheaf ((Opens.grothendieckTopology T).over X0) RingCat.{0}}
    (N : SheafOfModules.{0} R) (x : N.val.obj (op (Over.mk (𝟙 X0)))) (W : Over X0) :
    secAt (topSection N x) (op W) =
      N.val.map (Over.homMk (U := W) (V := Over.mk (𝟙 X0)) W.hom (by simp)).op x := rfl

/-- Transfer of covering sieves from `Over V` to `Over Z.left` for `Z : Over V`. -/
lemma exists_sieve_over_of_over {V : Opens T} (Z : Over V) (W : Over Z.left)
    (S' : Sieve (Over.mk (W.hom ≫ Z.hom)))
    (hS' : S' ∈ ((Opens.grothendieckTopology T).over V) (Over.mk (W.hom ≫ Z.hom))) :
    ∃ S : Sieve W, S ∈ ((Opens.grothendieckTopology T).over Z.left) W ∧
      ∀ ⦃Y : Over Z.left⦄ (f : Y ⟶ W), S f →
        S' (Over.homMk (U := Over.mk (f.left ≫ W.hom ≫ Z.hom)) (V := Over.mk (W.hom ≫ Z.hom))
          f.left (by simp)) := by
  refine ⟨(Sieve.overEquiv W).symm ((Sieve.overEquiv (Over.mk (W.hom ≫ Z.hom))) S'), ?_,
    fun Y f hf => ?_⟩
  · rw [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
    exact (GrothendieckTopology.mem_over_iff _ _).1 hS'
  · rw [Sieve.overEquiv_symm_iff, Sieve.overEquiv_iff] at hf
    exact hf

/-- Local generation by generating sections of a restriction `N|_Z`, read on `Over Z.left`. -/
lemma exists_local_combination_over {V : Opens T} {N : SheafOfModules.{0} (A.over V)}
    (Z : Over V) (H : (N.over Z).GeneratingSections) [Fintype H.I] (W : Over Z.left)
    (n : N.val.obj (op (Over.mk (W.hom ≫ Z.hom)))) :
    ∃ S : Sieve W, S ∈ ((Opens.grothendieckTopology T).over Z.left) W ∧
      ∀ ⦃Y : Over Z.left⦄ (f : Y ⟶ W), S f → ∃ d : H.I → A.obj.obj (op Y.left),
        N.val.map (Over.homMk (U := Over.mk (f.left ≫ W.hom ≫ Z.hom))
          (V := Over.mk (W.hom ≫ Z.hom)) f.left (by simp)).op n =
          ∑ k, toOver (Over.mk (f.left ≫ W.hom ≫ Z.hom)) (d k) •
            N.val.map (Over.homMk (U := Over.mk (f.left ≫ W.hom ≫ Z.hom)) (V := Z)
              (f.left ≫ W.hom) (by simp)).op (secAt (H.s k) (op (Over.mk (𝟙 Z)))) := by
  classical
  haveI := H.epi
  let Ω : Over Z := Over.mk (Over.homMk (U := Over.mk (W.hom ≫ Z.hom)) (V := Z) W.hom (by simp))
  obtain ⟨S'', hS'', hS''c⟩ := exists_local_lift H.π (V := Ω) n
  rw [GrothendieckTopology.mem_over_iff] at hS''
  obtain ⟨S, hS, hSS⟩ := exists_sieve_over_of_over Z W _ hS''
  refine ⟨S, hS, fun Y f hf => ?_⟩
  have hf' := hSS f hf
  rw [Sieve.overEquiv_iff] at hf'
  obtain ⟨u, hu⟩ := hS''c _ hf'
  obtain ⟨d, rfl⟩ := MMP.exists_eq_sum_smul_freeSection _ u
  refine ⟨d, hu.symm.trans ((freeHomEquiv_symm_app_sum H.s _ d).trans
    (Finset.sum_congr rfl fun k _ => ?_))⟩
  congr 1
  exact over_section_eq (H.s k) _

section Q3

variable {M : SheafOfModules.{0} A} {V : Opens T} {p : ℕ} (s : Fin p → (M.over V).sections)
  (Z : Over V)

/-- The generators restricted to `Z.left`. -/
noncomputable abbrev resGen (l : Fin p) : (M.over Z.left).sections :=
  overSection M (secAt (s l) (op Z))

/-- The value at `W : Over Z.left` of a restricted generator is the value of the generator at the
composite `W ⟶ Z ⟶ V`. -/
lemma secAt_resGen (W : Over Z.left) (l : Fin p) :
    secAt (resGen s Z l) (op W) = secAt (s l) (op (Over.mk (W.hom ≫ Z.hom))) := by
  change M.val.map W.hom.op (secAt (s l) (op Z)) = _
  rw [over_section_eq (s l) Z, over_section_eq (s l) (Over.mk (W.hom ≫ Z.hom))]
  exact mres_mres (M := M) _ _ _

/-- The morphism from the free module given by the restricted generators, on a linear
combination over `W : Over Z.left`, agrees with the one given by `s` over `W ⟶ Z ⟶ V`. -/
lemma resGen_app_sum (W : Over Z.left) (c : Fin p → A.obj.obj (op W.left)) :
    ((M.over Z.left).freeHomEquiv.symm (resGen s Z)).val.app (op W)
        (∑ l, toOver W (c l) • freeElt (R := A.over Z.left) l (op W)) =
      ((M.over V).freeHomEquiv.symm s).val.app (op (Over.mk (W.hom ≫ Z.hom)))
        (∑ l, toOver (Over.mk (W.hom ≫ Z.hom)) (c l) • freeElt (R := A.over V) l _) := by
  rw [freeHomEquiv_symm_app_sum, freeHomEquiv_symm_app_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [secAt_resGen]
  rfl

/-- The restricted generators still generate. -/
lemma epi_resGen [Epi ((M.over V).freeHomEquiv.symm s)] :
    Epi ((M.over Z.left).freeHomEquiv.symm (resGen s Z)) := by
  classical
  refine epi_of_locally_surjective _ fun W q => ?_
  obtain ⟨S', hS', hS'c⟩ := exists_local_lift ((M.over V).freeHomEquiv.symm s)
    (V := Over.mk (W.hom ≫ Z.hom)) q
  obtain ⟨S, hS, hSS'⟩ := exists_sieve_over_of_over Z W S' hS'
  refine ⟨S, hS, fun Y f hf => ?_⟩
  obtain ⟨u, hu⟩ := hS'c _ (hSS' f hf)
  obtain ⟨c, rfl⟩ := MMP.exists_eq_sum_smul_freeSection _ u
  exact ⟨∑ l, toOver Y (c l) • freeElt l (op Y), (resGen_app_sum s Z Y c).trans hu⟩

variable [Epi ((M.over V).freeHomEquiv.symm s)]
  (H : ((kernel ((M.over V).freeHomEquiv.symm s)).over Z).GeneratingSections) [Fintype H.I]

/-- The relations of `H` as vectors over `Z`. -/
noncomputable abbrev relVec (k : H.I) :
    (SheafOfModules.free (R := A.over V) (Fin p)).val.obj (op Z) :=
  (kernel.ι ((M.over V).freeHomEquiv.symm s)).val.app (op Z)
    (secAt (H.s k) (op (Over.mk (𝟙 Z))))

/-- The coordinates of the relations of `H`. -/
noncomputable abbrev relCoef (k : H.I) (l : Fin p) : A.obj.obj (op Z.left) :=
  (show (A.over V).obj.obj (op Z) from
    (MMP.freeProj l).val.app (op Z) (relVec s Z H k))

/-- A relation of `H` is the combination of tautological sections with its coordinates. -/
lemma relVec_eq (k : H.I) :
    relVec s Z H k = ∑ l, toOver Z (relCoef s Z H k l) • freeElt (R := A.over V) l (op Z) :=
  eq_sum_freeProj_smul _

/-- The relations of `H` give relations among the restricted generators. -/
lemma exists_kernel_resGen (k : H.I) :
    ∃ κ : (kernel ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).val.obj
        (op (Over.mk (𝟙 Z.left))),
      (kernel.ι ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).val.app _ κ =
        ∑ l, toOver (Over.mk (𝟙 Z.left)) (relCoef s Z H k l) •
          freeElt (R := A.over Z.left) l (op (Over.mk (𝟙 Z.left))) := by
  refine exists_kernel_ι_app_eq _ _ _ ?_
  refine (resGen_app_sum s Z (Over.mk (𝟙 Z.left)) (relCoef s Z H k)).trans ?_
  have h0 := kernel_condition_app ((M.over V).freeHomEquiv.symm s) (op Z)
    (secAt (H.s k) (op (Over.mk (𝟙 Z))))
  change ((M.over V).freeHomEquiv.symm s).val.app (op Z) (relVec s Z H k) = 0 at h0
  rw [relVec_eq] at h0
  exact h0

omit [Epi ((M.over V).freeHomEquiv.symm s)] in
/-- Restricting a kernel element with known coordinates. -/
lemma kernel_ι_map_of_eq_sum {W' : Over V} {U : Opens T} (e : U ⟶ V) (h : U ⟶ W'.left)
    (he : h ≫ W'.hom = e) (x : (kernel ((M.over V).freeHomEquiv.symm s)).val.obj (op W'))
    (c : Fin p → A.obj.obj (op W'.left))
    (hx : (kernel.ι ((M.over V).freeHomEquiv.symm s)).val.app (op W') x =
      ∑ l, toOver W' (c l) • freeElt (R := A.over V) l _) :
    (kernel.ι ((M.over V).freeHomEquiv.symm s)).val.app (op (Over.mk e))
        ((kernel ((M.over V).freeHomEquiv.symm s)).val.map
          (Over.homMk (U := Over.mk e) (V := W') h he).op x) =
      ∑ l, toOver (Over.mk e) (res h.le (c l)) • freeElt (R := A.over V) l _ := by
  rw [PresheafOfModules.naturality_apply]
  exact (congrArg ((SheafOfModules.free (R := A.over V) (Fin p)).val.map
    (Over.homMk (U := Over.mk e) (V := W') h he).op) hx).trans (free_map_sum_smul _ _)

/-- Restricting a relation of `H` to `Y ≤ Z.left` and reading it in `𝒪_V^p`. -/
lemma kernel_ι_map_relVec (k : H.I) {U : Opens T} (e : U ⟶ V) (h : U ⟶ Z.left)
    (he : h ≫ Z.hom = e) :
    (kernel.ι ((M.over V).freeHomEquiv.symm s)).val.app (op (Over.mk e))
        ((kernel ((M.over V).freeHomEquiv.symm s)).val.map
          (Over.homMk (U := Over.mk e) (V := Z) h he).op (secAt (H.s k) (op (Over.mk (𝟙 Z))))) =
      ∑ l, toOver (Over.mk e) (res h.le (relCoef s Z H k l)) • freeElt (R := A.over V) l _ :=
  kernel_ι_map_of_eq_sum s e h he (secAt (H.s k) (op (Over.mk (𝟙 Z))))
    (relCoef s Z H k) (relVec_eq s Z H k)

/-- A combination of restricted relations of `H`, read in `𝒪_V^p`. -/
lemma kernel_ι_sum_map_relVec {U : Opens T} (e : U ⟶ V) (h : U ⟶ Z.left)
    (he : h ≫ Z.hom = e) (d : H.I → A.obj.obj (op U)) :
    (kernel.ι ((M.over V).freeHomEquiv.symm s)).val.app (op (Over.mk e))
        (∑ k, toOver (Over.mk e) (d k) •
          (kernel ((M.over V).freeHomEquiv.symm s)).val.map
            (Over.homMk (U := Over.mk e) (V := Z) h he).op (secAt (H.s k) (op (Over.mk (𝟙 Z))))) =
      ∑ k, toOver (Over.mk e) (d k) •
        ∑ l, toOver (Over.mk e) (res h.le (relCoef s Z H k l)) • freeElt (R := A.over V) l _ := by
  refine (map_sum ((kernel.ι ((M.over V).freeHomEquiv.symm s)).val.app
    (op (Over.mk e))).hom _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  refine (map_smul ((kernel.ι ((M.over V).freeHomEquiv.symm s)).val.app
    (op (Over.mk e))).hom _ _).trans ?_
  exact congrArg (toOver (Over.mk e) (d k) • ·) (kernel_ι_map_relVec s Z H k e h he)

/-- The relations `κ` of the restricted generators, combined with coefficients `d`. -/
lemma kernel_ι_resGen_freeHomEquiv_symm_app (κ : H.I →
      (kernel ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).val.obj (op (Over.mk (𝟙 Z.left))))
    (hκ : ∀ k, (kernel.ι ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).val.app _ (κ k) =
        ∑ l, toOver (Over.mk (𝟙 Z.left)) (relCoef s Z H k l) •
          freeElt (R := A.over Z.left) l (op (Over.mk (𝟙 Z.left))))
    (Y : Over Z.left) (d : H.I → A.obj.obj (op Y.left)) :
    (kernel.ι ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).val.app (op Y)
        (((kernel ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).freeHomEquiv.symm
          fun k => topSection _ (κ k)).val.app (op Y)
          (∑ k, toOver Y (d k) • freeElt (R := A.over Z.left) k (op Y))) =
      ∑ l, (∑ k, toOver Y (d k) * toOver Y (res Y.hom.le (relCoef s Z H k l))) •
        freeElt (R := A.over Z.left) l (op Y) := by
  rw [freeHomEquiv_symm_app_sum, map_sum, ← sum_smul_sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, topSection_apply]
  refine congrArg (toOver Y (d k) • ·) ?_
  rw [PresheafOfModules.naturality_apply]
  refine (congrArg ((SheafOfModules.free (R := A.over Z.left) (Fin p)).val.map
    (Over.homMk (U := Y) (V := Over.mk (𝟙 Z.left)) Y.hom (by simp)).op) (hκ k)).trans ?_
  exact free_map_sum_smul _ _

/-- If a kernel section restricts along `f : Y ⟶ W` to a combination of the relations `H.s k`,
then its restricted coordinates are the corresponding combinations of the `relCoef k`. -/
lemma relCoef_combination_eq {W Y : Over Z.left} (f : Y ⟶ W) (c : Fin p → A.obj.obj (op W.left))
    (k'' : (kernel ((M.over V).freeHomEquiv.symm s)).val.obj (op (Over.mk (W.hom ≫ Z.hom))))
    (hk'' : (kernel.ι ((M.over V).freeHomEquiv.symm s)).val.app _ k'' =
      ∑ l, toOver (Over.mk (W.hom ≫ Z.hom)) (c l) • freeElt (R := A.over V) l _)
    (d : H.I → A.obj.obj (op Y.left))
    (hd : (kernel ((M.over V).freeHomEquiv.symm s)).val.map
        (Over.homMk (U := Over.mk (f.left ≫ W.hom ≫ Z.hom))
          (V := Over.mk (W.hom ≫ Z.hom)) f.left (by simp)).op k'' =
        ∑ k, toOver (Over.mk (f.left ≫ W.hom ≫ Z.hom)) (d k) •
          (kernel ((M.over V).freeHomEquiv.symm s)).val.map
            (Over.homMk (U := Over.mk (f.left ≫ W.hom ≫ Z.hom)) (V := Z)
            (f.left ≫ W.hom) (by simp)).op (secAt (H.s k) (op (Over.mk (𝟙 Z))))) (l : Fin p) :
    res f.left.le (c l) = ∑ k, d k * res Y.hom.le (relCoef s Z H k l) := by
  classical
  have hL := kernel_ι_map_of_eq_sum s (W' := Over.mk (W.hom ≫ Z.hom))
    (f.left ≫ W.hom ≫ Z.hom) f.left (by simp) k'' c hk''
  have hR := kernel_ι_sum_map_relVec s Z H (f.left ≫ W.hom ≫ Z.hom) (f.left ≫ W.hom)
    (Category.assoc _ _ _) d
  have hcoef := (hL.symm.trans ((congrArg _ hd).trans hR)).trans (sum_smul_sum_smul _ _ _)
  exact coeff_eq_of_sum_smul_eq hcoef l

omit [Epi ((M.over V).freeHomEquiv.symm s)] in
/-- A local section of the kernel of the restricted presentation, with its coordinates, lifts to
the kernel of `𝒪_V^p → M|_V`. -/
lemma exists_coords_kernel_lift (W : Over Z.left)
    (q : (kernel ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).val.obj (op W)) :
    ∃ (c : Fin p → A.obj.obj (op W.left))
      (k'' : (kernel ((M.over V).freeHomEquiv.symm s)).val.obj (op (Over.mk (W.hom ≫ Z.hom)))),
      (kernel.ι ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).val.app (op W) q =
        ∑ l, toOver W (c l) • freeElt (R := A.over Z.left) l (op W) ∧
      (kernel.ι ((M.over V).freeHomEquiv.symm s)).val.app _ k'' =
        ∑ l, toOver (Over.mk (W.hom ≫ Z.hom)) (c l) • freeElt (R := A.over V) l _ := by
  obtain ⟨c, hc⟩ : ∃ c : Fin p → A.obj.obj (op W.left),
      (kernel.ι ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).val.app (op W) q =
        ∑ l, toOver W (c l) • freeElt (R := A.over Z.left) l (op W) :=
    ⟨_, eq_sum_freeProj_smul _⟩
  have h0 : ((M.over V).freeHomEquiv.symm s).val.app (op (Over.mk (W.hom ≫ Z.hom)))
      (∑ l, toOver (Over.mk (W.hom ≫ Z.hom)) (c l) • freeElt (R := A.over V) l _) = 0 :=
    (resGen_app_sum s Z W c).symm.trans (hc ▸ kernel_condition_app _ (op W) q)
  obtain ⟨k'', hk''⟩ := exists_kernel_ι_app_eq ((M.over V).freeHomEquiv.symm s)
    (op (Over.mk (W.hom ≫ Z.hom))) _ h0
  exact ⟨c, k'', hc, hk''⟩

/-- The relations `κ` of the restricted generators generate all relations. -/
lemma epi_kernel_resGen_freeHomEquiv_symm (κ : H.I →
      (kernel ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).val.obj (op (Over.mk (𝟙 Z.left))))
    (hκ : ∀ k, (kernel.ι ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).val.app _ (κ k) =
        ∑ l, toOver (Over.mk (𝟙 Z.left)) (relCoef s Z H k l) •
          freeElt (R := A.over Z.left) l (op (Over.mk (𝟙 Z.left)))) :
    Epi ((kernel ((M.over Z.left).freeHomEquiv.symm (resGen s Z))).freeHomEquiv.symm
      fun k => topSection _ (κ k)) := by
  classical
  refine epi_of_locally_surjective _ fun W q => ?_
  refine Exists.elim (exists_coords_kernel_lift s Z W q) fun c hck => ?_
  refine Exists.elim hck fun k'' hck => ?_
  refine Exists.elim (exists_local_combination_over Z H W k'') fun S hS => ?_
  refine ⟨S, hS.1, fun Y f hf => ?_⟩
  refine Exists.elim (hS.2 f hf) fun d hd => ?_
  have hc := hck.1
  have hk'' := hck.2
  refine ⟨∑ k, toOver Y (d k) • freeElt (R := A.over Z.left) k (op Y), ?_⟩
  apply kernel_ι_app_injective _ (op Y)
  refine (kernel_ι_resGen_freeHomEquiv_symm_app s Z H κ hκ Y d).trans ?_
  have hT2 := kernel_ι_map_of_eq_sum (resGen s Z) (W' := W) Y.hom f.left (Over.w f) q c hc
  refine Eq.trans ?_ hT2.symm
  refine Finset.sum_congr rfl fun l _ => ?_
  exact congrArg (· • _) (relCoef_combination_eq s Z H f c k'' hk'' d hd l).symm

include s H in
/-- **A presentation on a smaller open.** Finitely many generators `s` of `M|_V`, and finitely many
generators `H` of the kernel of `𝒪_V^p → M|_V` over `Z`, give a finite presentation of
`M|_{Z.left}`. -/
theorem exists_presentation_restrict :
    ∃ P : (M.over Z.left).Presentation, Finite P.generators.I ∧ Finite P.relations.I := by
  classical
  haveI := epi_resGen s Z
  choose κ hκ using exists_kernel_resGen s Z H
  exact ⟨⟨⟨Fin p, resGen s Z, inferInstance⟩,
    ⟨H.I, fun k => topSection _ (κ k), epi_kernel_resGen_freeHomEquiv_symm s Z H κ hκ⟩⟩,
    inferInstanceAs (Finite (Fin p)), inferInstanceAs (Finite H.I)⟩

end Q3

/-- **Coherent modules have local finite presentations.** -/
theorem exists_presentation_of_isCoherentModule {M : SheafOfModules.{0} A}
    (hM : IsCoherentModule M) (x : T) :
    ∃ X0 : Opens T, x ∈ X0 ∧ ∃ P : (M.over X0).Presentation,
      Finite P.generators.I ∧ Finite P.relations.I := by
  obtain ⟨V, hxV, p, s, hepi⟩ := exists_fin_generators hM.1 x
  obtain ⟨τ, hτ⟩ := (hM.2 V p s).exists_localGeneratorsData
  obtain ⟨j, hj⟩ := exists_mem_of_coversTop_over τ.coversTop x hxV
  have := hτ.isFiniteType j
  haveI := Fintype.ofFinite (τ.generators j).I
  exact ⟨(τ.X j).left, hj, exists_presentation_restrict s (τ.X j) (τ.generators j)⟩

/-- A sheaf of modules with local finite presentations is of finite type. -/
theorem isFiniteType_of_presentations {M : SheafOfModules.{0} A}
    (hP : ∀ x : T, ∃ X0 : Opens T, x ∈ X0 ∧ ∃ P : (M.over X0).Presentation,
      Finite P.generators.I ∧ Finite P.relations.I) :
    SheafOfModules.IsFiniteType.{0} M := by
  choose X0 hX0 P hPg _ using hP
  refine MMP.isFiniteType_of_coversTop M (Y := X0) (fun U y hy => ?_) fun x => ?_
  · exact ⟨U ⊓ X0 y, homOfLE inf_le_left, ⟨y, ⟨homOfLE inf_le_right⟩⟩, ⟨hy, hX0 y⟩⟩
  · haveI : HasBinaryProducts (Over (X0 x)) := Over.ConstructProducts.over_binaryProduct_of_pullback
    haveI := hPg x
    haveI : (P x).generators.IsFiniteType := ⟨inferInstance⟩
    exact ⟨⟨(P x).generators.localGeneratorsData,
      ⟨fun _ => ⟨inferInstanceAs (Finite (P x).generators.I)⟩⟩⟩⟩

/-- **Finitely presented modules over a coherent sheaf of rings are coherent.** -/
theorem isCoherentModule_of_presentations {M : SheafOfModules.{0} A}
    (hA : RelationsLocallyFinite A 1)
    (hP : ∀ x : T, ∃ X0 : Opens T, x ∈ X0 ∧ ∃ P : (M.over X0).Presentation,
      Finite P.generators.I ∧ Finite P.relations.I) :
    IsCoherentModule M :=
  isCoherentModule_of_relations (isFiniteType_of_presentations hP)
    (moduleRelationsLocallyFinite_of_presentation (relationsLocallyFinite_of_one hA) hP)

end CoherentPresentation

/-! ### Pullback of sheaves of modules commutes with restriction to opens -/

section PullbackRestriction

open TopologicalSpace

variable {T T' : TopCat.{0}} (f : T ⟶ T')

/-- The functor `Over U ⥤ Over (f⁻¹ U)` induced by preimage under `f` is representably flat. -/
theorem representablyFlat_overPost (U : Opens T') :
    RepresentablyFlat (Over.post (X := U) (Opens.map f)) := by
  constructor
  intro Z
  refine @IsCofiltered.mk _ _ ?_ ?_
  · constructor
    · intro V V'
      refine ⟨StructuredArrow.mk (Y := Over.mk (homOfLE (inf_le_left.trans V.right.hom.le) :
          V.right.left ⊓ V'.right.left ⟶ U)) (Over.homMk (homOfLE (le_inf V.hom.left.le
            V'.hom.left.le)) (Subsingleton.elim _ _)),
        StructuredArrow.homMk (Over.homMk (homOfLE inf_le_left) (Subsingleton.elim _ _))
          (Subsingleton.elim _ _),
        StructuredArrow.homMk (Over.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _))
          (Subsingleton.elim _ _), trivial⟩
    · intro V V' g g'
      refine ⟨V, 𝟙 _, ?_⟩
      ext
      exact Subsingleton.elim _ _
  · exact ⟨StructuredArrow.mk (Y := Over.mk (𝟙 U))
      (Over.homMk (homOfLE Z.hom.le) (Subsingleton.elim _ _))⟩

attribute [local instance] representablyFlat_overPost

/-- The functor `Over U ⥤ Over (f⁻¹ U)` induced by preimage under `f` is continuous for the
induced Grothendieck topologies. -/
theorem isContinuous_overPost (U : Opens T') :
    (Over.post (X := U) (Opens.map f)).IsContinuous ((Opens.grothendieckTopology T').over U)
      ((Opens.grothendieckTopology T).over ((Opens.map f).obj U)) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (CoverPreserving.overPost U (coverPreserving_opens_map f))

attribute [local instance] isContinuous_overPost

/-- The functor `Over U ⥤ Over (f⁻¹ U)` induced by preimage under `f` is final. -/
theorem final_overPost (U : Opens T') : (Over.post (X := U) (Opens.map f)).Final := by
  constructor
  intro Z
  haveI := RepresentablyFlat.cofiltered (F := Over.post (X := U) (Opens.map f)) Z
  exact IsCofiltered.isConnected _

attribute [local instance] final_overPost

section Restriction

variable {A : Sheaf (Opens.grothendieckTopology T') RingCat.{0}}
  {A' : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
  (φ : A ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{0} (Opens.grothendieckTopology T')
    (Opens.grothendieckTopology T)).obj A') (U : Opens T')

/-- The restriction of `φ` over an open `U`. -/
noncomputable abbrev overRingHom : A.over U ⟶
    ((Over.post (X := U) (Opens.map f)).sheafPushforwardContinuous RingCat.{0}
      ((Opens.grothendieckTopology T').over U)
      ((Opens.grothendieckTopology T).over ((Opens.map f).obj U))).obj
      (A'.over ((Opens.map f).obj U)) :=
  ((Over.forget U).sheafPushforwardContinuous RingCat.{0} ((Opens.grothendieckTopology T').over U)
    (Opens.grothendieckTopology T')).map φ

/-- Pushforward of presheaves of modules along `overRingHom f φ U` is a right adjoint. -/
theorem isRightAdjoint_presheafPushforward_overRingHom :
    (PresheafOfModules.pushforward.{0} (overRingHom f φ U).hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

attribute [local instance] isRightAdjoint_presheafPushforward_overRingHom

/-- The two composites `Opens T' ⥤ Over (f⁻¹ U)`, `V ↦ f⁻¹ U ⊓ f⁻¹ V` and `V ↦ f⁻¹ (U ⊓ V)`. -/
noncomputable def starPostIso :
    Opens.map f ⋙ Over.star ((Opens.map f).obj U) ≅ Over.star U ⋙ Over.post (Opens.map f) :=
  NatIso.ofComponents (fun V => Over.isoMk
    { hom := homOfLE fun x hx => (prod.lift (homOfLE inf_le_left) (homOfLE inf_le_right) :
          U ⊓ V ⟶ U ⨯ V).le ⟨(prod.fst : _ ⟶ (Opens.map f).obj U).le hx,
            (prod.snd : _ ⟶ (Opens.map f).obj V).le hx⟩
      inv := homOfLE fun x hx => (prod.lift (homOfLE inf_le_left) (homOfLE inf_le_right) :
          (Opens.map f).obj U ⊓ (Opens.map f).obj V ⟶ (Opens.map f).obj U ⨯ (Opens.map f).obj V).le
            ⟨(prod.fst : U ⨯ V ⟶ U).le hx, (prod.snd : U ⨯ V ⟶ V).le hx⟩
      hom_inv_id := Subsingleton.elim _ _
      inv_hom_id := Subsingleton.elim _ _ } (Subsingleton.elim _ _))
    (fun _ => by ext; exact Subsingleton.elim _ _)

/-- The functor `V ↦ f⁻¹ U ⊓ f⁻¹ V` is continuous. -/
theorem isContinuous_map_comp_star : (Opens.map f ⋙ Over.star ((Opens.map f).obj U)).IsContinuous
    (Opens.grothendieckTopology T') ((Opens.grothendieckTopology T).over ((Opens.map f).obj U)) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology T) _

/-- The functor `V ↦ f⁻¹ (U ⊓ V)` is continuous. -/
theorem isContinuous_star_comp_post : (Over.star U ⋙ Over.post (Opens.map f)).IsContinuous
    (Opens.grothendieckTopology T') ((Opens.grothendieckTopology T).over ((Opens.map f).obj U)) :=
  Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology T').over U) _

attribute [local instance] isContinuous_map_comp_star isContinuous_star_comp_post

/-- Two successive restriction maps of a presheaf on opens compose to the direct one. -/
lemma map_map_eq {X : TopCat.{0}} (P : (Opens X)ᵒᵖ ⥤ RingCat.{0}) {a b c : (Opens X)ᵒᵖ}
    (g1 : a ⟶ b) (g2 : b ⟶ c) (g3 : a ⟶ c) (y : P.obj a) :
    P.map g2 (P.map g1 y) = P.map g3 y := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, Subsingleton.elim (g1 ≫ g2) g3]

/-- The morphisms of sheaves of rings obtained by restricting `φ` over `U` and then
pushing forward, and by pushing forward and then restricting over `f⁻¹ U`, agree along
`starPostIso f U`. -/
lemma starPost_ringHom_eq :
    (SheafOfModules.pushforwardOver U ≫ ((Over.star U).sheafPushforwardContinuous RingCat.{0}
        (Opens.grothendieckTopology T') ((Opens.grothendieckTopology T').over U)).map
          (overRingHom f φ U)) ≫
      (Functor.sheafPushforwardContinuousNatTrans (starPostIso f U).hom RingCat.{0}
        (Opens.grothendieckTopology T') ((Opens.grothendieckTopology T).over
          ((Opens.map f).obj U))).app (A'.over ((Opens.map f).obj U)) =
    φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{0} (Opens.grothendieckTopology T')
        (Opens.grothendieckTopology T)).map
          (SheafOfModules.pushforwardOver ((Opens.map f).obj U)) := by
  ext V x
  change A'.obj.map ((starPostIso f U).hom.app V.unop).left.op
      (φ.hom.app (op (U ⨯ V.unop)) (A.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op x)) =
    A'.obj.map (prod.snd : (Opens.map f).obj U ⨯ (Opens.map f).obj V.unop ⟶ _).op
      (φ.hom.app V x)
  have hn : φ.hom.app (op (U ⨯ V.unop)) (A.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op x) =
      A'.obj.map ((Opens.map f).map (prod.snd : U ⨯ V.unop ⟶ V.unop)).op (φ.hom.app V x) :=
    NatTrans.naturality_apply φ.hom (prod.snd : U ⨯ V.unop ⟶ V.unop).op x
  rw [hn]
  exact map_map_eq (A'.obj) _ _ _ _

/-- Pushforward of presheaves of modules along `φ` is a right adjoint. -/
theorem isRightAdjoint_presheafPushforward :
    (PresheafOfModules.pushforward.{0} φ.hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

attribute [local instance] isRightAdjoint_presheafPushforward

/-- The two right adjoints `Mod(𝒪'|_{f⁻¹ U}) ⥤ Mod(𝒪)` agree. -/
noncomputable def rightAdjointIso :
    SheafOfModules.pushforward.{0} (overRingHom f φ U) ⋙
        SheafOfModules.pushforward.{0} (SheafOfModules.pushforwardOver U) ≅
      SheafOfModules.pushforward.{0} (SheafOfModules.pushforwardOver ((Opens.map f).obj U)) ⋙
        SheafOfModules.pushforward.{0} φ :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (starPostIso f U) (starPost_ringHom_eq f φ U) ≪≫
      (SheafOfModules.pushforwardComp _ _).symm

/-- **Pullback commutes with restriction to opens.** -/
noncomputable def overPullbackIso :
    SheafOfModules.pullback.{0} φ ⋙ SheafOfModules.overFunctor A' ((Opens.map f).obj U) ≅
      SheafOfModules.overFunctor A U ⋙ SheafOfModules.pullback.{0} (overRingHom f φ U) :=
  Adjunction.leftAdjointUniq
    ((SheafOfModules.pullbackPushforwardAdjunction φ).comp
      (SheafOfModules.overPushforwardOverAdj _))
    (((SheafOfModules.overPushforwardOverAdj U).comp
      (SheafOfModules.pullbackPushforwardAdjunction (overRingHom f φ U))).ofNatIsoRight
        (rightAdjointIso f φ U))

/-- **Pullbacks of local finite presentations.** -/
theorem exists_presentation_pullback (M : SheafOfModules.{0} A) (P : (M.over U).Presentation)
    [Finite P.generators.I] [Finite P.relations.I] :
    ∃ P' : (((SheafOfModules.pullback.{0} φ).obj M).over ((Opens.map f).obj U)).Presentation,
      Finite P'.generators.I ∧ Finite P'.relations.I := by
  let F := SheafOfModules.pullback.{0} (overRingHom f φ U)
  let η : SheafOfModules.unit (A'.over ((Opens.map f).obj U)) ≅
      F.obj (SheafOfModules.unit (A.over U)) :=
    (asIso (SheafOfModules.pullbackObjUnitToUnit (overRingHom f φ U))).symm
  let P' := P.map F η
  let e := (overPullbackIso f φ U).app M
  exact ⟨P'.ofIsIso e.inv, inferInstanceAs (Finite P.generators.I),
    inferInstanceAs (Finite P.relations.I)⟩

end Restriction

end PullbackRestriction

/-! ### Holomorphic functions in charts -/

section Charts

open Set TopologicalSpace

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M]

/-- A holomorphic function on an open set `U ⊆ M`, read in the chart at `x`, is complex
differentiable on the image of `U ∩` the chart source. -/
theorem differentiableOn_chart_symm (x : M) (U : Opens M) (g : U → ℂ)
    (hg : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ g) :
    DifferentiableOn ℂ (fun z => Function.extend (Subtype.val : U → M) g 0
      ((chartAt (EuclideanSpace ℂ (Fin n)) x).symm z))
      ((chartAt (EuclideanSpace ℂ (Fin n)) x).target ∩
        (chartAt (EuclideanSpace ℂ (Fin n)) x).symm ⁻¹' U) := by
  set e := chartAt (EuclideanSpace ℂ (Fin n)) x
  set g' : M → ℂ := Function.extend (Subtype.val : U → M) g 0
  have hg' : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ g' U := by
    intro m hm
    have : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (fun w : U => g' w) ⟨m, hm⟩ := by
      have h1 : (fun w : U => g' w) = g := funext fun w => Subtype.val_injective.extend_apply g 0 w
      rw [h1]; exact hg _
    exact (contMDiffAt_subtype_iff.1 this).contMDiffWithinAt
  have h2 : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (g' ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' U) :=
    hg'.comp ((contMDiffOn_chart_symm (x := x)).mono inter_subset_left) (fun z hz => hz.2)
  exact (contMDiffOn_iff_contDiffOn.1 h2).differentiableOn (by simp)

/-- A complex differentiable function on the image in the chart at `x` of an open set
`U ⊆` the chart source, composed with the chart, is holomorphic on `U`. -/
theorem contMDiff_comp_chart (x : M) (U : Opens M)
    (hU : (U : Set M) ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x).source)
    (G : EuclideanSpace ℂ (Fin n) → ℂ)
    (hG : DifferentiableOn ℂ G ((chartAt (EuclideanSpace ℂ (Fin n)) x).target ∩
        (chartAt (EuclideanSpace ℂ (Fin n)) x).symm ⁻¹' U)) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞
      (fun w : U => G (chartAt (EuclideanSpace ℂ (Fin n)) x w)) := by
  set e := chartAt (EuclideanSpace ℂ (Fin n)) x
  have hS : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm U.isOpen
  have hGa := analyticOnNhd_of_differentiableOn hS hG
  have hG' : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ G (e.target ∩ e.symm ⁻¹' U) :=
    contMDiffOn_iff_contDiffOn.2 (hGa.contDiffOn hS.uniqueDiffOn)
  have h2 : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (G ∘ e) U :=
    hG'.comp ((contMDiffOn_chart (x := x)).mono hU) (fun m hm =>
      ⟨e.map_source (hU hm), by simpa [e.left_inv (hU hm)] using hm⟩)
  intro w
  exact contMDiffAt_subtype_iff.2 (h2.contMDiffAt (U.isOpen.mem_nhds w.2))

variable (n) in
/-- Evaluation at a point of a holomorphic function on an open set of `M`. -/
noncomputable def holEval (U : Opens (TopCat.of M)) (w : U) :
    (holomorphicRingCatSheaf n M).obj.obj (op U) →+* ℂ where
  toFun a := (show C^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin n)), U; 𝓘(ℂ), ℂ⟯ from a) w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The function `w ↦ holEval n U w a` underlying a section `a` is holomorphic. -/
lemma contMDiff_holEval (U : Opens (TopCat.of M))
    (a : (holomorphicRingCatSheaf n M).obj.obj (op U)) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (fun w => holEval n U w a) :=
  (show C^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin n)), U; 𝓘(ℂ), ℂ⟯ from a).contMDiff

/-- Holomorphic functions with the same values are equal. -/
lemma holEval_ext {U : Opens (TopCat.of M)}
    {a b : (holomorphicRingCatSheaf n M).obj.obj (op U)}
    (h : ∀ w, holEval n U w a = holEval n U w b) :
    a = b :=
  ContMDiffMap.ext h

/-- Evaluation of a restriction. -/
lemma holEval_res {U U' : Opens (TopCat.of M)} (h : U' ≤ U) (w : U')
    (a : (holomorphicRingCatSheaf n M).obj.obj (op U)) :
    holEval n U' w (res h a) = holEval n U ⟨w.1, h w.2⟩ a := rfl

variable (n) in
/-- The holomorphic function on an open set `U` given by a holomorphic function on `M`. -/
noncomputable def holMk (U : Opens (TopCat.of M)) (g : U → ℂ)
    (hg : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ g) :
    (holomorphicRingCatSheaf n M).obj.obj (op U) :=
  (⟨g, hg⟩ : C^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin n)), U; 𝓘(ℂ), ℂ⟯)

/-- Evaluation of `holMk n U g hg` at `w` is `g w`. -/
lemma holEval_holMk (U : Opens (TopCat.of M)) (g : U → ℂ)
    (hg : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ g) (w : U) :
    holEval n U w (holMk n U g hg) = g w := rfl

end Charts

/-- The relations among the `p` vectors `Fᵢ` of length `q` of functions on `V ⊆ E` are finitely
generated near `x`: there are a neighbourhood `W` of `x` and finitely many relations over `W`
which locally generate all complex differentiable relations over every open `U ⊆ W`. -/
def HolomorphicRelationsGeneratedNear {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : Set E) {p q : ℕ} (F : Fin p → Fin q → E → ℂ) (x : E) : Prop :=
  ∃ W : Set E, IsOpen W ∧ W ⊆ V ∧ x ∈ W ∧ ∃ (s : ℕ) (r : Fin s → Fin p → E → ℂ),
    (∀ k i, DifferentiableOn ℂ (r k i) W) ∧ (∀ k j, ∀ z ∈ W, ∑ i, r k i z * F i j z = 0) ∧
    ∀ U : Set E, IsOpen U → U ⊆ W → ∀ a : Fin p → E → ℂ, (∀ i, DifferentiableOn ℂ (a i) U) →
      (∀ j, ∀ z ∈ U, ∑ i, a i z * F i j z = 0) →
      ∀ y ∈ U, ∃ U' : Set E, IsOpen U' ∧ U' ⊆ U ∧ y ∈ U' ∧ ∃ c : Fin s → E → ℂ,
        (∀ k, DifferentiableOn ℂ (c k) U') ∧ ∀ i, ∀ z ∈ U', a i z = ∑ k, c k z * r k i z

/-- The relations among `p` vectors of length `q` of complex differentiable functions on an open
subset of `E` are locally finitely generated: near every point there are finitely many
relations which locally generate all relations over smaller open sets. -/
def HolomorphicRelationsLocallyFinite (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (q : ℕ) : Prop :=
  ∀ (V : Set E), IsOpen V → ∀ (p : ℕ) (F : Fin p → Fin q → E → ℂ),
    (∀ i j, DifferentiableOn ℂ (F i j) V) → ∀ x ∈ V, HolomorphicRelationsGeneratedNear V F x

section Rows

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- There is nothing to check for holomorphic relations among vectors of length `0`. -/
theorem holomorphicRelationsLocallyFinite_zero : HolomorphicRelationsLocallyFinite E 0 := by
  intro V hV p F _ x hx
  refine ⟨V, hV, subset_rfl, hx, p, fun k i _ => if k = i then 1 else 0,
    fun k i => differentiableOn_const _, fun k j => j.elim0,
    fun U hU _ a ha _ y hy => ⟨U, hU, subset_rfl, hy, a, ha, fun i z _ => ?_⟩⟩
  simp

/-- **Reduction to one row** for holomorphic relations. -/
theorem holomorphicRelationsLocallyFinite_succ {q : ℕ}
    (h1 : HolomorphicRelationsLocallyFinite E 1) (hq : HolomorphicRelationsLocallyFinite E q) :
    HolomorphicRelationsLocallyFinite E (q + 1) := by
  intro V hV p F hF x hx
  obtain ⟨W₁, hW₁o, hW₁V, hx₁, s₁, r, hrd, hr, hgr⟩ :=
    h1 V hV p (fun i _ => F i (Fin.last q)) (fun i _ => hF i _) x hx
  let G : Fin s₁ → Fin q → E → ℂ := fun k j z => ∑ i, r k i z * F i j.castSucc z
  have hGd : ∀ k j, DifferentiableOn ℂ (G k j) W₁ := fun k j =>
    DifferentiableOn.fun_sum fun i _ => (hrd k i).mul ((hF i _).mono hW₁V)
  obtain ⟨W₂, hW₂o, hW₂W, hx₂, s₂, t, htd, ht, hgt⟩ := hq W₁ hW₁o s₁ G hGd x hx₁
  refine ⟨W₂, hW₂o, hW₂W.trans hW₁V, hx₂, s₂, fun l i z => ∑ k, t l k z * r k i z,
    fun l i => DifferentiableOn.fun_sum fun k _ => (htd l k).mul ((hrd k i).mono hW₂W),
    fun l j z hz => ?_, fun U hU hUW a ha har y hy => ?_⟩
  · have key : ∑ i, (∑ k, t l k z * r k i z) * F i j z =
        ∑ k, t l k z * ∑ i, r k i z * F i j z := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    rw [key]
    induction j using Fin.lastCases with
    | last => simp [hr _ 0 z (hW₂W hz)]
    | cast j => exact ht l j z hz
  · obtain ⟨U₁, hU₁o, hU₁U, hy₁, c, hcd, hc⟩ :=
      hgr U hU (hUW.trans hW₂W) a ha (fun _ => har (Fin.last q)) y hy
    have hcG : ∀ j, ∀ z ∈ U₁, ∑ k, c k z * G k j z = 0 := by
      intro j z hz
      have e : ∑ k, c k z * G k j z = ∑ i, a i z * F i j.castSucc z := by
        simp only [G, hc _ z hz, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      rw [e, har j.castSucc z (hU₁U hz)]
    obtain ⟨U₂, hU₂o, hU₂U, hy₂, d, hdd, hd⟩ :=
      hgt U₁ hU₁o (hU₁U.trans hUW) c hcd hcG y hy₁
    refine ⟨U₂, hU₂o, hU₂U.trans hU₁U, hy₂, d, hdd, fun i z hz => ?_⟩
    rw [hc i z (hU₂U hz)]
    simp only [hd _ z hz, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

/-- **Relations near a point where one function is a unit.** If `f_{i₀}(x) ≠ 0`, the relations
among the `fᵢ` are generated near `x` by the trivial relations `f_{i₀} eⱼ - fⱼ e_{i₀}`: a
relation `a` is `∑ⱼ (aⱼ / f_{i₀}) (f_{i₀} eⱼ - fⱼ e_{i₀})`. -/
theorem holomorphicRelationsGeneratedNear_of_ne_zero {V : Set E} (hV : IsOpen V) {p : ℕ}
    {F : Fin p → Fin 1 → E → ℂ} (hF : ∀ i j, DifferentiableOn ℂ (F i j) V) {x : E} (hx : x ∈ V)
    (i₀ : Fin p) (h0 : F i₀ 0 x ≠ 0) : HolomorphicRelationsGeneratedNear V F x := by
  classical
  set W := V ∩ (fun z => F i₀ 0 z) ⁻¹' {0}ᶜ with hW
  have hWo : IsOpen W := (hF i₀ 0).continuousOn.isOpen_inter_preimage hV isOpen_compl_singleton
  have hne : ∀ z ∈ W, F i₀ 0 z ≠ 0 := fun z hz => hz.2
  refine ⟨W, hWo, Set.inter_subset_left, ⟨hx, h0⟩, p,
    fun j i z => (if i = j then F i₀ 0 z else 0) - (if i = i₀ then F j 0 z else 0),
    fun j i => ?_, fun j l z _ => ?_, fun U hU hUW a ha har y hy => ?_⟩
  · refine DifferentiableOn.sub ?_ ?_
    · split_ifs
      · exact (hF i₀ 0).mono Set.inter_subset_left
      · exact differentiableOn_const _
    · split_ifs
      · exact (hF j 0).mono Set.inter_subset_left
      · exact differentiableOn_const _
  · rw [Subsingleton.elim l 0]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  · refine ⟨U, hU, subset_rfl, hy, fun j z => a j z * (F i₀ 0 z)⁻¹,
      fun j => (ha j).mul (((hF i₀ 0).mono (hUW.trans Set.inter_subset_left)).inv
        fun z hz => hne z (hUW hz)), fun m z hz => ?_⟩
    have hz0 := hne z (hUW hz)
    have hrel : ∑ i, a i z * F i 0 z = 0 := har 0 z hz
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [inv_mul_cancel_right₀ hz0]
    split_ifs with hm
    · have : ∑ j, a j z * (F i₀ 0 z)⁻¹ * F j 0 z = 0 := by
        simp only [mul_right_comm _ (F i₀ 0 z)⁻¹, ← Finset.sum_mul, hrel, zero_mul]
      rw [this, sub_zero]
    · simp

/-- Holomorphic relations among vectors of any length are locally finitely generated once those
among functions are. -/
theorem holomorphicRelationsLocallyFinite_of_one
    (h1 : HolomorphicRelationsLocallyFinite E 1) (q : ℕ) :
    HolomorphicRelationsLocallyFinite E q := by
  induction q with
  | zero => exact holomorphicRelationsLocallyFinite_zero
  | succ q ih => exact holomorphicRelationsLocallyFinite_succ h1 ih

end Rows

/-- Local finite generation of holomorphic relations is invariant under complex linear
isomorphisms. -/
theorem HolomorphicRelationsLocallyFinite.of_continuousLinearEquiv
    {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] {q : ℕ} (h : HolomorphicRelationsLocallyFinite E q) (L : E ≃L[ℂ] E') :
    HolomorphicRelationsLocallyFinite E' q := by
  intro V hV p F hF x hx
  have hL : ∀ (T : Set E') (g : E' → ℂ), DifferentiableOn ℂ g T →
      DifferentiableOn ℂ (fun z => g (L z)) (L ⁻¹' T) := fun T g hg =>
    hg.comp L.differentiableOn (fun _ h => h)
  have hLs : ∀ (T : Set E) (g : E → ℂ), DifferentiableOn ℂ g T →
      DifferentiableOn ℂ (fun z => g (L.symm z)) (L.symm ⁻¹' T) := fun T g hg =>
    hg.comp L.symm.differentiableOn (fun _ h => h)
  obtain ⟨W, hWo, hWV, hxW, s, r, hrd, hr, hgen⟩ := h (L ⁻¹' V) (hV.preimage L.continuous) p
    (fun i j z => F i j (L z)) (fun i j => hL V _ (hF i j)) (L.symm x)
    (by simpa using hx)
  refine ⟨L.symm ⁻¹' W, hWo.preimage L.symm.continuous, fun z hz => by simpa using hWV hz,
    by simpa using hxW, s, fun k i z => r k i (L.symm z), fun k i => hLs W _ (hrd k i),
    fun k j z hz => by simpa using hr k j _ hz, fun U hU hUW a ha har y hy => ?_⟩
  obtain ⟨U', hU'o, hU'U, hyU', c, hcd, hc⟩ := hgen (L ⁻¹' U) (hU.preimage L.continuous)
    (fun z hz => by simpa using hUW hz) (fun i z => a i (L z)) (fun i => hL U _ (ha i))
    (fun j z hz => har j _ hz) (L.symm y) (by simpa using hy)
  refine ⟨L.symm ⁻¹' U', hU'o.preimage L.symm.continuous, fun z hz => by simpa using hU'U hz,
    hyU', fun k z => c k (L.symm z), fun k => hLs U' _ (hcd k), fun i z hz => ?_⟩
  simpa using hc i _ hz

section Charts

open Set TopologicalSpace

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M]

/-- **Oka's theorem is local.** Relations among holomorphic functions on a complex manifold are
locally finitely generated once they are so on `ℂⁿ`: read everything in a chart. -/
theorem relationsLocallyFinite_of_holomorphic {q : ℕ}
    (h : HolomorphicRelationsLocallyFinite (EuclideanSpace ℂ (Fin n)) q) :
    RelationsLocallyFinite (holomorphicRingCatSheaf n M) q := by
  intro V p F x hx
  set e := chartAt (EuclideanSpace ℂ (Fin n)) x
  let S : Opens (TopCat.of M) → Set (EuclideanSpace ℂ (Fin n)) := fun U => e.target ∩ e.symm ⁻¹' U
  have hSo : ∀ U, IsOpen (S U) := fun U => e.isOpen_inter_preimage_symm U.isOpen
  let ext : (U : Opens (TopCat.of M)) → (holomorphicRingCatSheaf n M).obj.obj (op U) →
      EuclideanSpace ℂ (Fin n) → ℂ := fun U b z =>
    Function.extend (Subtype.val : U → M) (fun w => holEval n U w b) 0 (e.symm z)
  have hextd : ∀ U b, DifferentiableOn ℂ (ext U b) (S U) := fun U b =>
    differentiableOn_chart_symm x U _ (contMDiff_holEval U b)
  have hext : ∀ U b z (hz : e.symm z ∈ U), ext U b z = holEval n U ⟨e.symm z, hz⟩ b :=
    fun U b z hz => Subtype.val_injective.extend_apply (fun w => holEval n U w b) 0 ⟨_, hz⟩
  have hext' : ∀ U b (m : M) (hm : m ∈ U), m ∈ e.source → ext U b (e m) = holEval n U ⟨m, hm⟩ b :=
    fun U b m hm hms => by
      change Function.extend (Subtype.val : U → M) (fun w => holEval n U w b) 0 (e.symm (e m)) = _
      rw [e.left_inv hms]
      exact Subtype.val_injective.extend_apply (fun w => holEval n U w b) 0 ⟨m, hm⟩
  have hxe : x ∈ e.source := mem_chart_source _ x
  obtain ⟨W', hW'o, hW'V, hxW', s, ρ, hρd, hρ, hgen⟩ := h (S V) (hSo V) p
    (fun i j => ext V (F i j)) (fun i j => hextd V _) (e x)
    ⟨e.map_source hxe, show e.symm (e x) ∈ V by rw [e.left_inv hxe]; exact hx⟩
  let pull : (T : Set (EuclideanSpace ℂ (Fin n))) → IsOpen T → Opens (TopCat.of M) := fun T hT =>
    ⟨e.source ∩ e ⁻¹' T, e.isOpen_inter_preimage hT⟩
  have hpull_src : ∀ T hT, ((pull T hT : Opens (TopCat.of M)) : Set M) ⊆ e.source :=
    fun T hT m hm => hm.1
  have hS_pull : ∀ T hT, S (pull T hT) ⊆ T := fun T hT z hz => by
    have := hz.2.2
    rwa [Set.mem_preimage, e.right_inv hz.1] at this
  have hpull_le : ∀ (T hT) (U : Opens (TopCat.of M)), T ⊆ S U → pull T hT ≤ U :=
    fun T hT U hTU m hm => by
      have := (hTU hm.2).2
      rwa [Set.mem_preimage, e.left_inv hm.1] at this
  let W := pull W' hW'o
  have hWV : W ≤ V := hpull_le W' hW'o V hW'V
  let r : Fin s → Fin p → (holomorphicRingCatSheaf n M).obj.obj (op W) := fun k i =>
    holMk n W _ (contMDiff_comp_chart x W (hpull_src W' hW'o) (ρ k i)
      ((hρd k i).mono (hS_pull W' hW'o)))
  refine ⟨W, hWV, ⟨hxe, hxW'⟩, s, r, fun k j => ?_, fun U hUW a ha y hy => ?_⟩
  · refine holEval_ext fun w => ?_
    have hw := w.2
    rw [map_sum, map_zero]
    have := hρ k j (e w) hw.2
    beta_reduce at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, holEval_res, holEval_holMk, hext V _ _ (by rw [e.left_inv hw.1]; exact hWV hw)]
    simp only [e.left_inv hw.1]
    rfl
  · let α : Fin p → EuclideanSpace ℂ (Fin n) → ℂ := fun i => ext U (a i)
    have hUW' : S U ⊆ W' := fun z hz => by
      have := (hUW hz.2).2
      rwa [Set.mem_preimage, e.right_inv hz.1] at this
    have hrel : ∀ j, ∀ z ∈ S U, ∑ i, α i z * ext V (F i j) z = 0 := by
      intro j z hz
      have := congrArg (holEval n U ⟨e.symm z, hz.2⟩) (ha j)
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, holEval_res]
      exact congrArg₂ (· * ·) (hext U _ z hz.2) (hext V _ z (hWV (hUW hz.2)))
    have hye : y ∈ e.source := hpull_src W' hW'o (hUW hy)
    obtain ⟨U'E, hU'o, hU'U, hyU', c, hcd, hc⟩ := hgen (S U) (hSo U) hUW' α
      (fun i => hextd U _) hrel (e y)
      ⟨e.map_source hye, show e.symm (e y) ∈ U by rw [e.left_inv hye]; exact hy⟩
    let U' := pull U'E hU'o
    have hU'le : U' ≤ U := hpull_le U'E hU'o U hU'U
    let c' : Fin s → (holomorphicRingCatSheaf n M).obj.obj (op U') := fun k =>
      holMk n U' _ (contMDiff_comp_chart x U' (hpull_src U'E hU'o) (c k)
        ((hcd k).mono (hS_pull U'E hU'o)))
    refine ⟨U', hU'le, ⟨hye, hyU'⟩, c', fun i => holEval_ext fun w => ?_⟩
    have hw := w.2
    rw [holEval_res, map_sum]
    have h1 : ext U (a i) (e w) = _ := hc i (e w) hw.2
    rw [hext' U _ w.1 (hU'le hw) hw.1] at h1
    refine h1.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, holEval_holMk, holEval_res, holEval_holMk]

end Charts

/-- Oka's relation theorem on `ℂ⁰`, a point: the relations among finitely many complex numbers
form a finite-dimensional vector space, spanned by a basis. -/
theorem holomorphicRelationsLocallyFinite_pi_zero :
    HolomorphicRelationsLocallyFinite (Fin 0 → ℂ) 1 := by
  intro V hV p F _ x hx
  let φ : (Fin p → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun a => ∑ i, a i * F i 0 x
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.mul_sum, mul_assoc] }
  let b := Module.finBasis ℂ (LinearMap.ker φ)
  have hx' : ∀ z : Fin 0 → ℂ, z = x := fun z => Subsingleton.elim z x
  refine ⟨V, hV, subset_rfl, hx, Module.finrank ℂ (LinearMap.ker φ),
    fun k i _ => (b k : Fin p → ℂ) i, fun k i => differentiableOn_const _,
    fun k j z _ => ?_, fun U hU _ a _ har y hy => ?_⟩
  · rw [hx' z, Subsingleton.elim j 0]
    exact (b k).2
  · have ha : (fun i => a i x) ∈ LinearMap.ker φ := by
      have := har 0 x (by rw [← hx' y]; exact hy)
      exact this
    refine ⟨U, hU, subset_rfl, hy, fun k _ => b.repr ⟨_, ha⟩ k, fun k => differentiableOn_const _,
      fun i z _ => ?_⟩
    have := congrArg (fun v : LinearMap.ker φ => (v : Fin p → ℂ) i) (b.sum_repr ⟨_, ha⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at this
    rw [hx' z, ← this]

/-! ### The Weierstrass case of the inductive step -/

section Weierstrass

open Filter Topology Polynomial

section Germs

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function complex differentiable on an open subset of a finite-dimensional complex space is
analytic there. -/
theorem analyticOnNhd_of_differentiableOn' [FiniteDimensional ℂ E] {S : Set E}
    (hS : IsOpen S) {G : E → ℂ} (hG : DifferentiableOn ℂ G S) : AnalyticOnNhd ℂ G S := by
  let e : E ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) :=
    (LinearEquiv.ofFinrankEq _ _ (by simp)).toContinuousLinearEquiv
  have h1 : DifferentiableOn ℂ (G ∘ e.symm) (e.symm ⁻¹' S) :=
    hG.comp e.symm.differentiableOn (fun _ h => h)
  have h2 := analyticOnNhd_of_differentiableOn (hS.preimage e.symm.continuous) h1
  intro y hy
  have h3 : AnalyticAt ℂ ((G ∘ e.symm) ∘ e) y :=
    (h2 (e y) (by simpa using hy)).comp (e.analyticAt y)
  simpa [Function.comp_def] using h3

/-- On a finite-dimensional complex space, a function is analytic at `y` if and only if it is
complex differentiable near `y`. -/
theorem analyticAt_iff_eventually_differentiableAt' [FiniteDimensional ℂ E] {f : E → ℂ}
    {y : E} : AnalyticAt ℂ f y ↔ ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ f z := by
  refine ⟨fun h => h.eventually_analyticAt.mono fun z hz => hz.differentiableAt, fun h => ?_⟩
  obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.1 h
  exact analyticOnNhd_of_differentiableOn' hto (fun z hz => (ht z hz).differentiableWithinAt) y hyt

/-- The germ at `y` of a function complex differentiable near `y`. -/
noncomputable def hgerm {y : E} (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ f z) :
    holGerms y :=
  ⟨f, coe_mem_holGerms hf⟩

/-- The germ `hgerm f hf` is the germ of `f`. -/
lemma coe_hgerm {y : E} (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ f z) :
    ((hgerm f hf : holGerms y) : Germ (𝓝 y) ℂ) = f := rfl

/-- Two functions have the same germ at `y` if and only if they agree near `y`. -/
lemma hgerm_eq_iff {y : E} {f g : E → ℂ} (hf : ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ g z) : hgerm f hf = hgerm g hg ↔ f =ᶠ[𝓝 y] g :=
  Subtype.ext_iff.trans Germ.coe_eq

/-- Every holomorphic germ at `y` is the germ of a function complex differentiable near `y`. -/
lemma exists_hgerm {y : E} (a : holGerms y) :
    ∃ f : E → ℂ, ∃ hf : ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ f z, a = hgerm f hf := by
  obtain ⟨f, hf, hd⟩ := a.2
  exact ⟨f, hd, Subtype.ext hf.symm⟩

/-- Holomorphic germs with the same underlying germ are equal. -/
lemma holGerms_ext {y : E} {a b : holGerms y}
    (h : (a : Germ (𝓝 y) ℂ) = b) : a = b := Subtype.ext h

/-- The germ of `f` at `y` is zero if and only if `f` vanishes near `y`. -/
lemma hgerm_eq_zero_iff {y : E} {f : E → ℂ} (hf : ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ f z) :
    hgerm f hf = 0 ↔ f =ᶠ[𝓝 y] 0 :=
  Subtype.ext_iff.trans Germ.coe_eq

/-- The germ at `y` of a function not vanishing at `y` is a unit. -/
lemma isUnit_hgerm {y : E} {f : E → ℂ} (hf : ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ f z)
    (h0 : f y ≠ 0) : IsUnit (hgerm f hf) := by
  have hne : ∀ᶠ z in 𝓝 y, f z ≠ 0 := hf.self_of_nhds.continuousAt.eventually_ne h0
  have hd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ (fun z => (f z)⁻¹) z :=
    (hf.and hne).mono fun z h => h.1.inv h.2
  refine IsUnit.of_mul_eq_one (b := hgerm _ hd) (holGerms_ext ?_)
  change ((fun z => f z * (f z)⁻¹ : E → ℂ) : Germ (𝓝 y) ℂ) = ((1 : E → ℂ) : Germ (𝓝 y) ℂ)
  exact Germ.coe_eq.2 (hne.mono fun z hz => by simp [hz])

/-- A function complex differentiable on an open set `W` is complex differentiable near each
point of `W`. -/
lemma eventually_differentiableAt_of_differentiableOn {W : Set E} (hW : IsOpen W)
    {f : E → ℂ} (hf : DifferentiableOn ℂ f W) {y : E} (hy : y ∈ W) :
    ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ f z :=
  Filter.eventually_of_mem (hW.mem_nhds hy) fun z hz => hf.differentiableAt (hW.mem_nhds hz)

/-- The germ at `y ∈ W` of a function complex differentiable on the open set `W`. -/
noncomputable abbrev germOn {W : Set E} (hW : IsOpen W) {f : E → ℂ}
    (hf : DifferentiableOn ℂ f W) {y : E} (hy : y ∈ W) : holGerms y :=
  hgerm f (eventually_differentiableAt_of_differentiableOn hW hf hy)

/-- The underlying germ of a finite sum of holomorphic germs is the sum of the underlying germs. -/
lemma coe_holGerms_sum {y : E} {ι : Type} (s : Finset ι) (a : ι → holGerms y) :
    ((∑ i ∈ s, a i : holGerms y) : Germ (𝓝 y) ℂ) = ∑ i ∈ s, (a i : Germ (𝓝 y) ℂ) :=
  map_sum (holGerms y).subtype a s

/-- The germ of a pointwise finite sum of functions is the sum of their germs. -/
lemma germ_coe_sum {y : E} {ι : Type} (s : Finset ι) (f : ι → E → ℂ) :
    ((fun z => ∑ i ∈ s, f i z : E → ℂ) : Germ (𝓝 y) ℂ) =
      ∑ i ∈ s, ((f i : E → ℂ) : Germ (𝓝 y) ℂ) := by
  change _ = ∑ i ∈ s, Germ.coeRingHom (𝓝 y) (f i)
  rw [← map_sum (Germ.coeRingHom (𝓝 y))]
  change ((fun z => ∑ i ∈ s, f i z : E → ℂ) : Germ (𝓝 y) ℂ) =
    ((∑ i ∈ s, f i : E → ℂ) : Germ (𝓝 y) ℂ)
  congr 1
  funext z
  simp [Finset.sum_apply]

/-- A germ identity `∑ᵢ aᵢ bᵢ = c` read on representatives. -/
lemma hgerm_sum_mul_eq_iff {y : E} {ι : Type} (s : Finset ι) {a b : ι → E → ℂ}
    (ha : ∀ i, ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ (a i) z)
    (hb : ∀ i, ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ (b i) z) (c : holGerms y) {g : E → ℂ}
    (hc : (c : Germ (𝓝 y) ℂ) = g) :
    ∑ i ∈ s, hgerm (a i) (ha i) * hgerm (b i) (hb i) = c ↔
      (fun z => ∑ i ∈ s, a i z * b i z) =ᶠ[𝓝 y] g := by
  rw [← Germ.coe_eq, ← hc, germ_coe_sum, Subtype.ext_iff, coe_holGerms_sum]
  rfl

end Germs

section Conversions

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Germ form of local generation.** Relations among the `Fᵢ` are generated near `x` as soon as
there are finitely many relations over a neighbourhood `W` whose germs span the germs of
relations at every point of `W`. -/
theorem generatedNear_of_germ {V : Set E} {p q : ℕ} {F : Fin p → Fin q → E → ℂ} {x : E}
    {W : Set E} (hW : IsOpen W) (hWV : W ⊆ V) (hxW : x ∈ W)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) W) {s : ℕ} (r : Fin s → Fin p → E → ℂ)
    (hrd : ∀ k i, DifferentiableOn ℂ (r k i) W) (hr : ∀ k j, ∀ z ∈ W, ∑ i, r k i z * F i j z = 0)
    (hgen : ∀ y (hy : y ∈ W) (a : Fin p → holGerms y),
      (∀ j, ∑ i, a i * germOn hW (hF i j) hy = 0) →
      a ∈ Submodule.span (holGerms y) (Set.range fun k i => germOn hW (hrd k i) hy)) :
    HolomorphicRelationsGeneratedNear V F x := by
  refine ⟨W, hW, hWV, hxW, s, r, hrd, hr, fun U hU hUW a ha har y hy => ?_⟩
  have hyW := hUW hy
  have had : ∀ i, ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ (a i) z := fun i =>
    eventually_differentiableAt_of_differentiableOn hU (ha i) hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (hgen y hyW (fun i => hgerm (a i) (had i)) fun j => by
      refine (hgerm_sum_mul_eq_iff _ _ _ 0 (g := 0) rfl).2 ?_
      exact Filter.eventually_of_mem (hU.mem_nhds hy) fun z hz => har j z hz)
  choose ĉ hĉd hĉ using fun k => exists_hgerm (c k)
  have hci : ∀ i, (fun z => ∑ k, ĉ k z * r k i z) =ᶠ[𝓝 y] a i := fun i => by
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hĉ] at this
    exact (hgerm_sum_mul_eq_iff _ _ _ _ rfl).1 this
  have hev : ∀ᶠ z in 𝓝 y, (∀ k, ∀ᶠ z' in 𝓝 z, DifferentiableAt ℂ (ĉ k) z') ∧
      ∀ i, a i z = ∑ k, ĉ k z * r k i z := by
    refine (Filter.eventually_all.2 fun k => (hĉd k).eventually_nhds).and
      (Filter.eventually_all.2 fun i => (hci i).mono fun z hz => hz.symm)
  obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.1 hev
  refine ⟨t ∩ U, hto.inter hU, Set.inter_subset_right, ⟨hyt, hy⟩, ĉ, fun k z hz =>
    ((ht z hz.1).1 k).self_of_nhds.differentiableWithinAt, fun i z hz => (ht z hz.1).2 i⟩

/-- **Local generation read on germs.** -/
theorem mem_span_germOn_of_generatedNear {W : Set E} (hW : IsOpen W) {p q s : ℕ}
    {F : Fin p → Fin q → E → ℂ} (hF : ∀ i j, DifferentiableOn ℂ (F i j) W)
    {r : Fin s → Fin p → E → ℂ} (hrd : ∀ k i, DifferentiableOn ℂ (r k i) W)
    (hgen : ∀ U : Set E, IsOpen U → U ⊆ W → ∀ a : Fin p → E → ℂ,
      (∀ i, DifferentiableOn ℂ (a i) U) → (∀ j, ∀ z ∈ U, ∑ i, a i z * F i j z = 0) →
      ∀ y ∈ U, ∃ U' : Set E, IsOpen U' ∧ U' ⊆ U ∧ y ∈ U' ∧ ∃ c : Fin s → E → ℂ,
        (∀ k, DifferentiableOn ℂ (c k) U') ∧ ∀ i, ∀ z ∈ U', a i z = ∑ k, c k z * r k i z)
    {y : E} (hy : y ∈ W) (a : Fin p → holGerms y)
    (ha : ∀ j, ∑ i, a i * germOn hW (hF i j) hy = 0) :
    a ∈ Submodule.span (holGerms y) (Set.range fun k i => germOn hW (hrd k i) hy) := by
  choose â hâd hâ using fun i => exists_hgerm (a i)
  have hrel : ∀ j, (fun z => ∑ i, â i z * F i j z) =ᶠ[𝓝 y] (0 : E → ℂ) := fun j => by
    have := ha j
    simp only [hâ] at this
    exact (hgerm_sum_mul_eq_iff _ _ _ 0 rfl).1 this
  have hev : ∀ᶠ z in 𝓝 y, (∀ i, ∀ᶠ z' in 𝓝 z, DifferentiableAt ℂ (â i) z') ∧
      ∀ j, ∑ i, â i z * F i j z = 0 :=
    (Filter.eventually_all.2 fun i => (hâd i).eventually_nhds).and
      (Filter.eventually_all.2 hrel)
  obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.1 hev
  obtain ⟨U', hU'o, hU'U, hyU', c, hcd, hc⟩ := hgen (t ∩ W) (hto.inter hW) Set.inter_subset_right â
    (fun i z hz => ((ht z hz.1).1 i).self_of_nhds.differentiableWithinAt)
    (fun j z hz => (ht z hz.1).2 j) y ⟨hyt, hy⟩
  refine (Submodule.mem_span_range_iff_exists_fun _).2
    ⟨fun k => germOn hU'o (hcd k) hyU', funext fun i => ?_⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hâ]
  refine ((hgerm_sum_mul_eq_iff _ _ _ _ rfl).2 ?_)
  exact Filter.eventually_of_mem (hU'o.mem_nhds hyU') fun z hz => (hc i z hz).symm

end Conversions

section AlgCore

/-- Let `φ : R'[X] →+* R` be injective, let `G i₀ = Q Q'` be monic with `Q` monic and `φ Q'` a
unit, and suppose every element of `R` is uniquely `h φ(Q) + φ(r)` with `deg r < deg Q`. Then
every relation `∑ᵢ aᵢ φ(Gᵢ) = 0` among polynomials `Gᵢ` of degree `≤ d` lies in the span of the
images of the polynomial relations `∑ᵢ πᵢ Gᵢ = 0` with `deg πᵢ ≤ 3d`. -/
theorem mem_span_polyRelations_of_sum_mul_eq_zero {R' R : Type*} [CommRing R'] [Nontrivial R']
    [CommRing R] (φ : R'[X] →+* R) (hφ : Function.Injective φ) {p d : ℕ} (i0 : Fin p)
    (G : Fin p → R'[X]) (hG : ∀ i, (G i).natDegree ≤ d) (hP : (G i0).Monic)
    (Q Q' : R'[X]) (hQ : Q.Monic) (hPQ : G i0 = Q * Q') (hQ' : IsUnit (φ Q'))
    (hdiv : ∀ g : R, ∃ h : R, ∃ r : R'[X], r.degree < Q.degree ∧ g = h * φ Q + φ r)
    (huniq : ∀ (h : R) (r : R'[X]), r.degree < Q.degree → h * φ Q + φ r = 0 → h = 0 ∧ r = 0)
    (a : Fin p → R) (ha : ∑ i, a i * φ (G i) = 0) :
    a ∈ Submodule.span R {b | ∃ π : Fin p → R'[X], (∀ i, (π i).natDegree ≤ 3 * d) ∧
      ∑ i, π i * G i = 0 ∧ b = fun i => φ (π i)} := by
  classical
  set S := {b : Fin p → R | ∃ π : Fin p → R'[X], (∀ i, (π i).natDegree ≤ 3 * d) ∧
      ∑ i, π i * G i = 0 ∧ b = fun i => φ (π i)} with hS
  have hQ'0 : Q' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hPQ
    exact hP.ne_zero hPQ
  have hdegP := hG i0
  rw [hPQ, hQ.natDegree_mul' hQ'0] at hdegP
  obtain ⟨u, hu⟩ : ∃ u, u * φ Q' = 1 := hQ'.exists_left_inv
  choose b r hr hbr using hdiv
  have hrdeg : ∀ g, (r g).natDegree ≤ d := fun g => by
    have := natDegree_le_natDegree (le_of_lt (hr g))
    omega
  let rr : Fin p → R'[X] := fun i => if i = i0 then 0 else r (a i)
  have hrr : ∀ i, (rr i).natDegree ≤ d := fun i => by
    by_cases h : i = i0 <;> simp [rr, h, hrdeg]
  let lam : Fin p → R := fun i => if i = i0 then 0 else b (a i) * u
  let T : Fin p → Fin p → R'[X] := fun i k =>
    (if k = i then G i0 else 0) - (if k = i0 then G i else 0)
  have hT : ∀ i, (fun k => φ (T i k)) ∈ S := fun i => by
    refine ⟨T i, fun k => ?_, ?_, rfl⟩
    · have h1 : (if k = i then G i0 else 0).natDegree ≤ d := by
        split_ifs
        · exact hG i0
        · simp
      have h2 : (if k = i0 then G i else 0).natDegree ≤ d := by
        split_ifs
        · exact hG i
        · simp
      exact (natDegree_sub_le _ _).trans (max_le (by omega) (by omega))
    · simp only [T, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
  let a' : Fin p → R := a - ∑ i, lam i • fun k => φ (T i k)
  have ha'k : ∀ k, k ≠ i0 → a' k = φ (rr k) := fun k hk => by
    simp only [a', Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, T, map_sub,
      apply_ite φ, map_zero, mul_sub, mul_ite, mul_zero, if_neg hk, sub_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, rr, lam]
    rw [hPQ, map_mul]
    linear_combination hbr (a k) - b (a k) * φ Q * hu
  have ha' : ∑ k, a' k * φ (G k) = 0 := by
    have hTrel : ∀ i, ∑ k, φ (T i k) * φ (G k) = 0 := fun i => by
      simp only [← map_mul, ← map_sum, T, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_comm (G i0), sub_self, map_zero]
    simp only [a', Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib, ha, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, hTrel, mul_zero, Finset.sum_const_zero, sub_zero]
  set H : R'[X] := -(∑ k, rr k * G k) with hHdef
  have hα : a' i0 * φ (G i0) = φ H := by
    have : ∑ k, a' k * φ (G k) = a' i0 * φ (G i0) + φ (∑ k, rr k * G k) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), map_sum,
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
      simp only [rr, if_pos rfl, zero_mul, map_zero, zero_add]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.ne_of_mem_erase hk
      rw [ha'k k hk', map_mul]
    rw [ha'] at this
    rw [hHdef, map_neg]
    linear_combination -this
  have hH : H.natDegree ≤ 2 * d := by
    rw [hHdef, natDegree_neg]
    refine natDegree_sum_le_of_forall_le _ _ fun k _ => (natDegree_mul_le).trans ?_
    have := hrr k; have := hG k; omega
  set c := H /ₘ G i0 with hc
  set ρ := H %ₘ G i0 with hρdef
  have hρ : ρ + G i0 * c = H := modByMonic_add_div H (G i0)
  set q := ρ /ₘ Q with hq
  set ρ' := ρ %ₘ Q with hρ'def
  have hρ' : ρ' + Q * q = ρ := modByMonic_add_div ρ Q
  have key := huniq (-((a' i0 - φ c) * φ Q' - φ q)) ρ' (degree_modByMonic_lt _ hQ) (by
    have e1 : φ ρ = (a' i0 - φ c) * φ (G i0) := by
      rw [sub_mul, hα, ← hρ, map_add, map_mul]; ring
    have e2 : φ ρ' = φ ρ - φ Q * φ q := by rw [← hρ', map_add, map_mul]; ring
    rw [e2, e1, hPQ, map_mul]; ring)
  have hkey : φ Q' * a' i0 = φ (c * Q' + q) := by
    have := key.1
    rw [neg_eq_zero, sub_eq_zero] at this
    rw [map_add, map_mul, ← this]; ring
  let π : Fin p → R'[X] := fun k => if k = i0 then c * Q' + q else Q' * rr k
  have hπ : ∀ k, φ (π k) = φ Q' * a' k := fun k => by
    by_cases hk : k = i0
    · subst hk; simp only [π, if_pos rfl, hkey]
    · simp only [π, if_neg hk, map_mul, ha'k k hk]
  have hπrel : ∑ k, π k * G k = 0 := hφ <| by
    rw [map_sum, map_zero]
    simp only [map_mul, hπ, mul_assoc, ← Finset.mul_sum, ha', mul_zero]
  have hπdeg : ∀ k, (π k).natDegree ≤ 3 * d := fun k => by
    by_cases hk : k = i0
    · simp only [π, if_pos hk]
      refine (natDegree_add_le _ _).trans (max_le ((natDegree_mul_le).trans ?_) ?_)
      · have : c.natDegree ≤ 2 * d := by
          rw [hc, natDegree_divByMonic _ hP]; omega
        omega
      · have : ρ.natDegree ≤ d := (natDegree_modByMonic_le _ hP).trans (hG i0)
        rw [hq, natDegree_divByMonic _ hQ]; omega
    · simp only [π, if_neg hk]
      refine (natDegree_mul_le).trans ?_
      have := hrr k; omega
  have ha'eq : a' = u • fun k => φ (π k) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, hπ, ← mul_assoc, hu, one_mul]
  have hasum : a = a' + ∑ i, lam i • fun k => φ (T i k) := by
    simp only [a', sub_add_cancel]
  rw [hasum]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hT i)))
  rw [ha'eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨π, hπdeg, hπrel, rfl⟩)

end AlgCore

section Prod

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- Germs of functions of `z'` as germs of functions of `(z', w)`. -/
noncomputable def fstHom (z : E' × ℂ) : holGerms z.1 →+* holGerms z :=
  holPullback Prod.fst differentiable_fst (continuous_fst.tendsto z)

/-- The germ of the last coordinate `w`. -/
noncomputable def wGerm (z : E' × ℂ) : holGerms z :=
  hgerm (fun p => p.2) (Eventually.of_forall fun _ => differentiableAt_snd)

/-- Evaluating a polynomial in `w` with coefficients germs at `z'` gives a germ at
`z = (z', w₀)`. -/
noncomputable def polyHom (z : E' × ℂ) : (holGerms z.1)[X] →+* holGerms z :=
  Polynomial.eval₂RingHom (fstHom z) (wGerm z)

/-- The constant germ. -/
noncomputable def cst (y : E) (c : ℂ) : holGerms y :=
  hgerm (fun _ => c) (Eventually.of_forall fun _ => differentiableAt_const _)

/-- The germ `fstHom z g` is the germ of `g` composed with the first projection. -/
lemma coe_fstHom (z : E' × ℂ) (g : holGerms z.1) :
    ((fstHom z g : holGerms z) : Germ (𝓝 z) ℂ) =
      (g : Germ (𝓝 z.1) ℂ).compTendsto Prod.fst (continuous_fst.tendsto z) := rfl

/-- The polynomial `X` evaluates to the germ of the last coordinate `w`. -/
lemma coe_polyHom_X (z : E' × ℂ) :
    ((polyHom z Polynomial.X : holGerms z) : Germ (𝓝 z) ℂ) = ((fun p => p.2 : E' × ℂ → ℂ) :
      Germ (𝓝 z) ℂ) := by
  simp [polyHom]; rfl

/-- The polynomial `X - c` evaluates to the germ of `(z', w) ↦ w - c`. -/
lemma coe_polyHom_X_sub_C (z : E' × ℂ) (c : ℂ) :
    ((polyHom z (Polynomial.X - C (cst z.1 c)) : holGerms z) : Germ (𝓝 z) ℂ) =
      ((fun p => p.2 - c : E' × ℂ → ℂ) : Germ (𝓝 z) ℂ) := by
  simp [polyHom]; rfl

/-- If `T` evaluates to the germ of `τ`, then `∑ₘ bₘ T^{eₘ}` evaluates to the germ of
`(z', w) ↦ ∑ₘ bₘ(z') τ(z', w)^{eₘ}`. -/
lemma coe_polyHom_sum {ι : Type} (z : E' × ℂ) (T : (holGerms z.1)[X]) (τ : E' × ℂ → ℂ)
    (hT : ((polyHom z T : holGerms z) : Germ (𝓝 z) ℂ) = τ) (s : Finset ι) (b : ι → E' → ℂ)
    (hb : ∀ m, ∀ᶠ y in 𝓝 z.1, DifferentiableAt ℂ (b m) y) (ex : ι → ℕ) :
    ((polyHom z (∑ m ∈ s, C (hgerm (b m) (hb m)) * T ^ ex m) : holGerms z) : Germ (𝓝 z) ℂ) =
      ((fun p => ∑ m ∈ s, b m p.1 * τ p ^ ex m : E' × ℂ → ℂ) : Germ (𝓝 z) ℂ) := by
  rw [map_sum]
  change (holGerms z).subtype _ = Germ.coeRingHom (𝓝 z) _
  rw [map_sum (holGerms z).subtype]
  rw [show (fun p => ∑ m ∈ s, b m p.1 * τ p ^ ex m : E' × ℂ → ℂ) =
    ∑ m ∈ s, (fun p : E' × ℂ => b m p.1) * τ ^ ex m from by ext p; simp, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_pow, map_mul, map_pow, map_mul, map_pow]
  change ((polyHom z (C _) : holGerms z) : Germ (𝓝 z) ℂ) * ((polyHom z T : holGerms z) :
    Germ (𝓝 z) ℂ) ^ ex m = _
  rw [hT]
  simp only [polyHom, Polynomial.coe_eval₂RingHom, eval₂_C]
  rfl

/-- A polynomial over `ℂ` vanishing near a point is zero. -/
lemma polynomial_eq_zero_of_eventually_eval_eq_zero {P : ℂ[X]} {c : ℂ}
    (h : ∀ᶠ w in 𝓝 c, P.eval w = 0) : P = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot P (Set.Infinite.mono (fun w hw => hw) ?_)
  refine Set.infinite_coe_iff.1 (Cardinal.infinite_iff.2 ?_)
  rw [show {x | P.IsRoot x} = {x | P.eval x = 0} from rfl, cardinal_eq_of_mem_nhds ℂ h]
  exact Cardinal.infinite_iff.1 inferInstance

/-- **Polynomials in `w` are determined by their germs.** -/
theorem polyHom_injective (z : E' × ℂ) : Function.Injective (polyHom z) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  set N := g.natDegree + 1
  choose β hβd hβ using fun m => exists_hgerm (g.coeff m)
  have hg' : g = ∑ m ∈ Finset.range N, C (hgerm (β m) (hβd m)) * Polynomial.X ^ m := by
    conv_lhs => rw [as_sum_range_C_mul_X_pow g]
    simp only [hβ]
    rfl
  have h1 :=
    coe_polyHom_sum z Polynomial.X _ (coe_polyHom_X z) (Finset.range N) β hβd (fun m => m)
  rw [← hg', hg] at h1
  have h2 : ∀ᶠ p in 𝓝 z, ∑ m ∈ Finset.range N, β m p.1 * p.2 ^ m = 0 :=
    (Germ.coe_eq.1 h1.symm)
  rw [nhds_prod_eq] at h2
  have h3 := h2.curry
  have h4 : ∀ m < N, ∀ᶠ y in 𝓝 z.1, β m y = 0 := by
    intro m hm
    refine h3.mono fun y hy => ?_
    have hP := polynomial_eq_zero_of_eventually_eval_eq_zero
      (P := ∑ k ∈ Finset.range N, C (β k y) * Polynomial.X ^ k)
      (c := z.2) (hy.mono fun w hw => by simpa [eval_finset_sum] using hw)
    have := congrArg (fun P => P.coeff m) hP
    simpa [finset_sum_coeff, coeff_C_mul_X_pow, hm] using this
  refine Polynomial.ext fun m => ?_
  rw [coeff_zero]
  by_cases hm : m < N
  · rw [hβ m, hgerm_eq_zero_iff]
    exact h4 m hm
  · exact coeff_eq_zero_of_natDegree_lt (p := g) (by omega)

end Prod

section MovingCentre

variable {k : ℕ}

/-- Recentring at `z`: the order in `w` of `p ↦ f (p + z)` at `0` is that of `f` at `z`. -/
lemma analyticOrderAt_recentre (f : (Fin k → ℂ) × ℂ → ℂ) (z : (Fin k → ℂ) × ℂ) :
    analyticOrderAt (fun w : ℂ => f ((0, w) + z)) 0 =
      analyticOrderAt (fun t : ℂ => f (z.1, z.2 + t)) 0 := by
  congr 1
  funext w
  congr 1
  ext <;> simp [add_comm]

/-- **Weierstrass division at a point `z`.** -/
theorem weierstrassDivision_at {e : ℕ} (he : 1 ≤ e) {f : (Fin k → ℂ) × ℂ → ℂ}
    {z : (Fin k → ℂ) × ℂ} (hf : AnalyticAt ℂ f z)
    (hfe : analyticOrderAt (fun t : ℂ => f (z.1, z.2 + t)) 0 = e) :
    (∀ h : (Fin k → ℂ) × ℂ → ℂ, AnalyticAt ℂ h z → ∃ q : (Fin k → ℂ) × ℂ → ℂ,
      ∃ a : Fin e → (Fin k → ℂ) → ℂ, AnalyticAt ℂ q z ∧ (∀ i, AnalyticAt ℂ (a i) z.1) ∧
        h =ᶠ[𝓝 z] fun p => f p * q p + ∑ i, a i p.1 * (p.2 - z.2) ^ (i : ℕ)) ∧
    (∀ (q : (Fin k → ℂ) × ℂ → ℂ) (a : Fin e → (Fin k → ℂ) → ℂ), AnalyticAt ℂ q z →
      (∀ i, AnalyticAt ℂ (a i) z.1) →
      (fun p => f p * q p + ∑ i, a i p.1 * (p.2 - z.2) ^ (i : ℕ)) =ᶠ[𝓝 z] 0 →
      q =ᶠ[𝓝 z] 0 ∧ ∀ i, a i =ᶠ[𝓝 z.1] 0) := by
  set f' : (Fin k → ℂ) × ℂ → ℂ := fun p => f (p + z)
  have hf' : AnalyticAt ℂ f' 0 :=
    hf.comp_of_eq ((analyticAt_id).add analyticAt_const) (by simp)
  have hf'e : analyticOrderAt (fun w : ℂ => f' (0, w)) 0 = e :=
    (analyticOrderAt_recentre f z).trans hfe
  have htz : Tendsto (fun p => p - z) (𝓝 z) (𝓝 0) :=
    (continuous_sub_right z).tendsto' z 0 (sub_self z)
  have hz0 : Tendsto (fun p => p + z) (𝓝 0) (𝓝 z) :=
    (continuous_add_const z).tendsto' 0 z (zero_add z)
  have htz1 : Tendsto (fun y => y - z.1) (𝓝 z.1) (𝓝 0) :=
    (continuous_sub_right z.1).tendsto' z.1 0 (sub_self z.1)
  constructor
  · intro h hh
    obtain ⟨q, a, ⟨hq, ha, hqa⟩, -⟩ := MMP.Convergent.existsUnique_weierstrassDivision he hf' hf'e
      (h := fun p => h (p + z)) (hh.comp_of_eq ((analyticAt_id).add analyticAt_const) (by simp))
    refine ⟨fun p => q (p - z), fun i y => a i (y - z.1),
      hq.comp_of_eq ((analyticAt_id).sub analyticAt_const) (by simp),
      fun i => (ha i).comp_of_eq ((analyticAt_id).sub analyticAt_const) (by simp), ?_⟩
    filter_upwards [htz.eventually hqa] with p hp
    simpa [f'] using hp
  · intro q a hq ha h0
    obtain ⟨q0, a0, -, huniq⟩ := MMP.Convergent.existsUnique_weierstrassDivision he hf' hf'e
      (h := 0) analyticAt_const
    have hA := huniq (fun p => q (p + z)) (fun i y => a i (y + z.1))
      (hq.comp_of_eq ((analyticAt_id).add analyticAt_const) (by simp))
      (fun i => (ha i).comp_of_eq ((analyticAt_id).add analyticAt_const) (by simp)) (by
        filter_upwards [hz0.eventually h0] with p hp
        simp only [Pi.zero_apply] at hp ⊢
        rw [← hp]
        simp [f'])
    have hB := huniq 0 0 analyticAt_const (fun _ => analyticAt_const) (by
      filter_upwards with p
      simp)
    refine ⟨?_, fun i => ?_⟩
    · filter_upwards [htz.eventually (hA.1.trans hB.1.symm)] with p hp
      simpa using hp
    · filter_upwards [htz1.eventually ((hA.2 i).trans (hB.2 i).symm)] with p hp
      simpa using hp

/-- **Weierstrass preparation at a point `z`.** -/
theorem weierstrassPreparation_at {e : ℕ} (he : 1 ≤ e) {f : (Fin k → ℂ) × ℂ → ℂ}
    {z : (Fin k → ℂ) × ℂ} (hf : AnalyticAt ℂ f z)
    (hfe : analyticOrderAt (fun t : ℂ => f (z.1, z.2 + t)) 0 = e) :
    ∃ u : (Fin k → ℂ) × ℂ → ℂ, ∃ b : Fin e → (Fin k → ℂ) → ℂ,
      AnalyticAt ℂ u z ∧ u z ≠ 0 ∧ (∀ i, AnalyticAt ℂ (b i) z.1 ∧ b i z.1 = 0) ∧
        f =ᶠ[𝓝 z] fun p => u p * ((p.2 - z.2) ^ e + ∑ i, b i p.1 * (p.2 - z.2) ^ (i : ℕ)) := by
  set f' : (Fin k → ℂ) × ℂ → ℂ := fun p => f (p + z)
  have hf' : AnalyticAt ℂ f' 0 :=
    hf.comp_of_eq ((analyticAt_id).add analyticAt_const) (by simp)
  have hf'e : analyticOrderAt (fun w : ℂ => f' (0, w)) 0 = e :=
    (analyticOrderAt_recentre f z).trans hfe
  have htz : Tendsto (fun p => p - z) (𝓝 z) (𝓝 0) :=
    (continuous_sub_right z).tendsto' z 0 (sub_self z)
  obtain ⟨u, b, ⟨hu, hu0, hb, hfu⟩, -⟩ :=
    MMP.Convergent.existsUnique_weierstrassPreparation he hf' hf'e
  refine ⟨fun p => u (p - z), fun i y => b i (y - z.1),
    hu.comp_of_eq ((analyticAt_id).sub analyticAt_const) (by simp), by simpa using hu0,
    fun i => ⟨(hb i).1.comp_of_eq ((analyticAt_id).sub analyticAt_const) (by simp),
      by simpa using (hb i).2⟩, ?_⟩
  filter_upwards [htz.eventually hfu] with p hp
  simpa [f'] using hp

end MovingCentre

section Divisor

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- A function analytic at `y` is complex differentiable near `y`. -/
lemma eventually_differentiableAt_of_analyticAt {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℂ} {y : E} (hf : AnalyticAt ℂ f y) :
    ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ f z :=
  hf.eventually_analyticAt.mono fun _ h => h.differentiableAt

/-- The polynomial `∑_{i < e} aᵢ (X - c)ⁱ` has degree `< e`. -/
lemma degree_sum_C_mul_X_sub_C_pow_lt {R : Type} [CommRing R] [Nontrivial R] (c : R)
    {e : ℕ} (a : Fin e → R) :
    (∑ i : Fin e, C (a i) * (Polynomial.X - C c) ^ (i : ℕ)).degree < (e : WithBot ℕ) := by
  refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun i _ => ?_)
  refine lt_of_le_of_lt (degree_le_of_natDegree_le (n := i) (by compute_degree)) ?_
  exact_mod_cast i.2

variable {k : ℕ}

/-- The Weierstrass polynomial `(w - w₀)ᵉ + ∑ bᵢ (w - w₀)ⁱ` over the germs at `z'`. -/
noncomputable def wPoly (z : (Fin k → ℂ) × ℂ) {e : ℕ} (b : Fin e → (Fin k → ℂ) → ℂ)
    (hb : ∀ i, AnalyticAt ℂ (b i) z.1) : (holGerms z.1)[X] :=
  (Polynomial.X - C (cst z.1 z.2)) ^ e +
    ∑ i, C (hgerm (b i) (eventually_differentiableAt_of_analyticAt (hb i))) *
      (Polynomial.X - C (cst z.1 z.2)) ^ (i : ℕ)

/-- The Weierstrass polynomial is monic. -/
lemma monic_wPoly (z : (Fin k → ℂ) × ℂ) {e : ℕ} (b : Fin e → (Fin k → ℂ) → ℂ)
    (hb : ∀ i, AnalyticAt ℂ (b i) z.1) : (wPoly z b hb).Monic := by
  refine ((monic_X_sub_C _).pow e).add_of_left ?_
  rw [degree_eq_natDegree ((monic_X_sub_C _).pow e).ne_zero, (monic_X_sub_C _).natDegree_pow,
    natDegree_X_sub_C, mul_one]
  exact degree_sum_C_mul_X_sub_C_pow_lt _ _

/-- The Weierstrass polynomial has degree `e`. -/
lemma degree_wPoly (z : (Fin k → ℂ) × ℂ) {e : ℕ} (b : Fin e → (Fin k → ℂ) → ℂ)
    (hb : ∀ i, AnalyticAt ℂ (b i) z.1) : (wPoly z b hb).degree = e := by
  rw [wPoly, degree_add_eq_left_of_degree_lt, degree_eq_natDegree ((monic_X_sub_C _).pow e).ne_zero,
    (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [degree_eq_natDegree ((monic_X_sub_C _).pow e).ne_zero, (monic_X_sub_C _).natDegree_pow,
    natDegree_X_sub_C, mul_one]
  exact degree_sum_C_mul_X_sub_C_pow_lt _ _

/-- The Weierstrass polynomial evaluates to the germ at `z` of
`(z', w) ↦ (w - w₀)ᵉ + ∑ᵢ bᵢ(z') (w - w₀)ⁱ`. -/
lemma coe_polyHom_wPoly (z : (Fin k → ℂ) × ℂ) {e : ℕ} (b : Fin e → (Fin k → ℂ) → ℂ)
    (hb : ∀ i, AnalyticAt ℂ (b i) z.1) :
    ((polyHom z (wPoly z b hb) : holGerms z) : Germ (𝓝 z) ℂ) =
      ((fun p => (p.2 - z.2) ^ e + ∑ i, b i p.1 * (p.2 - z.2) ^ (i : ℕ) :
        (Fin k → ℂ) × ℂ → ℂ) : Germ (𝓝 z) ℂ) := by
  rw [wPoly, map_add, map_pow, Subring.coe_add, Subring.coe_pow]
  rw [coe_polyHom_X_sub_C, coe_polyHom_sum z _ _ (coe_polyHom_X_sub_C z z.2)]
  rfl

/-- The function `(z', w) ↦ (w - w₀)ᵉ + ∑ᵢ bᵢ(z') (w - w₀)ⁱ` is analytic at `z`. -/
lemma analyticAt_wFun (z : (Fin k → ℂ) × ℂ) {e : ℕ} (b : Fin e → (Fin k → ℂ) → ℂ)
    (hb : ∀ i, AnalyticAt ℂ (b i) z.1) :
    AnalyticAt ℂ (fun p : (Fin k → ℂ) × ℂ => (p.2 - z.2) ^ e +
      ∑ i, b i p.1 * (p.2 - z.2) ^ (i : ℕ)) z := by
  have h1 : AnalyticAt ℂ (fun p : (Fin k → ℂ) × ℂ => p.2 - z.2) z :=
    analyticAt_snd.sub analyticAt_const
  refine (h1.pow e).add ?_
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact ((hb i).comp analyticAt_fst).mul (h1.pow _)

/-- If every `bᵢ` vanishes at `z'`, then for `F(z', w) = (w - w₀)ᵉ + ∑ᵢ bᵢ(z') (w - w₀)ⁱ` the
function `t ↦ F(z', w₀ + t)` has order `e` at `0`. -/
lemma analyticOrderAt_wFun (z : (Fin k → ℂ) × ℂ) {e : ℕ} (b : Fin e → (Fin k → ℂ) → ℂ)
    (hb0 : ∀ i, b i z.1 = 0) :
    analyticOrderAt (fun t : ℂ => (fun p : (Fin k → ℂ) × ℂ => (p.2 - z.2) ^ e +
      ∑ i, b i p.1 * (p.2 - z.2) ^ (i : ℕ)) (z.1, z.2 + t)) 0 = e := by
  have : (fun t : ℂ => (fun p : (Fin k → ℂ) × ℂ => (p.2 - z.2) ^ e +
      ∑ i, b i p.1 * (p.2 - z.2) ^ (i : ℕ)) (z.1, z.2 + t)) = (fun t => t - 0) ^ e := by
    funext t
    simp [hb0]
  rw [this]
  exact analyticOrderAt_centeredMonomial

/-- **Division by a Weierstrass polynomial on germs**: every germ at `z` is `h Q + r` with
`deg r < deg Q`, uniquely. -/
theorem wPoly_div (z : (Fin k → ℂ) × ℂ) {e : ℕ} (he : 1 ≤ e)
    (b : Fin e → (Fin k → ℂ) → ℂ) (hb : ∀ i, AnalyticAt ℂ (b i) z.1) (hb0 : ∀ i, b i z.1 = 0) :
    (∀ g : holGerms z, ∃ (h : holGerms z) (r : (holGerms z.1)[X]),
      r.degree < (wPoly z b hb).degree ∧ g = h * polyHom z (wPoly z b hb) + polyHom z r) ∧
    (∀ (h : holGerms z) (r : (holGerms z.1)[X]), r.degree < (wPoly z b hb).degree →
      h * polyHom z (wPoly z b hb) + polyHom z r = 0 → h = 0 ∧ r = 0) := by
  set Qf : (Fin k → ℂ) × ℂ → ℂ := fun p => (p.2 - z.2) ^ e + ∑ i, b i p.1 * (p.2 - z.2) ^ (i : ℕ)
    with hQf
  obtain ⟨hex, hun⟩ := weierstrassDivision_at he (analyticAt_wFun z b hb)
    (analyticOrderAt_wFun z b hb0)
  rw [degree_wPoly]
  constructor
  · intro g
    obtain ⟨γ, hγd, rfl⟩ := exists_hgerm g
    obtain ⟨q, a, hq, ha, heq⟩ := hex γ (analyticAt_iff_eventually_differentiableAt'.2 hγd)
    refine ⟨hgerm q (eventually_differentiableAt_of_analyticAt hq),
      ∑ i, C (hgerm (a i) (eventually_differentiableAt_of_analyticAt (ha i))) *
        (Polynomial.X - C (cst z.1 z.2)) ^ (i : ℕ), degree_sum_C_mul_X_sub_C_pow_lt _ _, ?_⟩
    apply holGerms_ext
    rw [Subring.coe_add, Subring.coe_mul]
    rw [coe_polyHom_wPoly, coe_polyHom_sum z _ _ (coe_polyHom_X_sub_C z z.2), coe_hgerm,
      coe_hgerm, ← Germ.coe_mul, ← Germ.coe_add]
    exact Germ.coe_eq.2 (heq.trans (Eventually.of_forall fun p => by simp [mul_comm]))
  · intro h r hr h0
    set c := cst z.1 z.2
    have hrn : r.natDegree < e := by
      by_cases hr0 : r = 0
      · rw [hr0, natDegree_zero]; omega
      · exact (natDegree_lt_iff_degree_lt hr0).2 hr
    have hrT : r = ∑ i ∈ Finset.range e, C ((taylor c r).coeff i) * (Polynomial.X - C c) ^ i := by
      conv_lhs => rw [← sum_taylor_eq r c]
      exact sum_over_range' _ (fun _ => by simp) e (by rwa [natDegree_taylor])
    choose ρ hρd hρ using fun i => exists_hgerm ((taylor c r).coeff i)
    obtain ⟨η, hηd, rfl⟩ := exists_hgerm h
    have hrT' : r = ∑ i ∈ Finset.range e, C (hgerm (ρ i) (hρd i)) * (Polynomial.X - C c) ^ i := by
      rw [hrT]; simp only [hρ]
    have hfun : (fun p => Qf p * η p + ∑ i : Fin e, ρ i p.1 * (p.2 - z.2) ^ (i : ℕ)) =ᶠ[𝓝 z] 0 := by
      have := congrArg (fun g : holGerms z => (g : Germ (𝓝 z) ℂ)) h0
      simp only [Subring.coe_add, Subring.coe_mul, ZeroMemClass.coe_zero] at this
      rw [hrT', coe_polyHom_wPoly, coe_polyHom_sum z _ _ (coe_polyHom_X_sub_C z z.2), coe_hgerm,
        ← Germ.coe_mul, ← Germ.coe_add] at this
      filter_upwards [Germ.coe_eq.1 this] with p hp
      simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply, Qf, Finset.sum_range] at hp ⊢
      linear_combination hp
    obtain ⟨hη, hρ0⟩ := hun η (fun i => ρ i) (analyticAt_iff_eventually_differentiableAt'.2 hηd)
      (fun i => analyticAt_iff_eventually_differentiableAt'.2 (hρd i)) hfun
    refine ⟨(hgerm_eq_zero_iff _).2 hη, ?_⟩
    have hT0 : taylor c r = 0 := by
      refine Polynomial.ext fun i => ?_
      rw [coeff_zero]
      by_cases hi : i < e
      · rw [hρ i, hgerm_eq_zero_iff]
        exact hρ0 ⟨i, hi⟩
      · exact coeff_eq_zero_of_natDegree_lt (by rw [natDegree_taylor]; omega)
    rw [← sum_taylor_eq r c, hT0]
    simp

end Divisor

section PolyRel

variable {k : ℕ}

/-- The polynomial `∑_{m ≤ d} cₘ wᵐ` over the germs at `y`. -/
noncomputable def coeffPoly {W' : Set (Fin k → ℂ)} (hW' : IsOpen W') (d : ℕ)
    (c : ℕ → (Fin k → ℂ) → ℂ) (hc : ∀ m, DifferentiableOn ℂ (c m) W') {y : Fin k → ℂ}
    (hy : y ∈ W') : (holGerms y)[X] :=
  ∑ m ∈ Finset.range (d + 1), C (germOn hW' (hc m) hy) * Polynomial.X ^ m

/-- The germ of the zero function is zero. -/
lemma germOn_eq_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Set E}
    (hW : IsOpen W) {f : E → ℂ} (hf : DifferentiableOn ℂ f W) {y : E} (hy : y ∈ W) (h0 : f = 0) :
    germOn hW hf hy = 0 :=
  holGerms_ext (by rw [coe_hgerm, h0]; rfl)

/-- If `cₘ = 0` for `m > d`, the `m`-th coefficient of `coeffPoly` is the germ of `cₘ`. -/
lemma coeff_coeffPoly {W' : Set (Fin k → ℂ)} (hW' : IsOpen W') (d : ℕ)
    (c : ℕ → (Fin k → ℂ) → ℂ) (hc : ∀ m, DifferentiableOn ℂ (c m) W')
    (hcd : ∀ m, d < m → c m = 0) {y : Fin k → ℂ} (hy : y ∈ W') (m : ℕ) :
    (coeffPoly hW' d c hc hy).coeff m = germOn hW' (hc m) hy := by
  rw [coeffPoly, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [germOn_eq_zero hW' (hc m) hy (hcd m (by simp at h; omega))]

/-- The polynomial `coeffPoly` has degree at most `d`. -/
lemma natDegree_coeffPoly_le {W' : Set (Fin k → ℂ)} (hW' : IsOpen W') (d : ℕ)
    (c : ℕ → (Fin k → ℂ) → ℂ) (hc : ∀ m, DifferentiableOn ℂ (c m) W') {y : Fin k → ℂ}
    (hy : y ∈ W') : (coeffPoly hW' d c hc hy).natDegree ≤ d := by
  refine natDegree_sum_le_of_forall_le _ _ fun m hm => (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.le_of_lt_succ (Finset.mem_range.1 hm)

/-- The polynomial `coeffPoly` evaluates to the germ at `z` of `(z', w) ↦ ∑_{m ≤ d} cₘ(z') wᵐ`. -/
lemma coe_polyHom_coeffPoly {W' : Set (Fin k → ℂ)} (hW' : IsOpen W') (d : ℕ)
    (c : ℕ → (Fin k → ℂ) → ℂ) (hc : ∀ m, DifferentiableOn ℂ (c m) W') (z : (Fin k → ℂ) × ℂ)
    (hz : z.1 ∈ W') :
    ((polyHom z (coeffPoly hW' d c hc hz) : holGerms z) : Germ (𝓝 z) ℂ) =
      ((fun p => ∑ m ∈ Finset.range (d + 1), c m p.1 * p.2 ^ m : (Fin k → ℂ) × ℂ → ℂ) :
        Germ (𝓝 z) ℂ) :=
  coe_polyHom_sum z _ _ (coe_polyHom_X z) _ c _ (fun m => m)

/-- The function `(z', w) ↦ ∑_{m ≤ d} cₘ(z') wᵐ` is analytic at `z` when `z' ∈ W'`. -/
lemma analyticAt_polyFun {W' : Set (Fin k → ℂ)} (hW' : IsOpen W') (d : ℕ)
    (c : ℕ → (Fin k → ℂ) → ℂ) (hc : ∀ m, DifferentiableOn ℂ (c m) W') (z : (Fin k → ℂ) × ℂ)
    (hz : z.1 ∈ W') :
    AnalyticAt ℂ (fun p : (Fin k → ℂ) × ℂ => ∑ m ∈ Finset.range (d + 1), c m p.1 * p.2 ^ m) z := by
  refine Finset.analyticAt_fun_sum _ fun m _ => ?_
  exact ((analyticOnNhd_of_differentiableOn' hW' (hc m) z.1 hz).comp analyticAt_fst).mul
    (analyticAt_snd.pow _)

/-- **Polynomial relations generate the relations at `z`.** -/
theorem polyRelations_span_at {p d d0 : ℕ} {W' : Set (Fin k → ℂ)} (hW' : IsOpen W')
    (c : Fin p → ℕ → (Fin k → ℂ) → ℂ) (hc : ∀ i m, DifferentiableOn ℂ (c i m) W')
    (hcd : ∀ i m, d < m → c i m = 0) (i0 : Fin p) (hd0 : d0 ≤ d)
    (hm1 : c i0 d0 = fun _ => 1) (hm0 : ∀ m, d0 < m → c i0 m = 0)
    (z : (Fin k → ℂ) × ℂ) (hz : z.1 ∈ W') (a : Fin p → holGerms z)
    (ha : ∑ i, a i * polyHom z (coeffPoly hW' d (c i) (hc i) hz) = 0) :
    a ∈ Submodule.span (holGerms z) {b | ∃ π : Fin p → (holGerms z.1)[X],
      (∀ i, (π i).natDegree ≤ 3 * d) ∧ ∑ i, π i * coeffPoly hW' d (c i) (hc i) hz = 0 ∧
        b = fun i => polyHom z (π i)} := by
  set G := fun i => coeffPoly hW' d (c i) (hc i) hz with hG
  have hGd : ∀ i, (G i).natDegree ≤ d := fun i => natDegree_coeffPoly_le hW' d _ _ hz
  have hGm : (G i0).Monic := by
    refine monic_of_natDegree_le_of_coeff_eq_one d0 ?_ ?_
    · refine natDegree_le_iff_coeff_eq_zero.2 fun m hm => ?_
      rw [coeff_coeffPoly hW' d _ _ (hcd i0) hz m]
      exact germOn_eq_zero hW' _ hz (hm0 m (by exact_mod_cast hm))
    · rw [coeff_coeffPoly hW' d _ _ (hcd i0) hz d0]
      exact holGerms_ext (by rw [coe_hgerm, hm1]; rfl)
  set Pf : (Fin k → ℂ) × ℂ → ℂ := fun p => ∑ m ∈ Finset.range (d + 1), c i0 m p.1 * p.2 ^ m
    with hPf
  have hcoe : ((polyHom z (G i0) : holGerms z) : Germ (𝓝 z) ℂ) = Pf :=
    coe_polyHom_coeffPoly hW' d _ _ z hz
  have hPan : AnalyticAt ℂ Pf z := analyticAt_polyFun hW' d _ (hc i0) z hz
  by_cases h0 : Pf z = 0
  · -- Weierstrass preparation at `z`
    have hPan' : AnalyticAt ℂ (fun t : ℂ => Pf (z.1, z.2 + t)) 0 :=
      hPan.comp_of_eq (analyticAt_const.prod (analyticAt_const.add analyticAt_id)) (by simp)
    have htop : analyticOrderAt (fun t : ℂ => Pf (z.1, z.2 + t)) 0 ≠ ⊤ := by
      intro htop
      have h1 := analyticOrderAt_eq_top.1 htop
      have htz : Tendsto (fun w => w - z.2) (𝓝 z.2) (𝓝 0) :=
        (continuous_sub_right z.2).tendsto' z.2 0 (sub_self z.2)
      have h2 : ∀ᶠ w in 𝓝 z.2,
          (∑ m ∈ Finset.range (d + 1), C (c i0 m z.1) * Polynomial.X ^ m).eval w = 0 := by
        filter_upwards [htz.eventually h1] with w hw
        simpa [Pf, eval_finset_sum] using hw
      have h3 :=
        congrArg (fun P => P.coeff d0) (polynomial_eq_zero_of_eventually_eval_eq_zero h2)
      simp only [finset_sum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_range, coeff_zero] at h3
      rw [if_pos (by omega), hm1] at h3
      exact one_ne_zero h3
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 htop
    have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.2 fun h => by
      rw [h] at he
      rcases analyticOrderAt_eq_zero.1 he.symm with h' | h'
      · exact h' hPan'
      · exact h' (by simpa using h0)
    obtain ⟨u, bb, hu, hu0, hbb, hPu⟩ := weierstrassPreparation_at he1 hPan he.symm
    set Q := wPoly z bb (fun i => (hbb i).1)
    have hQm : Q.Monic := monic_wPoly _ _ _
    obtain ⟨hdiv, huniq⟩ := wPoly_div z he1 bb (fun i => (hbb i).1) (fun i => (hbb i).2)
    have key : polyHom z (G i0) =
        hgerm u (eventually_differentiableAt_of_analyticAt hu) * polyHom z Q := by
      apply holGerms_ext
      rw [Subring.coe_mul, hcoe, coe_hgerm, coe_polyHom_wPoly, ← Germ.coe_mul]
      exact Germ.coe_eq.2 hPu
    have hE := modByMonic_add_div (G i0) Q
    obtain ⟨h1, h2⟩ := huniq
      (polyHom z (G i0 /ₘ Q) - hgerm u (eventually_differentiableAt_of_analyticAt hu)) (G i0 %ₘ Q)
      (degree_modByMonic_lt _ hQm) (by
        have hE' := congrArg (polyHom z) hE
        rw [map_add, map_mul, key] at hE'
        linear_combination hE')
    have hPQ : G i0 = Q * (G i0 /ₘ Q) := by
      conv_lhs => rw [← hE, h2, zero_add]
    have hunit : IsUnit (polyHom z (G i0 /ₘ Q)) := by
      rw [sub_eq_zero.1 h1]
      exact isUnit_hgerm _ hu0
    exact mem_span_polyRelations_of_sum_mul_eq_zero (polyHom z) (polyHom_injective z) i0 G hGd hGm
      Q (G i0 /ₘ Q) hQm hPQ hunit hdiv huniq a ha
  · -- `P_{i₀}` is a unit at `z`
    have hunit : IsUnit (polyHom z (G i0)) := by
      rw [show polyHom z (G i0) = hgerm Pf (eventually_differentiableAt_of_analyticAt hPan) from
        holGerms_ext hcoe]
      exact isUnit_hgerm _ h0
    refine mem_span_polyRelations_of_sum_mul_eq_zero (polyHom z) (polyHom_injective z) i0 G hGd hGm
      1 (G i0) monic_one
      (one_mul _).symm hunit (fun g => ⟨g, 0, ?_, by simp⟩) (fun h r hr hh => ?_) a ha
    · rw [degree_zero, degree_one]
      exact WithBot.bot_lt_coe 0
    · rw [degree_one] at hr
      obtain rfl : r = 0 := degree_eq_bot.1 (Nat.WithBot.lt_zero_iff.1 hr)
      simp only [map_one, mul_one, map_zero, add_zero] at hh
      exact ⟨hh, rfl⟩

end PolyRel

section FiniteGeneration

/-- The coefficients of `∑ᵢ (∑ⱼ Aᵢⱼ Xʲ) Bᵢ`. -/
lemma coeff_sum_mul {R0 : Type} [CommRing R0] {p N d : ℕ} (A : Fin p → Fin N → R0)
    (B : Fin p → ℕ → R0) (k : ℕ) :
    (∑ i, (∑ j : Fin N, C (A i j) * Polynomial.X ^ (j : ℕ)) *
        (∑ m ∈ Finset.range (d + 1), C (B i m) * Polynomial.X ^ m)).coeff k =
      ∑ i, ∑ j : Fin N, A i j * (if (j : ℕ) ≤ k then
        (∑ m ∈ Finset.range (d + 1), C (B i m) * Polynomial.X ^ m).coeff (k - j) else 0) := by
  rw [finset_sum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, finset_sum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']

/-- If `Bₘ = 0` for `m > d`, the `m`-th coefficient of `∑_{m ≤ d} Bₘ Xᵐ` is `Bₘ`. -/
lemma coeff_sum_C_mul_X_pow_range {R0 : Type} [CommRing R0] {d : ℕ} (B : ℕ → R0)
    (hB : ∀ m, d < m → B m = 0) (m : ℕ) :
    (∑ m ∈ Finset.range (d + 1), C (B m) * Polynomial.X ^ m).coeff m = B m := by
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [hB m (by omega)]

/-- A polynomial relation of degree `< 3d + 1` among polynomials of degree `≤ d` is a linear
relation among the coefficient vectors. -/
lemma sum_mul_eq_zero_iff {R0 : Type} [CommRing R0] {p d : ℕ}
    (A : Fin p → Fin (3 * d + 1) → R0) (B : Fin p → ℕ → R0) (hB : ∀ i m, d < m → B i m = 0) :
    (∑ i, (∑ j : Fin (3 * d + 1), C (A i j) * Polynomial.X ^ (j : ℕ)) *
        (∑ m ∈ Finset.range (d + 1), C (B i m) * Polynomial.X ^ m)) = 0 ↔
      ∀ kk : Fin (4 * d + 1), ∑ i, ∑ j : Fin (3 * d + 1),
        A i j * (if (j : ℕ) ≤ kk then B i (kk - j) else 0) = 0 := by
  have key : ∀ k, (∑ i, (∑ j : Fin (3 * d + 1), C (A i j) * Polynomial.X ^ (j : ℕ)) *
        (∑ m ∈ Finset.range (d + 1), C (B i m) * Polynomial.X ^ m)).coeff k =
      ∑ i, ∑ j : Fin (3 * d + 1), A i j * (if (j : ℕ) ≤ k then B i (k - j) else 0) := by
    intro k
    rw [coeff_sum_mul]
    simp only [coeff_sum_C_mul_X_pow_range _ (hB _)]
  constructor
  · intro h kk
    rw [← key, h, coeff_zero]
  · intro h
    refine Polynomial.ext fun k => ?_
    rw [key, coeff_zero]
    by_cases hk : k < 4 * d + 1
    · exact h ⟨k, hk⟩
    · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      have := j.2
      rw [if_pos (by omega), hB i _ (by omega), mul_zero]

variable {n : ℕ}

/-- **Finite generation of relations among Weierstrass polynomials.** -/
theorem polyRelations_generatedNear {p d d0 : ℕ}
    (ih : ∀ q, HolomorphicRelationsLocallyFinite (Fin n → ℂ) q)
    {W' : Set (Fin n → ℂ)} (hW' : IsOpen W') {x' : Fin n → ℂ} (hx' : x' ∈ W')
    (c : Fin p → ℕ → (Fin n → ℂ) → ℂ) (hc : ∀ i m, DifferentiableOn ℂ (c i m) W')
    (hcd : ∀ i m, d < m → c i m = 0) (i0 : Fin p) (hd0 : d0 ≤ d)
    (hm1 : c i0 d0 = fun _ => 1) (hm0 : ∀ m, d0 < m → c i0 m = 0) (w0 : ℂ) :
    HolomorphicRelationsGeneratedNear (W' ×ˢ Set.univ)
      (fun i (_ : Fin 1) (q : (Fin n → ℂ) × ℂ) => ∑ m ∈ Finset.range (d + 1), c i m q.1 * q.2 ^ m)
      (x', w0) := by
  classical
  set N := 3 * d + 1
  let eq : Fin (p * N) ≃ Fin p × Fin N := finProdFinEquiv.symm
  let F' : Fin (p * N) → Fin (4 * d + 1) → (Fin n → ℂ) → ℂ := fun ij kk =>
    if ((eq ij).2 : ℕ) ≤ kk then c (eq ij).1 (kk - (eq ij).2) else 0
  have hF' : ∀ ij kk, DifferentiableOn ℂ (F' ij kk) W' := fun ij kk => by
    simp only [F']
    split_ifs
    · exact hc _ _
    · exact differentiableOn_const _
  obtain ⟨W'', hW''o, hW''W', hx'', s, ρ, hρd, hρ, hgen⟩ :=
    ih (4 * d + 1) W' hW' (p * N) F' hF' x' hx'
  set P : Fin p → Fin 1 → (Fin n → ℂ) × ℂ → ℂ :=
    fun i _ q => ∑ m ∈ Finset.range (d + 1), c i m q.1 * q.2 ^ m
  let R : Fin s → Fin p → (Fin n → ℂ) × ℂ → ℂ := fun l i q =>
    ∑ j : Fin N, ρ l (eq.symm (i, j)) q.1 * q.2 ^ (j : ℕ)
  have hW : IsOpen (W'' ×ˢ (Set.univ : Set ℂ)) := hW''o.prod isOpen_univ
  have hPd : ∀ i j, DifferentiableOn ℂ (P i j) (W'' ×ˢ Set.univ) := fun i j => by
    refine DifferentiableOn.fun_sum fun m _ => ?_
    exact (((hc i m).mono hW''W').comp differentiableOn_fst (fun q hq => hq.1)).mul
      (differentiableOn_snd.pow _)
  have hRd : ∀ l i, DifferentiableOn ℂ (R l i) (W'' ×ˢ Set.univ) := fun l i => by
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact ((hρd l _).comp differentiableOn_fst (fun q hq => hq.1)).mul
      (differentiableOn_snd.pow _)
  have hsum : ∀ {M : Type} [AddCommMonoid M] (f : Fin (p * N) → M),
      ∑ ij, f ij = ∑ i, ∑ j : Fin N, f (eq.symm (i, j)) := by
    intro M _ f
    rw [← Fintype.sum_prod_type', ← Equiv.sum_comp eq.symm]
  refine generatedNear_of_germ hW (Set.prod_mono hW''W' subset_rfl) ⟨hx'', trivial⟩ hPd R hRd
    (fun l j q hq => ?_) (fun y hy a ha => ?_)
  · -- the generators are relations
    have hrel := hρ l
    have hpoly : (∑ i, (∑ jj : Fin N, C (ρ l (eq.symm (i, jj)) q.1) * Polynomial.X ^ (jj : ℕ)) *
        (∑ m ∈ Finset.range (d + 1), C (c i m q.1) * Polynomial.X ^ m)) = 0 := by
      refine (sum_mul_eq_zero_iff _ (fun i m => c i m q.1) (fun i m hm => by
        rw [hcd i m hm]; rfl)).2 fun kk => ?_
      have := hrel kk q.1 hq.1
      rw [hsum] at this
      simp only [F', Equiv.apply_symm_apply] at this
      refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_) this
      split_ifs <;> simp
    have := congrArg (Polynomial.eval q.2) hpoly
    simpa [eval_finset_sum, R, P] using this
  · -- germs of relations are spanned by the germs of the generators
    have hy1 : y.1 ∈ W' := hW''W' hy.1
    have hGP : ∀ i, germOn hW (hPd i 0) hy = polyHom y (coeffPoly hW' d (c i) (hc i) hy1) :=
      fun i => holGerms_ext (coe_polyHom_coeffPoly hW' d _ _ y hy1).symm
    have ha' : ∑ i, a i * polyHom y (coeffPoly hW' d (c i) (hc i) hy1) = 0 := by
      simpa [hGP] using ha 0
    refine Submodule.span_le.2 ?_ (polyRelations_span_at hW' c hc hcd i0 hd0 hm1 hm0 y hy1 a ha')
    rintro b ⟨π, hπd, hπrel, rfl⟩
    let v : Fin (p * N) → holGerms y.1 := fun ij => (π (eq ij).1).coeff (eq ij).2
    have hπsum : ∀ i, π i = ∑ jj : Fin N, C ((π i).coeff jj) * Polynomial.X ^ (jj : ℕ) := by
      intro i
      conv_lhs => rw [as_sum_range' (π i) N (by have := hπd i; omega)]
      rw [Finset.sum_range]
      simp only [C_mul_X_pow_eq_monomial]
    have hv : ∀ kk, ∑ ij, v ij * germOn hW''o ((hF' ij kk).mono hW''W') hy.1 = 0 := by
      intro kk
      have h1 := (sum_mul_eq_zero_iff (fun i jj => (π i).coeff jj)
        (fun i m => germOn hW' (hc i m) hy1) (fun i m hm =>
          germOn_eq_zero hW' _ hy1 (hcd i m hm))).1 (by
        rw [← hπrel]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hπsum i]
        rfl) kk
      rw [hsum]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun jj _ => ?_) h1
      simp only [v, Equiv.apply_symm_apply]
      congr 1
      apply holGerms_ext
      simp only [F', Equiv.apply_symm_apply, coe_hgerm]
      split_ifs <;> rfl
    have hvs :=
      mem_span_germOn_of_generatedNear hW''o (fun ij kk => (hF' ij kk).mono hW''W') hρd hgen hy.1
        v hv
    obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hvs
    have hvij : ∀ ij, v ij = ∑ l, lam l * germOn hW''o (hρd l ij) hy.1 := by
      intro ij
      have := congrFun hlam ij
      simpa [Finset.sum_apply] using this.symm
    have hRgerm : ∀ l i, germOn hW (hRd l i) hy = polyHom y (∑ jj : Fin N,
        C (germOn hW''o (hρd l (eq.symm (i, jj))) hy.1) * Polynomial.X ^ (jj : ℕ)) :=
      fun l i => holGerms_ext (coe_polyHom_sum y _ _ (coe_polyHom_X y) _
        (fun jj : Fin N => ρ l (eq.symm (i, jj))) _ (fun jj => (jj : ℕ))).symm
    have hb : (fun i => polyHom y (π i)) =
        ∑ l, fstHom y (lam l) • fun i => germOn hW (hRd l i) hy := by
      funext i
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, hRgerm]
      rw [hπsum i]
      simp only [map_sum, map_mul, map_pow, polyHom, Polynomial.coe_eval₂RingHom, eval₂_C,
        eval₂_X, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun jj _ => ?_
      have := hvij (eq.symm (i, jj))
      simp only [v, Equiv.apply_symm_apply] at this
      rw [this, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul]; ring
    rw [SetLike.mem_coe, hb]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨l, rfl⟩)

end FiniteGeneration

section Reductions

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E']

/-- Local generation of relations is invariant under biholomorphic changes of variables. -/
theorem generatedNear_of_comp (Φ : E' → E) (Ψ : E → E') (hΦ : Differentiable ℂ Φ)
    (hΨ : Differentiable ℂ Ψ) (hΦΨ : ∀ y, Φ (Ψ y) = y) (hΨΦ : ∀ z, Ψ (Φ z) = z) {V : Set E}
    {p q : ℕ} {F : Fin p → Fin q → E → ℂ} {x : E}
    (h : HolomorphicRelationsGeneratedNear (Φ ⁻¹' V) (fun i j z => F i j (Φ z)) (Ψ x)) :
    HolomorphicRelationsGeneratedNear V F x := by
  obtain ⟨W, hWo, hWV, hxW, s, r, hrd, hr, hgen⟩ := h
  refine ⟨Ψ ⁻¹' W, hWo.preimage hΨ.continuous, fun y hy => by simpa [hΦΨ] using hWV hy, hxW, s,
    fun k i y => r k i (Ψ y), fun k i => (hrd k i).comp hΨ.differentiableOn (fun _ h => h),
    fun k j y hy => by simpa [hΦΨ] using hr k j _ hy, fun U hU hUW a ha har y hy => ?_⟩
  obtain ⟨U', hU'o, hU'U, hyU', c, hcd, hc⟩ := hgen (Φ ⁻¹' U) (hU.preimage hΦ.continuous)
    (fun z hz => by simpa [hΨΦ] using hUW hz) (fun i z => a i (Φ z))
    (fun i => (ha i).comp hΦ.differentiableOn (fun _ h => h))
    (fun j z hz => har j _ hz) (Ψ y) (by simpa [hΦΨ] using hy)
  refine ⟨Ψ ⁻¹' U', hU'o.preimage hΨ.continuous, fun z hz => by simpa [hΦΨ] using hU'U hz,
    hyU', fun k z => c k (Ψ z), fun k => (hcd k).comp hΨ.differentiableOn (fun _ h => h),
    fun i z hz => ?_⟩
  simpa [hΦΨ] using hc i _ hz

/-- Local generation of relations among functions is invariant under multiplication by units. -/
theorem generatedNear_of_eq_mul {V Vg N : Set E} (hN : IsOpen N) (hNV : N ⊆ V) {x : E}
    (hx : x ∈ N) {p : ℕ} {F G : Fin p → Fin 1 → E → ℂ} {u : Fin p → E → ℂ}
    (hud : ∀ i, DifferentiableOn ℂ (u i) N) (hu0 : ∀ i, ∀ z ∈ N, u i z ≠ 0)
    (hFG : ∀ i, ∀ z ∈ N, F i 0 z = u i z * G i 0 z)
    (hG : HolomorphicRelationsGeneratedNear Vg G x) : HolomorphicRelationsGeneratedNear V F x := by
  obtain ⟨W, hWo, -, hxW, s, r, hrd, hr, hgen⟩ := hG
  refine ⟨W ∩ N, hWo.inter hN, Set.inter_subset_right.trans hNV, ⟨hxW, hx⟩, s,
    fun k i z => r k i z * (u i z)⁻¹, fun k i => ((hrd k i).mono Set.inter_subset_left).mul
      (((hud i).mono Set.inter_subset_right).inv fun z hz => hu0 i z hz.2),
    fun k j z hz => ?_, fun U hU hUW a ha har y hy => ?_⟩
  · rw [Subsingleton.elim j 0, ← hr k 0 z hz.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFG i z hz.2]
    field_simp [hu0 i z hz.2]
  · obtain ⟨U', hU'o, hU'U, hyU', c, hcd, hc⟩ := hgen U hU (hUW.trans Set.inter_subset_left)
      (fun i z => a i z * u i z) (fun i => (ha i).mul ((hud i).mono
        (hUW.trans Set.inter_subset_right)))
      (fun j z hz => by
        rw [Subsingleton.elim j 0, ← har 0 z hz]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hFG i z (hUW hz).2]; ring) y hy
    refine ⟨U', hU'o, hU'U, hyU', c, hcd, fun i z hz => ?_⟩
    have h1 := hc i z hz
    have hu := hu0 i z (hUW (hU'U hz)).2
    simp only [← mul_assoc, ← Finset.sum_mul, ← h1]
    field_simp

/-- Relations among functions vanishing near `x` are generated by the unit vectors. -/
theorem generatedNear_of_eventually_zero {V : Set E} (hV : IsOpen V) {x : E} (hx : x ∈ V)
    {p : ℕ} {F : Fin p → Fin 1 → E → ℂ} (h0 : ∀ i, ∀ᶠ y in 𝓝 x, F i 0 y = 0) :
    HolomorphicRelationsGeneratedNear V F x := by
  classical
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.1
    ((Filter.eventually_all.2 h0).and (hV.mem_nhds hx))
  refine ⟨W, hWo, fun y hy => (hW y hy).2, hxW, p, fun k i _ => if k = i then 1 else 0,
    fun k i => differentiableOn_const _, fun k j z hz => ?_,
    fun U hU _ a ha _ y hy => ⟨U, hU, subset_rfl, hy, a, ha, fun i z _ => by simp⟩⟩
  rw [Subsingleton.elim j 0]
  simp [(hW z hz).1 k]

end Reductions

end Weierstrass

end MMP.Analytic.OkaCoherence
