module

public import MMP.Analysis.Complex.Dolbeault.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Geometry.Manifold.Sheaf.Smooth

/-!
# Smooth forms on an open subset of `ℂⁿ` as a retract of smooth functions

Let `D ⊆ ℂⁿ` be open. The restriction to `D` of the sheaf `ℰ^{0,q}` of smooth `(0, q)`-forms is a
finite direct sum of copies of the sheaf `C^∞_D` of smooth complex functions on the manifold `D`:
a form is the family of its coefficients `ω_I`, `|I| = q`. We record this as maps
`π_I : ℰ^{0,q}|_D ⟶ C^∞_D` (the coefficient of `dz̄_I`) and `ι_I : C^∞_D ⟶ ℰ^{0,q}|_D` (the form
`f dz̄_I`) with `∑_I π_I ≫ ι_I = 𝟙`. Every functor additive in the sheaf, such as `Ext^n(P, -)`,
that kills `C^∞_D` therefore kills `ℰ^{0,q}|_D`; this is how the acyclicity of smooth functions
passes to smooth forms.

The restriction is the naive inverse image `IsOpenEmbedding.sheafPullback` along the inclusion
`D → ℂⁿ`, whose sections over `W ⊆ D` are the sections over the image of `W`.

## Main definitions

* `MMP.Analytic.smoothSheafAb`: the sheaf of abelian groups of smooth complex functions on `D`.
* `MMP.Analytic.dolbeaultCoeff`: `π_I`, the coefficient of `dz̄_I`.
* `MMP.Analytic.dolbeaultOfCoeff`: `ι_I`, the form `f dz̄_I`.

## Main results

* `MMP.Analytic.sum_dolbeaultCoeff_comp_dolbeaultOfCoeff`: `∑_I π_I ≫ ι_I = 𝟙`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open scoped Manifold ContDiff

namespace MMP.Analytic

variable {n : ℕ}

section Bridge

variable {D : Opens (EuclideanSpace ℂ (Fin n))}

/-- A function on an open subset `W` of the manifold `D ⊆ ℂⁿ` which is the restriction of
`g : ℂⁿ → ℂ` is smooth at `w` iff `g` is real `C^m` at `w`. -/
lemma contMDiffAt_restrict_iff {m : WithTop ℕ∞} (g : EuclideanSpace ℂ (Fin n) → ℂ)
    {W : Opens D} (w : W) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℂ) m
        (fun x : W => g ((x : D) : EuclideanSpace ℂ (Fin n))) w ↔
      ContDiffAt ℝ m g ((w : D) : EuclideanSpace ℂ (Fin n)) := by
  rw [contMDiffAt_subtype_iff (f := fun x : D => g x), contMDiffAt_subtype_iff (f := g),
    contMDiffAt_iff_contDiffAt]

end Bridge

variable (D : Opens (TopCat.of (EuclideanSpace ℂ (Fin n))))

/-- The sheaf of abelian groups of smooth complex-valued functions on the open submanifold
`D ⊆ ℂⁿ`, the sheaf of abelian groups underlying the unit module over Mathlib's sheaf of smooth
functions. -/
noncomputable abbrev smoothSheafAb : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of D) :=
  (SheafOfModules.toSheaf _).obj (SheafOfModules.unit
    ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj
      (smoothSheafCommRing 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℂ) D ℂ)))

/-- The restriction `ℰ^{0,q}|_D` of smooth `(0, q)`-forms to the open set `D`. -/
noncomputable abbrev dolbeaultRestrictSheaf (q : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of D) :=
  (D.isOpenEmbedding.sheafPullback AddCommGrpCat.{0}).obj (dolbeaultSheaf n q)

variable {D}

/-- A point `z` of `ℂⁿ` lies in the image of `W ⊆ D` iff `z ∈ D` and the corresponding point of
`D` lies in `W`. -/
lemma mem_functor_obj_iff {W : Opens (TopCat.of D)} {z : EuclideanSpace ℂ (Fin n)} :
    z ∈ (D.isOpenEmbedding.isOpenMap.functor.obj W : Set (EuclideanSpace ℂ (Fin n))) ↔
      ∃ hz : z ∈ D, (⟨z, hz⟩ : D) ∈ W := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hz, hw⟩
    exact ⟨⟨z, hz⟩, hw, rfl⟩

/-- Every point of `W ⊆ D` lies, as a point of `ℂⁿ`, in the image of `W`. -/
lemma coe_mem_functor_obj {W : Opens (TopCat.of D)} (w : W) :
    ((w : D) : EuclideanSpace ℂ (Fin n)) ∈
      (D.isOpenEmbedding.isOpenMap.functor.obj W : Set (EuclideanSpace ℂ (Fin n))) :=
  mem_functor_obj_iff.2 ⟨(w : D).2, w.2⟩

section Coeff

/-- The coefficient of `dz̄_I` of a form over the image of `W`, as a smooth function on `W`. -/
noncomputable def dolbeaultCoeffSections (q : ℕ) (I : Finset (Fin n)) (W : Opens (TopCat.of D)) :
    (dolbeaultRestrictSheaf D q).obj.obj (op W) →+ (smoothSheafAb D).obj.obj (op W) where
  toFun s := ⟨fun w => s.1 I ((w : D) : EuclideanSpace ℂ (Fin n)), fun w =>
    (contMDiffAt_restrict_iff (s.1 I) w).2
      ((s.2.2.1 I).contDiffAt ((D.isOpenEmbedding.isOpenMap.functor.obj W).isOpen.mem_nhds
        (coe_mem_functor_obj w)))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable (D) in
/-- `π_I : ℰ^{0,q}|_D ⟶ C^∞_D`, the coefficient of `dz̄_I`. -/
noncomputable def dolbeaultCoeff (q : ℕ) (I : Finset (Fin n)) :
    dolbeaultRestrictSheaf D q ⟶ smoothSheafAb D :=
  ObjectProperty.homMk
    { app W := AddCommGrpCat.ofHom (dolbeaultCoeffSections q I W.unop)
      naturality {W W'} i := by
        ext s : 2
        exact Subtype.ext (funext fun w => Set.indicator_of_mem (coe_mem_functor_obj w) _) }

open Classical in
/-- A function on `W ⊆ D`, extended by zero to `ℂⁿ`. -/
noncomputable def extendFromOpen {W : Opens (TopCat.of D)} (f : W → ℂ) :
    EuclideanSpace ℂ (Fin n) → ℂ :=
  fun z => if h : ∃ hz : z ∈ D, (⟨z, hz⟩ : D) ∈ W then f ⟨⟨z, h.1⟩, h.2⟩ else 0

/-- The extension by zero of `f` agrees with `f` on `W`. -/
@[simp]
lemma extendFromOpen_coe {W : Opens (TopCat.of D)} (f : W → ℂ) (w : W) :
    extendFromOpen f ((w : D) : EuclideanSpace ℂ (Fin n)) = f w := by
  rw [extendFromOpen, dite_eq_left ⟨(w : D).2, w.2⟩]

/-- The extension by zero of `f` vanishes outside the image of `W`. -/
lemma extendFromOpen_of_notMem {W : Opens (TopCat.of D)} (f : W → ℂ)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∉ (D.isOpenEmbedding.isOpenMap.functor.obj W : Set (EuclideanSpace ℂ (Fin n)))) :
    extendFromOpen f z = 0 := by
  rw [extendFromOpen, dite_eq_right (fun h => hz (mem_functor_obj_iff.2 h))]

/-- The extension by zero of a smooth function on `W` is smooth on the image of `W` in `ℂⁿ`. -/
lemma contDiffOn_extendFromOpen {W : Opens (TopCat.of D)} (f : (smoothSheafAb D).obj.obj (op W)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (extendFromOpen f.1)
      (D.isOpenEmbedding.isOpenMap.functor.obj W : Set (EuclideanSpace ℂ (Fin n))) := by
  intro z hz
  obtain ⟨hzD, hzW⟩ := mem_functor_obj_iff.1 hz
  refine ((contMDiffAt_restrict_iff _ (⟨⟨z, hzD⟩, hzW⟩ : W)).1 ?_).contDiffWithinAt
  rw [funext (extendFromOpen_coe f.1)]
  exact smoothSheaf.contMDiff_section (IM := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (I := 𝓘(ℝ, ℂ))
    (N := ℂ) f _

open Classical in
/-- The form `f dz̄_I` over the image of `W`, for `|I| = q` (and `0` otherwise). -/
noncomputable def dolbeaultOfCoeffForm (q : ℕ) (I : Finset (Fin n)) {W : Opens (TopCat.of D)}
    (f : (smoothSheafAb D).obj.obj (op W)) : (dolbeaultRestrictSheaf D q).obj.obj (op W) :=
  ⟨fun J => if J = I ∧ J.card = q then extendFromOpen f.1 else 0,
    ⟨fun J hJ => by simp [hJ], fun J => by
      beta_reduce
      split_ifs
      · exact contDiffOn_extendFromOpen f
      · exact contDiffOn_const,
    fun J z hz => by
      change (if J = I ∧ J.card = q then extendFromOpen f.1 else 0) z = 0
      split_ifs
      · exact extendFromOpen_of_notMem _ hz
      · rfl⟩⟩

/-- The `dz̄_J`-coefficient of the form `f dz̄_I` is the extension by zero of `f` if `J = I` and
`|J| = q`, and `0` otherwise. -/
lemma dolbeaultOfCoeffForm_apply (q : ℕ) (I : Finset (Fin n)) {W : Opens (TopCat.of D)}
    (f : (smoothSheafAb D).obj.obj (op W)) (J : Finset (Fin n)) :
    ((dolbeaultOfCoeffForm q I f).1 J : EuclideanSpace ℂ (Fin n) → ℂ) =
      open Classical in if J = I ∧ J.card = q then extendFromOpen f.1 else 0 := rfl

/-- The form `f dz̄_I`, as an additive map. -/
noncomputable def dolbeaultOfCoeffSections (q : ℕ) (I : Finset (Fin n)) (W : Opens (TopCat.of D)) :
    (smoothSheafAb D).obj.obj (op W) →+ (dolbeaultRestrictSheaf D q).obj.obj (op W) where
  toFun f := dolbeaultOfCoeffForm q I f
  map_zero' := by
    apply Subtype.ext
    funext J z
    change (dolbeaultOfCoeffForm q I 0).1 J z = 0
    rw [dolbeaultOfCoeffForm_apply]
    split_ifs
    · simp only [extendFromOpen]
      split_ifs <;> rfl
    · rfl
  map_add' a b := by
    apply Subtype.ext
    funext J z
    change (dolbeaultOfCoeffForm q I (a + b)).1 J z =
      (dolbeaultOfCoeffForm q I a).1 J z + (dolbeaultOfCoeffForm q I b).1 J z
    rw [dolbeaultOfCoeffForm_apply, dolbeaultOfCoeffForm_apply, dolbeaultOfCoeffForm_apply]
    split_ifs
    · simp only [extendFromOpen]
      split_ifs
      · rfl
      · simp
    · simp

/-- `dolbeaultOfCoeffSections` evaluates as `dolbeaultOfCoeffForm`: the `dz̄_J`-coefficient of
`f dz̄_I` is the extension by zero of `f` if `J = I` and `|J| = q`, and `0` otherwise. -/
lemma dolbeaultOfCoeffSections_apply (q : ℕ) (I : Finset (Fin n)) (W : Opens (TopCat.of D))
    (f : (smoothSheafAb D).obj.obj (op W)) (J : Finset (Fin n)) :
    ((dolbeaultOfCoeffSections q I W f).1 J : EuclideanSpace ℂ (Fin n) → ℂ) =
      open Classical in if J = I ∧ J.card = q then extendFromOpen f.1 else 0 := rfl

variable (D) in
/-- `ι_I : C^∞_D ⟶ ℰ^{0,q}|_D`, the form `f dz̄_I`. -/
noncomputable def dolbeaultOfCoeff (q : ℕ) (I : Finset (Fin n)) :
    smoothSheafAb D ⟶ dolbeaultRestrictSheaf D q :=
  ObjectProperty.homMk
    { app W := AddCommGrpCat.ofHom (dolbeaultOfCoeffSections q I W.unop)
      naturality {W W'} i := by
        ext f : 2
        apply Subtype.ext
        funext J z
        change (dolbeaultOfCoeffSections q I W'.unop _).1 J z =
          ((D.isOpenEmbedding.isOpenMap.functor.obj W'.unop : Opens _) : Set _).indicator
            ((dolbeaultOfCoeffSections q I W.unop f).1 J) z
        rw [dolbeaultOfCoeffSections_apply, dolbeaultOfCoeffSections_apply]
        by_cases hz : z ∈ ((D.isOpenEmbedding.isOpenMap.functor.obj W'.unop : Opens _) : Set _)
        · rw [Set.indicator_of_mem hz]
          split_ifs
          · obtain ⟨hzD, hzW⟩ := mem_functor_obj_iff.1 hz
            let w : W'.unop := ⟨⟨z, hzD⟩, hzW⟩
            change extendFromOpen _ ((w : D) : EuclideanSpace ℂ (Fin n)) =
              extendFromOpen f.1 ((w : D) : EuclideanSpace ℂ (Fin n))
            rw [extendFromOpen_coe, extendFromOpen, dite_eq_left ⟨hzD, i.unop.le hzW⟩]
            rfl
          · rfl
        · rw [Set.indicator_of_notMem hz]
          split_ifs
          · exact extendFromOpen_of_notMem _ hz
          · rfl }

end Coeff

variable (D) in
/-- **`ℰ^{0,q}|_D` is a retract of a sum of copies of `C^∞_D`**: `∑_I π_I ≫ ι_I = 𝟙`. -/
theorem sum_dolbeaultCoeff_comp_dolbeaultOfCoeff (q : ℕ) :
    ∑ I : Finset (Fin n), dolbeaultCoeff D q I ≫ dolbeaultOfCoeff D q I =
      𝟙 (dolbeaultRestrictSheaf D q) := by
  refine InducedCategory.hom_ext (NatTrans.ext (funext fun W => AddCommGrpCat.ext fun s => ?_))
  apply Subtype.ext
  funext J z
  have hsum : ∀ F : Finset (Finset (Fin n)),
      ((∑ I ∈ F, dolbeaultCoeff D q I ≫ dolbeaultOfCoeff D q I).hom.app W s).1 J z =
        ∑ I ∈ F, ((dolbeaultCoeff D q I ≫ dolbeaultOfCoeff D q I).hom.app W s).1 J z := by
    intro F
    induction F using Finset.induction_on with
    | empty => rfl
    | insert a F ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      rfl
  have hext : extendFromOpen (dolbeaultCoeffSections q J W.unop s).1 z = s.1 J z := by
    by_cases hz : z ∈ ((D.isOpenEmbedding.isOpenMap.functor.obj W.unop : Opens _) : Set _)
    · obtain ⟨hzD, hzW⟩ := mem_functor_obj_iff.1 hz
      exact extendFromOpen_coe _ (⟨⟨z, hzD⟩, hzW⟩ : W.unop)
    · rw [extendFromOpen_of_notMem _ hz, s.2.2.2 J z hz]
  have hterm : ∀ I, ((dolbeaultCoeff D q I ≫ dolbeaultOfCoeff D q I).hom.app W s).1 J z =
      open Classical in if I = J ∧ J.card = q then s.1 J z else 0 := by
    intro I
    change (dolbeaultOfCoeffForm q I (dolbeaultCoeffSections q I W.unop s)).1 J z = _
    rw [dolbeaultOfCoeffForm_apply]
    by_cases h : I = J ∧ J.card = q
    · obtain ⟨rfl, hc⟩ := h
      rw [ite_eq_left ⟨rfl, hc⟩, ite_eq_left ⟨rfl, hc⟩, hext]
    · rw [ite_eq_right (fun h' => h ⟨h'.1.symm, h'.2⟩), ite_eq_right h]
      rfl
  rw [hsum, Finset.sum_congr rfl fun I _ => hterm I]
  change _ = s.1 J z
  classical
  by_cases hc : J.card = q
  · simp [hc]
  · simp [hc, s.2.1 J hc]

end MMP.Analytic
