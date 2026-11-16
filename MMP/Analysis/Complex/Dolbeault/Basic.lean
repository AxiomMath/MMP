module

public import MMP.Analysis.Complex.Wirtinger
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The Dolbeault operator on `(0, q)`-forms on `ℂⁿ`

A `(0, q)`-form on an open set of `ℂⁿ` is `ω = ∑_{|I| = q} ω_I dz̄_I`, where `I` runs over the
`q`-element subsets of `{0, …, n - 1}` and `dz̄_I = dz̄_{i₁} ∧ ⋯ ∧ dz̄_{i_q}` for
`i₁ < ⋯ < i_q`. We record a form of every degree at once by its family of coefficients
`ω : Finset (Fin n) → ℂⁿ → ℂ`; it has degree `q` when `ω_I = 0` for `|I| ≠ q`. The Dolbeault
operator is
`(∂̄ω)_I = ∑_{j ∈ I} (-1)^{#{i ∈ I | i < j}} ∂ω_{I ∖ j}/∂z̄ⱼ`,
and `∂̄ ∘ ∂̄ = 0` on forms with `C²` coefficients, because Wirtinger derivatives commute and
the two orders of removing `j ≠ k` from `I` carry opposite signs.

## Main definitions

* `MMP.Analytic.dolbeaultSign`: the sign `(-1)^{#{i ∈ I | i < j}}`.
* `MMP.Analytic.dbarForm`: the Dolbeault operator on coefficient families.
* `MMP.Analytic.dolbeaultSheaf`: the sheaf `ℰ^{0,q}` of smooth `(0, q)`-forms on `ℂⁿ`.
* `MMP.Analytic.dbarHom`: `∂̄ : ℰ^{0,q} ⟶ ℰ^{0,q+1}` as a morphism of sheaves.
* `MMP.Analytic.dolbeaultComplex`: the Dolbeault complex `ℰ^{0,0} ⟶ ℰ^{0,1} ⟶ ⋯`.

## Main results

* `MMP.Analytic.dbarForm_dbarForm`: `∂̄ ∘ ∂̄ = 0` at every point of an open set on which the
  coefficients are `C²`.
* `MMP.Analytic.contDiffOn_dbarForm`: `∂̄` maps `C^{m+1}` coefficients to `C^m` coefficients.
* `MMP.Analytic.dbarForm_of_degree`: `∂̄` raises the degree by one.
* `MMP.Analytic.isSheaf_dolbeaultPresheaf`: smooth forms glue.

## Implementation notes

A section of `ℰ^{0,q}` over an open `U` is a family of coefficients `ω_I : ℂⁿ → ℂ`, smooth on `U`,
vanishing off `U` and vanishing unless `|I| = q`; restriction to `V ⊆ U` multiplies by the
indicator of `V`. Extending by zero makes sections functions on all of `ℂⁿ`, so that the
derivatives of Mathlib's calculus on normed spaces apply directly.
-/

@[expose] public section

open Complex Filter Topology CategoryTheory TopologicalSpace Opposite

namespace MMP.Analytic

variable {n : ℕ}

section WirtingerAlgebra

/-- The Wirtinger derivative at `z` only depends on the germ at `z`. -/
lemma dbarPartial_congr {j : Fin n} {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (h : f =ᶠ[𝓝 z] g) : dbarPartial j f z = dbarPartial j g z := by
  simp only [dbarPartial, h.fderiv_eq]

/-- The Wirtinger derivative `∂/∂z̄ⱼ` is additive on functions differentiable at the point. -/
lemma dbarPartial_add {j : Fin n} {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbarPartial j (fun w => f w + g w) z = dbarPartial j f z + dbarPartial j g z := by
  simp only [dbarPartial, fderiv_fun_add hf hg]
  simp
  ring

/-- The Wirtinger derivative `∂/∂z̄ⱼ` commutes with multiplication by a complex constant. -/
lemma dbarPartial_const_mul {j : Fin n} (c : ℂ) {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f z) :
    dbarPartial j (fun w => c * f w) z = c * dbarPartial j f z := by
  simp only [dbarPartial, fderiv_const_mul hf]
  simp
  ring

/-- The Wirtinger derivative `∂/∂z̄ⱼ` of a finite sum of differentiable functions is the sum of
their Wirtinger derivatives. -/
lemma dbarPartial_sum {ι : Type*} (s : Finset ι) {j : Fin n}
    {f : ι → EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    dbarPartial j (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, dbarPartial j (f i) z := by
  simp only [dbarPartial]
  rw [fderiv_fun_sum hf]
  simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add]

/-- A Wirtinger derivative of a `C^{m+1}` function on an open set is `C^m` there. -/
lemma contDiffOn_dbarPartial {j : Fin n} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) {m : WithTop ℕ∞}
    (hf : ContDiffOn ℝ (m + 1) f U) : ContDiffOn ℝ m (dbarPartial j f) U := by
  have hd : ContDiffOn ℝ m (fderiv ℝ f) U := hf.fderiv_of_isOpen hU le_rfl
  unfold dbarPartial
  exact contDiffOn_const.mul ((hd.clm_apply contDiffOn_const).add
    (contDiffOn_const.mul (hd.clm_apply contDiffOn_const)))

end WirtingerAlgebra

section Sign

/-- The sign `(-1)^{#{i ∈ I | i < j}}` of moving `dz̄ⱼ` into place in `dz̄_I`. -/
def dolbeaultSign (j : Fin n) (I : Finset (Fin n)) : ℂ := (-1) ^ (I.filter (· < j)).card

/-- For `j ∈ I` with `j < k`, removing `j` from `I` lowers `#{i ∈ I | i < k}` by one. -/
lemma card_filter_lt_erase_of_lt {j k : Fin n} {I : Finset (Fin n)} (hj : j ∈ I) (hjk : j < k) :
    ((I.erase j).filter (· < k)).card + 1 = (I.filter (· < k)).card := by
  rw [Finset.filter_erase, Finset.card_erase_add_one (Finset.mem_filter.2 ⟨hj, hjk⟩)]

/-- The two orders of removing `j ≠ k` from `I` carry opposite signs. -/
lemma dolbeaultSign_mul_dolbeaultSign_swap {j k : Fin n} {I : Finset (Fin n)} (hj : j ∈ I)
    (hk : k ∈ I) (hjk : j ≠ k) :
    dolbeaultSign j (I.erase j) * dolbeaultSign k ((I.erase j).erase k) =
      -(dolbeaultSign k (I.erase k) * dolbeaultSign j ((I.erase k).erase j)) := by
  have e : ∀ (s : Finset (Fin n)) (a : Fin n), (s.erase a).filter (· < a) = s.filter (· < a) :=
    fun s a => by
      rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
      simp
  have key : ∀ {j k : Fin n}, j ∈ I → k ∈ I → j < k →
      dolbeaultSign j (I.erase j) * dolbeaultSign k ((I.erase j).erase k) =
        -(dolbeaultSign k (I.erase k) * dolbeaultSign j ((I.erase k).erase j)) := by
    intro j k hj hk hjk
    unfold dolbeaultSign
    have e4 : ((I.erase k).erase j).filter (· < j) = I.filter (· < j) := by
      rw [Finset.erase_right_comm, Finset.filter_erase,
        Finset.erase_eq_of_notMem (by simp [hjk.le]), e I j]
    rw [e I j, e (I.erase j) k, e I k, e4, ← card_filter_lt_erase_of_lt hj hjk, pow_succ]
    ring
  rcases lt_or_gt_of_ne hjk with h | h
  · exact key hj hk h
  · rw [key hk hj h, neg_neg]

end Sign

section Forms

/-- The Dolbeault operator on families of coefficients `ω : Finset (Fin n) → ℂⁿ → ℂ`:
`(∂̄ω)_I = ∑_{j ∈ I} (-1)^{#{i ∈ I | i < j}} ∂ω_{I ∖ j}/∂z̄ⱼ`. -/
noncomputable def dbarForm (ω : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ) :
    Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ :=
  fun I z => ∑ j ∈ I, dolbeaultSign j (I.erase j) * dbarPartial j (ω (I.erase j)) z

/-- `∂̄` raises the degree of a form by one. -/
lemma dbarForm_of_degree {q : ℕ} {ω : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    (hω : ∀ I : Finset (Fin n), I.card ≠ q → ω I = 0) (I : Finset (Fin n))
    (hI : I.card ≠ q + 1) : dbarForm ω I = 0 := by
  funext z
  refine Finset.sum_eq_zero fun j hj => ?_
  have : (I.erase j).card ≠ q := by
    have := Finset.card_pos.2 ⟨j, hj⟩
    rw [Finset.card_erase_of_mem hj]
    omega
  simp [hω _ this, dbarPartial]

/-- `∂̄` maps forms with `C^{m+1}` coefficients on an open set to forms with `C^m`
coefficients. -/
lemma contDiffOn_dbarForm {ω : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) {m : WithTop ℕ∞}
    (hω : ∀ I, ContDiffOn ℝ (m + 1) (ω I) U) (I : Finset (Fin n)) :
    ContDiffOn ℝ m (dbarForm ω I) U := by
  unfold dbarForm
  exact ContDiffOn.sum fun j _ => contDiffOn_const.mul (contDiffOn_dbarPartial hU (hω _))

/-- **`∂̄ ∘ ∂̄ = 0`** at every point of an open set on which the coefficients are `C²`. -/
theorem dbarForm_dbarForm {ω : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) (hω : ∀ I, ContDiffOn ℝ 2 (ω I) U)
    (I : Finset (Fin n)) {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U) :
    dbarForm (dbarForm ω) I z = 0 := by
  have hdiff : ∀ (k : Fin n) (J : Finset (Fin n)),
      DifferentiableAt ℝ (dbarPartial k (ω J)) z := fun k J =>
    ((contDiffOn_dbarPartial (m := 1) hU (hω J)).contDiffAt (hU.mem_nhds hz)).differentiableAt
      (by norm_num)
  set F : Fin n × Fin n → ℂ := fun p =>
    dolbeaultSign p.1 (I.erase p.1) * dolbeaultSign p.2 ((I.erase p.1).erase p.2) *
      dbarPartial p.1 (dbarPartial p.2 (ω ((I.erase p.1).erase p.2))) z with hF
  have hexp : dbarForm (dbarForm ω) I z = ∑ j ∈ I, ∑ k ∈ I.erase j, F (j, k) := by
    unfold dbarForm
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [dbarPartial_sum _ fun k _ => (hdiff k _).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dbarPartial_const_mul _ (hdiff k _), hF]
    ring
  have hanti : ∀ j ∈ I, ∀ k ∈ I.erase j, F (j, k) = -F (k, j) := by
    intro j hj k hk
    simp only [hF]
    rw [dolbeaultSign_mul_dolbeaultSign_swap (Finset.mem_of_mem_erase hk) hj
      (Finset.ne_of_mem_erase hk),
      show (I.erase k).erase j = (I.erase j).erase k from Finset.erase_right_comm,
      dbarPartial_comm k j ((hω _).contDiffAt (hU.mem_nhds hz))]
    ring
  have hswap : ∑ j ∈ I, ∑ k ∈ I.erase j, F (j, k) = ∑ k ∈ I, ∑ j ∈ I.erase k, F (j, k) :=
    Finset.sum_comm' fun j k => by
      simp only [Finset.mem_erase]
      tauto
  have : ∑ j ∈ I, ∑ k ∈ I.erase j, F (j, k) = -∑ j ∈ I, ∑ k ∈ I.erase j, F (j, k) := by
    conv_lhs => rw [hswap]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    exact hanti j (Finset.mem_of_mem_erase hj) k
      (Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hj).symm, hk⟩)
  rw [hexp]
  linear_combination (1 / 2 : ℂ) * this

end Forms

section Sheaf

variable (n) in
/-- The smooth `(0, q)`-forms on a set `U ⊆ ℂⁿ`, as coefficient families of degree `q` that are
smooth on `U` and vanish off `U`. -/
def dolbeaultSections (q : ℕ) (U : Set (EuclideanSpace ℂ (Fin n))) :
    AddSubgroup (Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ) where
  carrier := {ω | (∀ I : Finset (Fin n), I.card ≠ q → ω I = 0) ∧
    (∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (ω I) U) ∧ ∀ I, ∀ z ∉ U, ω I z = 0}
  add_mem' {a b} ha hb := ⟨fun I hI => by simp [ha.1 I hI, hb.1 I hI],
    fun I => (ha.2.1 I).add (hb.2.1 I), fun I z hz => by simp [ha.2.2 I z hz, hb.2.2 I z hz]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ => contDiffOn_const, fun _ _ _ => rfl⟩
  neg_mem' {a} ha := ⟨fun I hI => by simp [ha.1 I hI], fun I => (ha.2.1 I).neg,
    fun I z hz => by simp [ha.2.2 I z hz]⟩

/-- Restricting a form to a smaller set, extending by zero. -/
lemma indicator_mem_dolbeaultSections {q : ℕ} {U V : Set (EuclideanSpace ℂ (Fin n))}
    (hVU : V ⊆ U) {ω : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    (hω : ω ∈ dolbeaultSections n q U) :
    (fun I => V.indicator (ω I)) ∈ dolbeaultSections n q V := by
  refine ⟨fun I hI => by simp [hω.1 I hI], fun I => ?_, fun I z hz => by simp [hz]⟩
  exact ((hω.2.1 I).mono hVU).congr fun z hz => Set.indicator_of_mem hz _

variable (n) in
/-- The restriction of `(0, q)`-forms from `U` to `V ⊆ U`. -/
noncomputable def dolbeaultRestrict (q : ℕ) {U V : Opens (EuclideanSpace ℂ (Fin n))}
    (h : V ≤ U) : dolbeaultSections n q U →+ dolbeaultSections n q V where
  toFun ω := ⟨fun I => (V : Set _).indicator (ω.1 I),
    indicator_mem_dolbeaultSections h ω.2⟩
  map_zero' := by ext; simp
  map_add' a b := by
    ext I z
    by_cases hz : z ∈ (V : Set _) <;> simp [hz]

/-- The coefficients of the restriction of a form to `V` are its coefficients times the indicator
of `V`. -/
lemma dolbeaultRestrict_apply {q : ℕ} {U V : Opens (EuclideanSpace ℂ (Fin n))} (h : V ≤ U)
    (ω : dolbeaultSections n q U) (I : Finset (Fin n)) :
    (dolbeaultRestrict n q h ω).1 I = (V : Set _).indicator (ω.1 I) := rfl

/-- A form on `U` is determined by its values on `U`. -/
lemma dolbeaultSections_ext {q : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    {a b : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ} (ha : a ∈ dolbeaultSections n q U)
    (hb : b ∈ dolbeaultSections n q U) (h : ∀ I, ∀ z ∈ U, a I z = b I z) : a = b := by
  funext I z
  by_cases hz : z ∈ U
  · exact h I z hz
  · rw [ha.2.2 I z hz, hb.2.2 I z hz]

variable (n) in
/-- The presheaf of smooth `(0, q)`-forms on `ℂⁿ`. -/
noncomputable def dolbeaultPresheaf (q : ℕ) :
    TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of (EuclideanSpace ℂ (Fin n))) where
  obj U := AddCommGrpCat.of (dolbeaultSections n q (U.unop : Set _))
  map h := AddCommGrpCat.ofHom (dolbeaultRestrict n q h.unop.le)
  map_id U := by
    ext ω : 2
    refine Subtype.ext (dolbeaultSections_ext ?_ ω.2 fun I z hz => ?_)
    · exact (dolbeaultRestrict n q le_rfl ω).2
    · simp [dolbeaultRestrict_apply, hz]
  map_comp {X Y Z} f g := by
    ext ω : 2
    apply Subtype.ext
    funext I z
    change (dolbeaultRestrict n q (f ≫ g).unop.le ω).1 I z =
      (dolbeaultRestrict n q g.unop.le (dolbeaultRestrict n q f.unop.le ω)).1 I z
    simp only [dolbeaultRestrict_apply]
    by_cases hz : z ∈ ((Z.unop : Opens _) : Set _)
    · have hz' : z ∈ ((Y.unop : Opens _) : Set _) := g.unop.le hz
      simp [hz, hz']
    · simp [hz]

/-- The coefficients of the restriction map of `dolbeaultPresheaf` applied to a form are its
coefficients times the indicator of the smaller open set. -/
lemma dolbeaultPresheaf_map_apply {q : ℕ} {U V : (Opens (TopCat.of (EuclideanSpace ℂ (Fin n))))ᵒᵖ}
    (h : U ⟶ V) (ω : (dolbeaultPresheaf n q).obj U) (I : Finset (Fin n)) :
    ((dolbeaultPresheaf n q).map h ω).1 I = ((V.unop : Opens _) : Set _).indicator (ω.1 I) := rfl

/-- Compatible local forms agree on overlaps. -/
private lemma eq_of_isCompatible {q : ℕ} {ι : Type}
    {U : ι → Opens (TopCat.of (EuclideanSpace ℂ (Fin n)))}
    {sf : ∀ i, (dolbeaultPresheaf n q).obj (op (U i))}
    (hsf : TopCat.Presheaf.IsCompatible (dolbeaultPresheaf n q) U sf) (i j : ι) (I : Finset (Fin n))
    {z : EuclideanSpace ℂ (Fin n)} (hi : z ∈ U i) (hj : z ∈ U j) :
    (sf i).1 I z = (sf j).1 I z := by
  have h := congrArg (fun w : (dolbeaultPresheaf n q).obj (op (U i ⊓ U j)) => w.1 I z) (hsf i j)
  simp only [dolbeaultPresheaf_map_apply] at h
  have hz : z ∈ (U i : Set _) ∩ U j := ⟨hi, hj⟩
  simp only [Opens.coe_inf] at h
  rwa [Set.indicator_of_mem hz, Set.indicator_of_mem hz] at h

open Classical in
/-- The gluing of compatible local forms. -/
private noncomputable def glue {q : ℕ} {ι : Type}
    (U : ι → Opens (TopCat.of (EuclideanSpace ℂ (Fin n))))
    (sf : ∀ i, (dolbeaultPresheaf n q).obj (op (U i))) :
    Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ :=
  fun I z => if h : ∃ i, z ∈ U i then (sf h.choose).1 I z else 0

private lemma glue_eq {q : ℕ} {ι : Type} {U : ι → Opens (TopCat.of (EuclideanSpace ℂ (Fin n)))}
    {sf : ∀ i, (dolbeaultPresheaf n q).obj (op (U i))}
    (hsf : TopCat.Presheaf.IsCompatible (dolbeaultPresheaf n q) U sf) (i : ι) (I : Finset (Fin n))
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U i) : glue U sf I z = (sf i).1 I z := by
  have h : ∃ i, z ∈ U i := ⟨i, hz⟩
  unfold glue
  rw [dif_pos h]
  exact eq_of_isCompatible hsf _ _ I h.choose_spec hz

private lemma glue_mem {q : ℕ} {ι : Type} {U : ι → Opens (TopCat.of (EuclideanSpace ℂ (Fin n)))}
    {sf : ∀ i, (dolbeaultPresheaf n q).obj (op (U i))}
    (hsf : TopCat.Presheaf.IsCompatible (dolbeaultPresheaf n q) U sf) :
    glue U sf ∈ dolbeaultSections n q ((iSup U : Opens _) : Set _) := by
  refine ⟨fun I hI => ?_, fun I => ?_, fun I z hz => ?_⟩
  · funext z
    simp only [glue]
    split_ifs with h
    · rw [(sf h.choose).2.1 I hI]
    · rfl
  · intro z hz
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hz
    have hev : (sf i).1 I =ᶠ[𝓝 z] glue U sf I :=
      Filter.eventually_of_mem ((U i).isOpen.mem_nhds hi) fun w hw => (glue_eq hsf i I hw).symm
    exact (((sf i).2.2.1 I).contDiffAt ((U i).isOpen.mem_nhds hi)).congr_of_eventuallyEq
      hev.symm |>.contDiffWithinAt
  · have h : ¬ ∃ i, z ∈ U i := fun ⟨i, hi⟩ => hz (Opens.mem_iSup.2 ⟨i, hi⟩)
    unfold glue
    rw [dif_neg h]

variable (n) in
/-- The presheaf of smooth `(0, q)`-forms on `ℂⁿ` is a sheaf. -/
lemma isSheaf_dolbeaultPresheaf (q : ℕ) : (dolbeaultPresheaf n q).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  refine ⟨⟨glue U sf, glue_mem hsf⟩, fun i => ?_, fun t ht => ?_⟩
  · refine Subtype.ext (dolbeaultSections_ext ?_ (sf i).2 fun I z hz => ?_)
    · exact ((dolbeaultPresheaf n q).map (Opens.leSupr U i).op ⟨glue U sf, glue_mem hsf⟩).2
    · change ((U i : Opens _) : Set _).indicator (glue U sf I) z = _
      rw [Set.indicator_of_mem hz]
      exact glue_eq hsf i I hz
  · refine Subtype.ext (dolbeaultSections_ext t.2 (glue_mem hsf) fun I z hz => ?_)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hz
    have h := congrArg (fun w : (dolbeaultPresheaf n q).obj (op (U i)) => w.1 I z) (ht i)
    simp only [dolbeaultPresheaf_map_apply, Set.indicator_of_mem hi] at h
    change _ = glue U sf I z
    rw [h, glue_eq hsf i I hi]

variable (n) in
/-- The sheaf `ℰ^{0,q}` of smooth `(0, q)`-forms on `ℂⁿ`. -/
noncomputable def dolbeaultSheaf (q : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (EuclideanSpace ℂ (Fin n))) :=
  ⟨dolbeaultPresheaf n q, isSheaf_dolbeaultPresheaf n q⟩

end Sheaf

section Complex

/-- In `WithTop ℕ∞`, the smoothness exponent `∞` satisfies `∞ + 1 ≤ ∞`. -/
lemma top_add_one_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]

/-- On an open set `U`, `∂̄` of a form only depends on its restriction to `U`. -/
lemma dbarForm_indicator {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (ω : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ) (I : Finset (Fin n))
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U) :
    dbarForm (fun J => U.indicator (ω J)) I z = dbarForm ω I z := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dbarPartial_congr (Filter.eventually_of_mem (hU.mem_nhds hz)
    fun w hw => Set.indicator_of_mem hw _)]

/-- `∂̄` maps smooth `(0, q)`-forms on an open `U` to smooth `(0, q + 1)`-forms on `U`. -/
lemma indicator_dbarForm_mem {q : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {ω : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ} (hω : ω ∈ dolbeaultSections n q U) :
    (fun I => U.indicator (dbarForm ω I)) ∈ dolbeaultSections n (q + 1) U := by
  refine ⟨fun I hI => by simp [dbarForm_of_degree hω.1 I hI], fun I => ?_,
    fun I z hz => by simp [hz]⟩
  exact (contDiffOn_dbarForm hU (fun J => (hω.2.1 J).of_le top_add_one_le) I).congr
    fun z hz => Set.indicator_of_mem hz _

variable (n) in
/-- `∂̄ : ℰ^{0,q}(U) → ℰ^{0,q+1}(U)`. -/
noncomputable def dbarSections (q : ℕ) (U : Opens (EuclideanSpace ℂ (Fin n))) :
    dolbeaultSections n q U →+ dolbeaultSections n (q + 1) U where
  toFun ω := ⟨fun I => (U : Set _).indicator (dbarForm ω.1 I), indicator_dbarForm_mem U.isOpen ω.2⟩
  map_zero' := by
    ext I z
    simp [dbarForm, dbarPartial]
  map_add' a b := by
    ext I z
    by_cases hz : z ∈ (U : Set _)
    · have hd : ∀ (c : dolbeaultSections n q U) (J : Finset (Fin n)),
          DifferentiableAt ℝ (c.1 J) z := fun c J =>
        ((c.2.2.1 J).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
      simp only [AddMemClass.coe_add, Set.indicator_of_mem hz, dbarForm, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show a.1 (I.erase j) + b.1 (I.erase j) =
          fun w => a.1 (I.erase j) w + b.1 (I.erase j) w from rfl,
        dbarPartial_add (hd a _) (hd b _)]
      ring
    · simp [hz]

/-- The coefficients of `dbarSections n q U ω` are those of `dbarForm` of `ω` times the indicator
of `U`. -/
lemma dbarSections_apply {q : ℕ} {U : Opens (EuclideanSpace ℂ (Fin n))}
    (ω : dolbeaultSections n q U) (I : Finset (Fin n)) :
    (dbarSections n q U ω).1 I = (U : Set _).indicator (dbarForm ω.1 I) := rfl

/-- `∂̄` commutes with restriction. -/
lemma dbarSections_restrict {q : ℕ} {U V : Opens (EuclideanSpace ℂ (Fin n))} (h : V ≤ U)
    (ω : dolbeaultSections n q U) :
    dbarSections n q V (dolbeaultRestrict n q h ω) =
      dolbeaultRestrict n (q + 1) h (dbarSections n q U ω) := by
  apply Subtype.ext
  funext I z
  rw [dbarSections_apply, dolbeaultRestrict_apply, dbarSections_apply]
  by_cases hz : z ∈ (V : Set _)
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem (h hz)]
    exact dbarForm_indicator V.isOpen _ I hz
  · simp [hz]

variable (n) in
/-- The Dolbeault operator `∂̄ : ℰ^{0,q} ⟶ ℰ^{0,q+1}` as a morphism of sheaves. -/
noncomputable def dbarHom (q : ℕ) : dolbeaultSheaf n q ⟶ dolbeaultSheaf n (q + 1) :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (dbarSections n q U.unop)
      naturality {U V} h := by
        ext ω : 2
        exact dbarSections_restrict h.unop.le ω }

/-- The coefficients of `∂̄ ω` for a section `ω` over `U` are those of `dbarForm` of `ω` times the
indicator of `U`. -/
lemma dbarHom_app_apply {q : ℕ} (U : (Opens (TopCat.of (EuclideanSpace ℂ (Fin n))))ᵒᵖ)
    (ω : (dolbeaultSheaf n q).obj.obj U) (I : Finset (Fin n)) :
    ((dbarHom n q).hom.app U ω).1 I = ((U.unop : Opens _) : Set _).indicator (dbarForm ω.1 I) :=
  rfl

variable (n) in
/-- `∂̄ ∘ ∂̄ = 0` as a composite of morphisms of sheaves `ℰ^{0,q} ⟶ ℰ^{0,q+2}`. -/
lemma dbarHom_comp_dbarHom (q : ℕ) : dbarHom n q ≫ dbarHom n (q + 1) = 0 := by
  refine InducedCategory.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.ext fun ω => ?_))
  apply Subtype.ext
  funext I z
  change ((dbarHom n (q + 1)).hom.app U ((dbarHom n q).hom.app U ω)).1 I z = 0
  rw [dbarHom_app_apply]
  by_cases hz : z ∈ ((U.unop : Opens _) : Set _)
  · rw [Set.indicator_of_mem hz]
    change dbarForm (fun J => ((U.unop : Opens _) : Set _).indicator (dbarForm ω.1 J)) I z = 0
    rw [dbarForm_indicator (U.unop : Opens _).isOpen _ I hz]
    exact dbarForm_dbarForm (U.unop : Opens _).isOpen
      (fun J => (ω.2.2.1 J).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))) I hz
  · simp [hz]

variable (n) in
/-- The Dolbeault complex `ℰ^{0,0} ⟶ ℰ^{0,1} ⟶ ⋯` of sheaves on `ℂⁿ`. -/
noncomputable def dolbeaultComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (EuclideanSpace ℂ (Fin n)))) ℕ :=
  CochainComplex.of (dolbeaultSheaf n) (dbarHom n) (dbarHom_comp_dbarHom n)

end Complex

section Holomorphic

open scoped Manifold

/-- A function on an open `U ⊆ ℂⁿ`, extended by zero to `ℂⁿ`. -/
noncomputable def extendByZero {U : Opens (EuclideanSpace ℂ (Fin n))} (f : U → ℂ) :
    EuclideanSpace ℂ (Fin n) → ℂ :=
  open Classical in fun z => if h : z ∈ U then f ⟨z, h⟩ else 0

/-- The extension by zero of `f` agrees with `f` on `U`. -/
lemma extendByZero_of_mem {U : Opens (EuclideanSpace ℂ (Fin n))} (f : U → ℂ) {z}
    (h : z ∈ U) : extendByZero f z = f ⟨z, h⟩ := by
  simp [extendByZero, h]

/-- The extension by zero of `f` vanishes off `U`. -/
lemma extendByZero_of_notMem {U : Opens (EuclideanSpace ℂ (Fin n))} (f : U → ℂ) {z}
    (h : z ∉ U) : extendByZero f z = 0 := by
  simp [extendByZero, h]

/-- A function on an open `U ⊆ ℂⁿ` is holomorphic in Mathlib's manifold sense (complex `C^m` for
the model `𝓘(ℂ, ℂⁿ)` on the open submanifold `U`) iff its extension by zero is complex `C^m`
on `U`. -/
lemma contMDiff_iff_contDiffOn_extendByZero {U : Opens (EuclideanSpace ℂ (Fin n))}
    (f : U → ℂ) {m : WithTop ℕ∞} :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) m f ↔ ContDiffOn ℂ m (extendByZero f) U := by
  have hf : f = fun y : U => extendByZero f y :=
    funext fun y => (extendByZero_of_mem f y.2).symm
  refine ⟨fun h z hz => ?_, fun h y => ?_⟩
  · have h1 := h ⟨z, hz⟩
    rw [hf, contMDiffAt_subtype_iff] at h1
    exact (contMDiffAt_iff_contDiffAt.1 h1).contDiffWithinAt
  · rw [hf, contMDiffAt_subtype_iff]
    exact contMDiffAt_iff_contDiffAt.2 (h.contDiffAt (U.isOpen.mem_nhds y.2))

end Holomorphic

end MMP.Analytic
