module
public import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceComponentModule
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreFirstCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ProperFibreDimensionVanishing

/-!
# Gluing along the components of an SNC divisor

A foundational result used in the base point free theorem for log canonical pairs.

* Let `F = ∑ᵢ Fᵢ` be a reduced simple normal crossing divisor on a smooth variety `X` over a
  field `k`, regarded as the reduced closed subscheme `Supp F`. The finite closed cover of `F`
  by the components `Fᵢ` is a gluing cover: over every open `U ⊆ X`, regular functions on the
  `Fᵢ ∩ U` agreeing on every scheme-theoretic intersection `(Fᵢ ∩ Fⱼ) ∩ U` (cut out by
  `I_{Fᵢ} + I_{Fⱼ}`) are the restrictions of a unique regular function on `F ∩ U`, and the same
  holds for morphisms to an arbitrary scheme `Z`. Locally, in coordinates with
  `F = (x₁ ⋯ x_r = 0)`, the statement on functions is the exactness of
  `0 → R/(∏ xᵢ) → ⊕ᵢ R/(xᵢ) → ⊕_{i<j} R/(xᵢ, xⱼ)`.

## Main results

* `MMP.Intersection.IsSNCDivisor.existsUnique_glue`: gluing of functions and of morphisms
  along the components of an SNC divisor.

## Implementation notes

For the gluing, the components are indexed by `D.support`. The inclusions `Fᵢ ⟶ F` and
`Fᵢ ∩ Fⱼ ⟶ Fᵢ` are `AlgebraicGeometry.Scheme.IdealSheafData.inclusion`, and restriction to an
open is `Scheme.Hom.appLE` for functions and `Scheme.Hom.resLE` for morphisms, over the
preimages of an open `U` of `X`; every open of `F` is such a preimage, and `U = ⊤` is gluing on
`F` itself. Uniqueness holds for any reduced closed subscheme covered set-theoretically by
closed subschemes, since on a reduced scheme a section vanishing at every point is zero.
Existence of glued functions is the exactness above on SNC charts, whose algebraic core is
gluing modulo ideals, by induction on the number of components. Existence of glued morphisms is
gluing along a finite *closed* cover: near a point of `F ∩ U` all component maps land in one
affine open `W` of `Z`, morphisms into `W` are ring maps out of `Γ(W, ⊤)` which glue by the
function case, and the local morphisms then glue over an ordinary open cover.

## References

* [Kollár, Mori, *Birational geometry of algebraic varieties*][KM98]
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP.Intersection

open MMP.Mori (Divisor DivisorWithCoeffs)
open IsLocalRing

/-- The side condition of every restriction along an inclusion of closed subschemes. -/
private theorem le_preimage_inclusion {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J)
    (U : X.Opens) :
    J.subschemeι ⁻¹ᵁ U ≤ Scheme.IdealSheafData.inclusion h ⁻¹ᵁ I.subschemeι ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]

/-- The support `F = ∑ Fᵢ` of a divisor is contained in each component `Fᵢ`, as closed
subschemes. -/
private theorem suppIdeal_le {X : Scheme.{u}} {D : Divisor X} (E : D.support) :
    D.suppIdeal ≤ E.1.idealSheaf :=
  (suppIdeal_eq_finsetInf D).le.trans (Finset.inf_le E.2)

/-- The support of a divisor is a reduced closed subscheme. -/
private theorem isReduced_suppScheme {X : Scheme.{u}} (D : Divisor X) :
    IsReduced D.suppScheme :=
  inferInstanceAs (IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme)

/-- The support of a divisor is covered set-theoretically by its components. -/
private theorem support_suppIdeal_subset_iUnion {X : Scheme.{u}} (D : Divisor X) :
    ((DivisorWithCoeffs.suppIdeal D).support : Set X) ⊆
      ⋃ E : D.support, (E.1.idealSheaf.support : Set X) := by
  intro x hx
  rw [DivisorWithCoeffs.coe_support_suppIdeal, SetLike.mem_coe,
    DivisorWithCoeffs.mem_supp_iff] at hx
  obtain ⟨E, hE, hxE⟩ := hx
  exact Set.mem_iUnion.mpr ⟨⟨E, Finsupp.mem_support_iff.mpr hE⟩, hxE⟩

/-- On a reduced closed subscheme `I` covered set-theoretically by closed subschemes `J i ≥ I`,
a section over an open is determined by its restrictions to the `J i`. -/
private theorem appLE_inclusion_injective {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsReduced I.subscheme] {ι : Type*} {J : ι → X.IdealSheafData} (hJ : ∀ i, I ≤ J i)
    (hcov : (I.support : Set X) ⊆ ⋃ i, ((J i).support : Set X)) (U : X.Opens)
    (t t' : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U))
    (h : ∀ i, (Scheme.IdealSheafData.inclusion (hJ i)).appLE (I.subschemeι ⁻¹ᵁ U)
        ((J i).subschemeι ⁻¹ᵁ U) (le_preimage_inclusion _ _) t =
      (Scheme.IdealSheafData.inclusion (hJ i)).appLE (I.subschemeι ⁻¹ᵁ U)
        ((J i).subschemeι ⁻¹ᵁ U) (le_preimage_inclusion _ _) t') :
    t = t' := by
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  ext y
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hy
  have hyI : I.subschemeι y ∈ (I.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hyI)
  rw [← Scheme.IdealSheafData.range_subschemeι] at hi
  obtain ⟨w, hw⟩ := hi
  have hwy : Scheme.IdealSheafData.inclusion (hJ i) w = y := by
    apply I.subschemeι.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι, hw]
  have h0 := congrArg (fun r => (J i).subscheme.basicOpen r) (sub_eq_zero.mpr (h i))
  simp only [← map_sub, Scheme.basicOpen_zero] at h0
  rw [Scheme.basicOpen_appLE] at h0
  have : w ∈ ((⊥ : (J i).subscheme.Opens) : Set (J i).subscheme) := by
    rw [← h0]
    refine ⟨?_, ?_⟩
    · change (J i).subschemeι w ∈ U
      rw [hw]; exact I.subscheme.basicOpen_le _ hy
    · change Scheme.IdealSheafData.inclusion (hJ i) w ∈ (I.subscheme.basicOpen (t - t') : Set _)
      rw [hwy]; exact hy
  exact this

/-- On a reduced scheme, a section over an open is determined by its pullbacks along a jointly
surjective family of morphisms. -/
private theorem app_injective_of_isReduced {X : Scheme.{u}} [IsReduced X] {ι : Type*}
    {Y : ι → Scheme.{u}} (h : ∀ i, Y i ⟶ X) (hsurj : ∀ x, ∃ i y, h i y = x) (W : X.Opens)
    (s s' : Γ(X, W)) (e : ∀ i, (h i).app W s = (h i).app W s') : s = s' := by
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  ext x
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨i, y, rfl⟩ := hsurj x
  have h0 : (Y i).basicOpen ((h i).app W (s - s')) = ⊥ := by
    rw [map_sub, e i, sub_self, Scheme.basicOpen_zero]
  have : y ∈ ((⊥ : (Y i).Opens) : Set (Y i)) := by
    rw [← h0, ← Scheme.preimage_basicOpen]; exact hx
  exact this

/-- Morphisms out of a reduced scheme are determined by their composites with a jointly
surjective family of morphisms. -/
private theorem hom_ext_of_isReduced {X Z : Scheme.{u}} [IsReduced X] {ι : Type*}
    {Y : ι → Scheme.{u}} (h : ∀ i, Y i ⟶ X) (hsurj : ∀ x, ∃ i y, h i y = x) (t t' : X ⟶ Z)
    (e : ∀ i, h i ≫ t = h i ≫ t') : t = t' := by
  have hbase : t.base = t'.base := by
    ext x
    obtain ⟨i, y, rfl⟩ := hsurj x
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun g : Y i ⟶ Z => g y) (e i)
  refine Scheme.Hom.ext hbase fun U => ?_
  have hU : t' ⁻¹ᵁ U ≤ t ⁻¹ᵁ U := fun x hx => by
    change t x ∈ U; rw [show t x = t' x from congrArg (fun g => g x) hbase]; exact hx
  have hL : t.app U ≫ X.presheaf.map
      (eqToHom congr((TopologicalSpace.Opens.map $hbase.symm).obj U)).op =
      t.appLE U (t' ⁻¹ᵁ U) hU := rfl
  rw [hL, ← Scheme.Hom.appLE_eq_app]
  ext a
  refine app_injective_of_isReduced h hsurj _ _ _ fun i => ?_
  have key : ∀ (f g : Y i ⟶ Z) (_ : f = g) (V : (Y i).Opens) (e1 : V ≤ f ⁻¹ᵁ U)
      (e2 : V ≤ g ⁻¹ᵁ U), f.appLE U V e1 = g.appLE U V e2 := by rintro f g rfl V e1 e2; rfl
  have := key _ _ (e i) (h i ⁻¹ᵁ t' ⁻¹ᵁ U) (fun x hx => hU hx) le_rfl
  rw [← Scheme.Hom.appLE_comp_appLE (h i) t U (t' ⁻¹ᵁ U) _ hU le_rfl,
    ← Scheme.Hom.appLE_comp_appLE (h i) t' U (t' ⁻¹ᵁ U) _ le_rfl le_rfl] at this
  have h2 := congrArg (fun φ => φ a) (congrArg CommRingCat.Hom.hom this)
  simpa only [CommRingCat.comp_apply, Scheme.Hom.appLE_eq_app] using h2

/-- If closed subschemes `J i ≥ I` cover `I` set-theoretically, then over every open `U` of `X`
the restricted inclusions `J i ∩ U ⟶ I ∩ U` are jointly surjective. -/
private theorem exists_resLE_inclusion_eq {X : Scheme.{u}} {I : X.IdealSheafData} {ι : Type*}
    {J : ι → X.IdealSheafData} (hJ : ∀ i, I ≤ J i)
    (hcov : (I.support : Set X) ⊆ ⋃ i, ((J i).support : Set X)) (U : X.Opens)
    (y : (I.subschemeι ⁻¹ᵁ U).toScheme) :
    ∃ i, ∃ w, (Scheme.IdealSheafData.inclusion (hJ i)).resLE (I.subschemeι ⁻¹ᵁ U)
        ((J i).subschemeι ⁻¹ᵁ U) (le_preimage_inclusion _ _) w = y := by
  have hyI : I.subschemeι y.1 ∈ (I.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y.1, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hyI)
  rw [← Scheme.IdealSheafData.range_subschemeι] at hi
  obtain ⟨w, hw⟩ := hi
  have hwy : Scheme.IdealSheafData.inclusion (hJ i) w = y.1 := by
    apply I.subschemeι.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι, hw]
  have hwU : w ∈ (J i).subschemeι ⁻¹ᵁ U := by
    change (J i).subschemeι w ∈ U
    rw [hw]; exact y.2
  refine ⟨i, ⟨w, hwU⟩, Subtype.ext ?_⟩
  have := congrArg (fun g => g ⟨w, hwU⟩)
    (Scheme.Hom.resLE_comp_ι (Scheme.IdealSheafData.inclusion (hJ i))
      (U := I.subschemeι ⁻¹ᵁ U) (V := (J i).subschemeι ⁻¹ᵁ U) (le_preimage_inclusion _ _))
  simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at this
  exact this.trans hwy

/-- **Gluing modulo ideals.** If ideals `I i`, `i ∈ s`, satisfy
`⨅_{i ∈ t} (I i ⊔ I j) ≤ (⨅_{i ∈ t} I i) ⊔ I j` (for coordinate ideals `(xᵢ)` this is
`⋂_{i ∈ t} (xᵢ, x_j) = (∏_{i ∈ t} xᵢ, x_j)`), then elements `a i` which agree modulo every
`I i ⊔ I j` are the residues of a single element. This is the exactness of
`R → ∏ᵢ R/Iᵢ → ∏_{i,j} R/(Iᵢ + Iⱼ)` in the middle. -/
private theorem exists_forall_sub_mem {R ι : Type*} [CommRing R] [DecidableEq ι]
    (I : ι → Ideal R) (s : Finset ι)
    (H : ∀ t ⊆ s, ∀ j ∈ s, t.inf (fun i => I i ⊔ I j) ≤ t.inf I ⊔ I j)
    (a : ι → R) (ha : ∀ i ∈ s, ∀ j ∈ s, a i - a j ∈ I i ⊔ I j) :
    ∃ c, ∀ i ∈ s, c - a i ∈ I i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j s hj ih =>
    obtain ⟨c', hc'⟩ := ih
      (fun t ht i hi => H t (ht.trans (Finset.subset_insert _ _)) i (Finset.mem_insert_of_mem hi))
      (fun i hi k hk => ha i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk))
    have hmem : c' - a j ∈ s.inf I ⊔ I j := by
      refine H s (Finset.subset_insert _ _) j (Finset.mem_insert_self _ _) ?_
      rw [Submodule.mem_finsetInf]
      intro i hi
      simpa using add_mem (Submodule.mem_sup_left (hc' i hi) : c' - a i ∈ I i ⊔ I j)
        (ha i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_self _ _))
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hmem
    refine ⟨c' - x, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [show c' - x - a i = y by linear_combination hxy.symm]
      exact hy
    · rw [show c' - x - a i = (c' - a i) - x by ring]
      exact sub_mem (hc' i hi) ((Submodule.mem_finsetInf.mp hx) i hi)

section RegularSystemOfParameters

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ} {z : Fin n → R}

/-- A regular system of parameters is a minimal generating list of the maximal ideal. -/
private theorem ofList_eq_maximalIdeal_and_length_eq (hz : MMP.Mori.IsRegularSystemOfParameters z) :
    Ideal.ofList (List.ofFn z) = maximalIdeal R ∧
      (List.ofFn z).length = (maximalIdeal R).spanFinrank := by
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  refine ⟨?_, ?_⟩
  · rw [← hz.1]
    exact congrArg Ideal.span (Set.ext fun a => by simp [List.mem_ofFn])
  · have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hz.2] at h
    rw [List.length_ofFn]
    exact_mod_cast h.symm

/-- No member of a regular system of parameters lies in the ideal generated by the others. -/
private theorem notMem_span_image_compl (hz : MMP.Mori.IsRegularSystemOfParameters z) (i : Fin n) :
    z i ∉ Ideal.span (z '' {i}ᶜ) := by
  intro h
  have hle : maximalIdeal R ≤ Ideal.span (z '' {i}ᶜ) := by
    rw [← hz.1, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    by_cases hl : l = i
    · subst hl; exact h
    · exact Ideal.subset_span ⟨l, hl, rfl⟩
  have heq : maximalIdeal R = Ideal.span (z '' {i}ᶜ) := le_antisymm hle (by
    rw [← hz.1]; exact Ideal.span_mono (Set.image_subset_range _ _))
  have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.toFinite (z '' {i}ᶜ))
  change (Ideal.span _).spanFinrank ≤ _ at h1
  rw [← heq, ← (ofList_eq_maximalIdeal_and_length_eq hz).2, List.length_ofFn] at h1
  have h2 : (z '' {i}ᶜ).ncard ≤ n - 1 := by
    calc (z '' {i}ᶜ).ncard ≤ ({i}ᶜ : Set (Fin n)).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = n - 1 := by
        rw [Set.ncard_eq_toFinset_card']; simp [Finset.card_compl]
  have : 0 < n := i.pos
  omega

/-- Two distinct members of a regular system of parameters generate a prime ideal. -/
private theorem isPrime_span_sup_span (hz : MMP.Mori.IsRegularSystemOfParameters z) {k j : Fin n}
    (hkj : k ≠ j) :
    (Ideal.span {z k} ⊔ Ideal.span {z j}).IsPrime := by
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hgen, hlen⟩ := ofList_eq_maximalIdeal_and_length_eq hz
  have hn : 1 < n := by
    by_contra h; push Not at h
    exact hkj (Fin.ext (by omega))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set τ := Equiv.swap (0 : Fin (m+2)) k
  set σ := τ * Equiv.swap 1 (τ j)
  have hτj : τ j ≠ 0 := by
    intro h; apply hkj
    have := congrArg τ h
    simp only [τ, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact this.symm
  have hσ0 : σ 0 = k := by
    simp only [σ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hτj)]
    simp [τ]
  have hσ1 : σ 1 = j := by
    simp [σ, τ]
  have hperm := σ.ofFn_comp_perm z
  obtain ⟨hmain, -⟩ :=
    IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R
  obtain ⟨-, hquot⟩ :=
    hmain _ ((Ideal.ofList_eq_of_perm hperm).trans hgen) (hperm.length_eq.trans hlen)
  have h2 := (hquot 2 (by simp)).1
  have htake : (List.ofFn (z ∘ σ)).take 2 = [z k, z j] := by
    rw [List.ofFn_succ, List.ofFn_succ]
    simp [hσ0, ← hσ1]
  rw [htake] at h2
  have : IsDomain (R ⧸ Ideal.ofList [z k, z j]) := IsRegularLocalRing.isDomain _
  simpa using (Ideal.Quotient.isDomain_iff_prime _).mp this

/-- **The coordinate monomial calculation.** For a regular system of parameters `z` and indices
`p i` distinct on `S ∪ {j}`, `⋂_{i ∈ S} (z_{p i}, z_{p j}) ≤ (∏_{i ∈ S} z_{p i}, z_{p j})`. -/
private theorem finsetInf_span_sup_le_span_prod_sup {ι : Type*} [DecidableEq ι]
    (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (p : ι → Fin n) (S : Finset ι) (j : ι) (hp : Set.InjOn p (insert j S : Finset ι))
    (hj : j ∉ S) :
    S.inf (fun i => Ideal.span {z (p i)} ⊔ Ideal.span {z (p j)}) ≤
      Ideal.span {∏ i ∈ S, z (p i)} ⊔ Ideal.span {z (p j)} := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have hkj : p k ≠ p j := fun h => hj (by
      have := hp (by simp) (by simp) h; rw [this]; exact Finset.mem_insert_self _ _)
    have hjS : j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
    have hp' : Set.InjOn p (insert j S : Finset ι) :=
      hp.mono (Finset.coe_subset.mpr (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
    intro a ha
    rw [Finset.inf_insert] at ha
    obtain ⟨ha1, ha2⟩ := Submodule.mem_inf.mp ha
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (ih hp' hjS ha2)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have hP := isPrime_span_sup_span hz hkj
    have hpb : (b * ∏ i ∈ S, z (p i)) ∈ Ideal.span {z (p k)} ⊔ Ideal.span {z (p j)} := by
      have : b * ∏ i ∈ S, z (p i) = a - c * z (p j) := by rw [← hxy]; ring
      rw [this]
      exact sub_mem ha1
        (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    have hnp : (∏ i ∈ S, z (p i)) ∉ Ideal.span {z (p k)} ⊔ Ideal.span {z (p j)} := by
      intro hm
      obtain ⟨i, hi, hzi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).mp hm
      have hik : p i ≠ p k := fun h => hk (by
        have := hp (by simp [hi]) (by simp) h; rw [← this]; exact hi)
      have hij : p i ≠ p j := fun h => hjS (by
        have := hp (by simp [hi]) (by simp) h; rw [← this]; exact hi)
      apply notMem_span_image_compl hz (p i)
      refine (sup_le ?_ ?_ : Ideal.span {z (p k)} ⊔ Ideal.span {z (p j)} ≤ _) hzi
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.subset_span ⟨p k, Ne.symm hik, rfl⟩
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.subset_span ⟨p j, Ne.symm hij, rfl⟩
    have hb := (hP.mem_or_mem hpb).resolve_right hnp
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hb
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hu
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hv
    rw [Finset.prod_insert hk]
    have : a = u * (z (p k) * ∏ i ∈ S, z (p i)) + (v * ∏ i ∈ S, z (p i) + c) * z (p j) := by
      rw [← hxy, ← huv]; ring
    rw [this]
    exact add_mem
      (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

end RegularSystemOfParameters

/-- The coordinate calculation in the local ring at a closed point of an SNC divisor. -/
private theorem finsetInf_stalk_sup_le {X Y : Scheme.{u}} [IsLocallyNoetherian X] {f : X ⟶ Y}
    {D : Divisor X} (hD : IsSNCDivisor f D) (x : X) (hx : IsClosed ({x} : Set X))
    (t : Finset (MMP.Mori.PrimeDivisor X)) (ht : t ⊆ D.support) (j : MMP.Mori.PrimeDivisor X)
    (hj : j ∈ D.support) :
    t.inf (fun E => IdealSheafData.stalk E.idealSheaf x ⊔ IdealSheafData.stalk j.idealSheaf x) ≤
      t.inf (fun E => IdealSheafData.stalk E.idealSheaf x) ⊔
        IdealSheafData.stalk j.idealSheaf x := by
  classical
  by_cases hxj : x ∉ j.support
  · rw [stalk_idealSheaf_eq_top_of_notMem_support j hxj]; simp
  push Not at hxj
  by_cases hjt : j ∈ t
  · exact (Finset.inf_le hjt).trans (sup_le le_sup_right le_sup_right)
  obtain ⟨n, w, σ, hw, hσ, hσE⟩ := hD.exists_isRegularSystemOfParameters x hx
  let p : MMP.Mori.PrimeDivisor X → Fin n := fun E =>
    if h : E ∈ D.support ∧ x ∈ E.support then σ ⟨E, h⟩ else σ ⟨j, hj, hxj⟩
  have hpE : ∀ E (h : E ∈ D.support ∧ x ∈ E.support),
      IdealSheafData.stalk E.idealSheaf x = Ideal.span {w (p E)} := by
    intro E h; simp only [p, dif_pos h]; exact hσE ⟨E, h⟩
  set S := t.filter fun E => x ∈ E.support
  have hjS : j ∉ S := fun h => hjt (Finset.mem_filter.mp h).1
  have hSD : ∀ E ∈ insert j S, E ∈ D.support ∧ x ∈ E.support := by
    intro E hE
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact ⟨hj, hxj⟩
    · exact ⟨ht (Finset.mem_filter.mp hE).1, (Finset.mem_filter.mp hE).2⟩
  have hinj : Set.InjOn p (insert j S : Finset _) := by
    intro E hE E' hE' h
    simp only [p, dif_pos (hSD E hE), dif_pos (hSD E' hE')] at h
    exact congrArg Subtype.val (hσ h)
  calc _ ≤ S.inf (fun E => IdealSheafData.stalk E.idealSheaf x ⊔
          IdealSheafData.stalk j.idealSheaf x) := Finset.inf_mono (Finset.filter_subset _ _)
    _ = S.inf (fun E => Ideal.span {w (p E)} ⊔ Ideal.span {w (p j)}) := by
        refine Finset.inf_congr rfl fun E hE => ?_
        rw [hpE E (hSD E (Finset.mem_insert_of_mem hE)), hpE j ⟨hj, hxj⟩]
    _ ≤ Ideal.span {∏ E ∈ S, w (p E)} ⊔ Ideal.span {w (p j)} :=
        finsetInf_span_sup_le_span_prod_sup hw p S j hinj hjS
    _ ≤ _ := by
        rw [← hpE j ⟨hj, hxj⟩]
        refine sup_le_sup_right (Finset.le_inf fun E hE => ?_) _
        by_cases hxE : x ∈ E.support
        · have hES : E ∈ S := Finset.mem_filter.mpr ⟨hE, hxE⟩
          rw [hpE E (hSD E (Finset.mem_insert_of_mem hES)), Ideal.span_singleton_le_span_singleton]
          exact Finset.dvd_prod_of_mem _ hES
        · rw [stalk_idealSheaf_eq_top_of_notMem_support E hxE]; exact le_top

/-- Sections over an affine open of a finite intersection of ideal sheaves. -/
private theorem ideal_finsetInf {X : Scheme.{u}} {ι : Type*} (t : Finset ι)
    (I : ι → X.IdealSheafData)
    (V : X.affineOpens) : (t.inf I).ideal V = t.inf fun i => (I i).ideal V := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.inf_insert, Finset.inf_insert, ← ih]; rfl

/-- The coordinate calculation on an affine open, checked at its closed points. -/
private theorem finsetInf_ideal_sup_le {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} [Smooth f] {D : Divisor X}
    (hD : IsSNCDivisor f D) (V : X.affineOpens)
    (t : Finset (MMP.Mori.PrimeDivisor X)) (ht : t ⊆ D.support) (j : MMP.Mori.PrimeDivisor X)
    (hj : j ∈ D.support) :
    t.inf (fun E => E.idealSheaf.ideal V ⊔ j.idealSheaf.ideal V) ≤
      t.inf (fun E => E.idealSheaf.ideal V) ⊔ j.idealSheaf.ideal V := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  refine Ideal.le_of_localization_maximal fun P hP => ?_
  let y : PrimeSpectrum Γ(X, V) := ⟨P, hP.isPrime⟩
  have := V.2.isOpenImmersion_fromSpec
  have hyV : V.2.fromSpec y ∈ V.1 := V.2.range_fromSpec.le ⟨y, rfl⟩
  set x := V.2.fromSpec y
  have hxc : IsClosed ({x} : Set X) := by
    have h1 : IsClosed ({y} : Set (PrimeSpectrum Γ(X, V))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hP
    have h2 : IsLocallyClosed ({x} : Set X) := by
      have := h1.isLocallyClosed.image V.2.fromSpec.isOpenEmbedding.isInducing
        V.2.fromSpec.isOpenEmbedding.isOpen_range.isLocallyClosed
      convert this using 1
      ext z
      constructor
      · rintro rfl; exact ⟨y, rfl, rfl⟩
      · rintro ⟨w, hw, rfl⟩; rw [Set.mem_singleton_iff.mp hw]; rfl
    exact isClosed_singleton_of_isLocallyClosed_singleton h2
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hyV⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P := V.2.isLocalization_stalk' y hyV
  let e := IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk x) (Localization.AtPrime P)
  have he : (e : X.presheaf.stalk x →+* Localization.AtPrime P).comp
      (X.presheaf.germ V.1 x hyV).hom = algebraMap Γ(X, V) (Localization.AtPrime P) :=
    e.toAlgHom.comp_algebraMap
  have key : Ideal.map (X.presheaf.germ V.1 x hyV).hom
      (t.inf (fun E => E.idealSheaf.ideal V ⊔ j.idealSheaf.ideal V)) ≤
      Ideal.map (X.presheaf.germ V.1 x hyV).hom
      (t.inf (fun E => E.idealSheaf.ideal V) ⊔ j.idealSheaf.ideal V) := by
    rw [Ideal.map_sup, ← ideal_finsetInf, ← IdealSheafData.stalk_eq_map_germ _ x V hyV,
      ← IdealSheafData.stalk_eq_map_germ _ x V hyV, stalk_finsetInf]
    refine le_trans (Finset.le_inf fun E hE => Ideal.map_mono (Finset.inf_le hE)) ?_
    refine le_trans (le_of_eq (Finset.inf_congr rfl fun E _ => by
      rw [Ideal.map_sup, ← IdealSheafData.stalk_eq_map_germ _ x V hyV,
        ← IdealSheafData.stalk_eq_map_germ _ x V hyV])) ?_
    exact finsetInf_stalk_sup_le hD x hxc t ht j hj
  rw [← he, ← Ideal.map_map, ← Ideal.map_map]
  exact Ideal.map_mono key

/-- Restricting the image of a function on `X` along an inclusion of closed subschemes. -/
private theorem appLE_inclusion_app {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J)
    (V : X.Opens) (a : Γ(X, V)) :
    (Scheme.IdealSheafData.inclusion h).appLE (I.subschemeι ⁻¹ᵁ V) (J.subschemeι ⁻¹ᵁ V)
      (le_preimage_inclusion _ _)
      (I.subschemeι.app V a) = J.subschemeι.app V a := by
  have key : ∀ (g g' : J.subscheme ⟶ X) (_ : g = g') (e1 : J.subschemeι ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)
      (e2 : J.subschemeι ⁻¹ᵁ V ≤ g' ⁻¹ᵁ V), g.appLE V _ e1 = g'.appLE V _ e2 := by
    rintro g g' rfl e1 e2; rfl
  have := key _ _ (Scheme.IdealSheafData.inclusion_subschemeι h)
    (by rw [Scheme.IdealSheafData.inclusion_subschemeι]) le_rfl
  rw [Scheme.Hom.comp_appLE] at this
  rw [← CommRingCat.comp_apply, this, ← Scheme.Hom.app_eq_appLE]

/-- Existence of glued functions over an affine open: the exactness of
`R/(∏ xᵢ) → ⊕ᵢ R/(xᵢ) → ⊕_{i,j} R/(xᵢ, xⱼ)`. -/
private theorem exists_glue_affine {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} [Smooth f] {D : Divisor X}
    (hD : IsSNCDivisor f D) (V : X.affineOpens)
    (s : ∀ E : D.support, Γ(E.1.idealSheaf.subscheme, E.1.idealSheaf.subschemeι ⁻¹ᵁ V.1))
    (hs : ∀ E E' : D.support,
        (Scheme.IdealSheafData.inclusion le_sup_left).appLE
            (E.1.idealSheaf.subschemeι ⁻¹ᵁ V.1)
            ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ V.1)
            (le_preimage_inclusion _ _)
            (s E) =
          (Scheme.IdealSheafData.inclusion le_sup_right).appLE
            (E'.1.idealSheaf.subschemeι ⁻¹ᵁ V.1)
            ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ V.1)
            (le_preimage_inclusion _ _)
            (s E')) :
    ∃ t : Γ(D.suppScheme, D.suppIdeal.subschemeι ⁻¹ᵁ V.1), ∀ E : D.support,
        (Scheme.IdealSheafData.inclusion
            (suppIdeal_le E)).appLE
          (D.suppIdeal.subschemeι ⁻¹ᵁ V.1) (E.1.idealSheaf.subschemeι ⁻¹ᵁ V.1)
          (le_preimage_inclusion _ _) t =
          s E := by
  classical
  let E_ideal : MMP.Mori.PrimeDivisor X → Ideal Γ(X, V.1) := fun E => E.idealSheaf.ideal V
  choose a ha using fun E : D.support => E.1.idealSheaf.subschemeι_app_surjective V (s E)
  let a' : MMP.Mori.PrimeDivisor X → Γ(X, V.1) := fun E => if h : E ∈ D.support then a ⟨E, h⟩ else 0
  have ha' : ∀ E : D.support, a' E.1 = a E := fun E => dif_pos E.2
  have hcompat : ∀ i ∈ D.support, ∀ j ∈ D.support, a' i - a' j ∈ E_ideal i ⊔ E_ideal j := by
    intro i hi j hj
    have h1 := hs ⟨i, hi⟩ ⟨j, hj⟩
    rw [← ha, ← ha, appLE_inclusion_app, appLE_inclusion_app] at h1
    have : a' i - a' j ∈ RingHom.ker ((i.idealSheaf ⊔ j.idealSheaf).subschemeι.app V).hom := by
      rw [RingHom.mem_ker, map_sub, ha' ⟨i, hi⟩, ha' ⟨j, hj⟩]
      exact sub_eq_zero.mpr h1
    rwa [Scheme.IdealSheafData.ker_subschemeι_app] at this
  obtain ⟨c, hc⟩ := exists_forall_sub_mem E_ideal D.support (finsetInf_ideal_sup_le hD V) a' hcompat
  refine ⟨D.suppIdeal.subschemeι.app V c, fun E => ?_⟩
  rw [appLE_inclusion_app, ← ha]
  have h : c - a' E.1 ∈ E.1.idealSheaf.ideal V := hc E.1 E.2
  rwa [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker, map_sub, ha', sub_eq_zero] at h

/-- Restriction along an inclusion of closed subschemes commutes with restriction to smaller
opens. -/
private theorem appLE_inclusion_map {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J)
    {U U' : X.Opens} (iI : I.subschemeι ⁻¹ᵁ U' ⟶ I.subschemeι ⁻¹ᵁ U)
    (iJ : J.subschemeι ⁻¹ᵁ U' ⟶ J.subschemeι ⁻¹ᵁ U) (x : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U)) :
    (Scheme.IdealSheafData.inclusion h).appLE (I.subschemeι ⁻¹ᵁ U') (J.subschemeι ⁻¹ᵁ U')
      (le_preimage_inclusion _ _)
      (I.subscheme.presheaf.map iI.op x) =
    J.subscheme.presheaf.map iJ.op ((Scheme.IdealSheafData.inclusion h).appLE
      (I.subschemeι ⁻¹ᵁ U) (J.subschemeι ⁻¹ᵁ U)
      (le_preimage_inclusion _ _) x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- Every open `J ∩ U` of a closed subscheme is covered by the `J ∩ V`, `V ⊆ U` affine. -/
private theorem le_iSup_preimage_affine {X : Scheme.{u}} (J : X.IdealSheafData) (U : X.Opens) :
    J.subschemeι ⁻¹ᵁ U ≤ ⨆ V : {V : X.affineOpens // V.1 ≤ U}, J.subschemeι ⁻¹ᵁ V.1.1 := by
  intro w hw
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show J.subschemeι w ∈ (U : Set X) from hw)
      U.2
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hwV⟩

/-- Existence of glued functions (the exactness of
`0 → R/(∏ xᵢ) → ⊕ᵢ R/(xᵢ) → ⊕_{i<j} R/(xᵢ, xⱼ)` on SNC charts). -/
private theorem exists_glue_functions {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} [Smooth f] {D : Divisor X}
    (hD : IsSNCDivisor f D) (U : X.Opens)
    (s : ∀ E : D.support, Γ(E.1.idealSheaf.subscheme, E.1.idealSheaf.subschemeι ⁻¹ᵁ U))
    (hs : ∀ E E' : D.support,
        (Scheme.IdealSheafData.inclusion le_sup_left).appLE
            (E.1.idealSheaf.subschemeι ⁻¹ᵁ U) ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ U)
            (le_preimage_inclusion _ _)
            (s E) =
          (Scheme.IdealSheafData.inclusion le_sup_right).appLE
            (E'.1.idealSheaf.subschemeι ⁻¹ᵁ U) ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ U)
            (le_preimage_inclusion _ _)
            (s E')) :
    ∃ t : Γ(D.suppScheme, D.suppIdeal.subschemeι ⁻¹ᵁ U), ∀ E : D.support,
        (Scheme.IdealSheafData.inclusion
            (suppIdeal_le E)).appLE
          (D.suppIdeal.subschemeι ⁻¹ᵁ U) (E.1.idealSheaf.subschemeι ⁻¹ᵁ U)
          (le_preimage_inclusion _ _) t =
          s E := by
  classical
  have := isReduced_suppScheme D
  have hcov := support_suppIdeal_subset_iUnion D
  have hle : ∀ (J : X.IdealSheafData) (V : {V : X.affineOpens // V.1 ≤ U}),
      J.subschemeι ⁻¹ᵁ V.1.1 ≤ J.subschemeι ⁻¹ᵁ U := fun J V x hx => V.2 hx
  let sV : ∀ V : {V : X.affineOpens // V.1 ≤ U}, ∀ E : D.support,
      Γ(E.1.idealSheaf.subscheme, E.1.idealSheaf.subschemeι ⁻¹ᵁ V.1.1) := fun V E =>
    E.1.idealSheaf.subscheme.presheaf.map (homOfLE (hle _ V)).op (s E)
  choose tV htV using fun V : {V : X.affineOpens // V.1 ≤ U} =>
    exists_glue_affine hD V.1 (sV V) fun E E' => by
      simp only [sV]
      rw [appLE_inclusion_map _ _ (homOfLE (hle _ V)), appLE_inclusion_map _ _ (homOfLE (hle _ V)),
        hs]
  obtain ⟨t, ht, -⟩ := D.suppScheme.sheaf.existsUnique_gluing'
    (fun V : {V : X.affineOpens // V.1 ≤ U} => D.suppIdeal.subschemeι ⁻¹ᵁ V.1.1)
    (D.suppIdeal.subschemeι ⁻¹ᵁ U) (fun V => homOfLE (hle _ V))
    (le_iSup_preimage_affine _ U) tV (by
      intro V W
      refine appLE_inclusion_injective (J := fun E : D.support => E.1.idealSheaf)
        suppIdeal_le hcov
        (V.1.1 ⊓ W.1.1) _ _ fun E => ?_
      have hE := suppIdeal_le E
      have h1 := appLE_inclusion_map (U := V.1.1) (U' := V.1.1 ⊓ W.1.1) hE
        (TopologicalSpace.Opens.infLELeft (D.suppIdeal.subschemeι ⁻¹ᵁ V.1.1)
          (D.suppIdeal.subschemeι ⁻¹ᵁ W.1.1))
        (homOfLE (fun x hx => hx.1) : E.1.idealSheaf.subschemeι ⁻¹ᵁ (V.1.1 ⊓ W.1.1) ⟶ _) (tV V)
      have h2 := appLE_inclusion_map (U := W.1.1) (U' := V.1.1 ⊓ W.1.1) hE
        (TopologicalSpace.Opens.infLERight (D.suppIdeal.subschemeι ⁻¹ᵁ V.1.1)
          (D.suppIdeal.subschemeι ⁻¹ᵁ W.1.1))
        (homOfLE (fun x hx => hx.2) : E.1.idealSheaf.subschemeι ⁻¹ᵁ (V.1.1 ⊓ W.1.1) ⟶ _) (tV W)
      refine (h1.trans ?_).trans h2.symm
      rw [htV, htV]
      simp only [sV, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl)
  let t' : Γ(D.suppScheme, D.suppIdeal.subschemeι ⁻¹ᵁ U) := t
  have ht' : ∀ V : {V : X.affineOpens // V.1 ≤ U},
      D.suppScheme.presheaf.map (homOfLE (hle _ V)).op t' = tV V := ht
  refine ⟨t', fun E => ?_⟩
  refine E.1.idealSheaf.subscheme.sheaf.eq_of_locally_eq'
    (fun V : {V : X.affineOpens // V.1 ≤ U} => E.1.idealSheaf.subschemeι ⁻¹ᵁ V.1.1)
    (E.1.idealSheaf.subschemeι ⁻¹ᵁ U) (fun V => homOfLE (hle _ V))
    (le_iSup_preimage_affine _ U) _ _ fun V => ?_
  change E.1.idealSheaf.subscheme.presheaf.map _ _ = E.1.idealSheaf.subscheme.presheaf.map _ _
  rw [← appLE_inclusion_map _ (homOfLE (hle _ V)), ht' V, htV V]

/-- The restriction `J ∩ V ⟶ I ∩ V` of the inclusion of closed subschemes `J ⊆ I`. -/
private noncomputable abbrev res {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J)
    (V : X.Opens) :
    (J.subschemeι ⁻¹ᵁ V).toScheme ⟶ (I.subschemeι ⁻¹ᵁ V).toScheme :=
  (Scheme.IdealSheafData.inclusion h).resLE (I.subschemeι ⁻¹ᵁ V) (J.subschemeι ⁻¹ᵁ V)
    (le_preimage_inclusion _ _)

/-- The restriction `Γ(I, I ∩ V) ⟶ Γ(J, J ∩ V)` along an inclusion of closed subschemes. -/
private noncomputable abbrev resApp {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J)
    (V : X.Opens) :
    Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) ⟶ Γ(J.subscheme, J.subschemeι ⁻¹ᵁ V) :=
  (Scheme.IdealSheafData.inclusion h).appLE (I.subschemeι ⁻¹ᵁ V) (J.subschemeι ⁻¹ᵁ V)
    (le_preimage_inclusion _ _)

/-- Restricting along an inclusion of closed subschemes commutes with shrinking the open. -/
private theorem res_homOfLE {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J)
    {V V' : X.Opens} (e : V' ≤ V) :
    res h V' ≫ I.subscheme.homOfLE (I.subschemeι.preimage_mono e) =
      J.subscheme.homOfLE (J.subschemeι.preimage_mono e) ≫ res h V := by
  dsimp only [res]
  rw [Scheme.Hom.resLE_map, Scheme.Hom.map_resLE]

/-- Every ring map into the global sections comes from a morphism to an affine scheme. -/
private theorem exists_appTop_eq {Y W : Scheme.{u}} [IsAffine W] (Φ : Γ(W, ⊤) ⟶ Γ(Y, ⊤)) :
    ∃ t : Y ⟶ W, t.appTop = Φ := by
  refine ⟨Y.toSpecΓ ≫ Spec.map Φ ≫ W.isoSpec.inv, ?_⟩
  have h : W.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(W, ⊤)).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso Γ(W, ⊤)).hom, Iso.inv_hom_id, ← Scheme.toSpecΓ_appTop]
    change W.isoSpec.inv.appTop ≫ W.isoSpec.hom.appTop = _
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]; rfl
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Category.assoc, h]
  simp

/-- **Gluing morphisms to an affine scheme.** If compatible functions on the `J i ∩ V` glue to
`I ∩ V`, then so do compatible morphisms `J i ∩ V ⟶ W` to an affine scheme. -/
private theorem exists_glue_affine_target {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsReduced I.subscheme] {ι : Type*} {J : ι → X.IdealSheafData} (hJ : ∀ i, I ≤ J i)
    (hcov : (I.support : Set X) ⊆ ⋃ i, ((J i).support : Set X)) (V : X.Opens)
    (hF : ∀ s : ∀ i, Γ((J i).subscheme, (J i).subschemeι ⁻¹ᵁ V),
      (∀ i j, resApp (le_sup_left : J i ≤ J i ⊔ J j) V (s i) =
        resApp (le_sup_right : J j ≤ J i ⊔ J j) V (s j)) →
      ∃ t : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V), ∀ i, resApp (hJ i) V t = s i)
    {W : Scheme.{u}} [IsAffine W] (h : ∀ i, ((J i).subschemeι ⁻¹ᵁ V).toScheme ⟶ W)
    (hh : ∀ i j, res (le_sup_left : J i ≤ J i ⊔ J j) V ≫ h i =
      res (le_sup_right : J j ≤ J i ⊔ J j) V ≫ h j) :
    ∃ t : (I.subschemeι ⁻¹ᵁ V).toScheme ⟶ W, ∀ i, res (hJ i) V ≫ t = h i := by
  let ψ : ∀ i, Γ(W, ⊤) ⟶ Γ((J i).subscheme, (J i).subschemeι ⁻¹ᵁ V) := fun i =>
    (h i).appTop ≫ ((J i).subschemeι ⁻¹ᵁ V).topIso.hom
  have happ : ∀ {K L : X.IdealSheafData} (e : K ≤ L) (g : (K.subschemeι ⁻¹ᵁ V).toScheme ⟶ W),
      (res e V ≫ g).appTop = g.appTop ≫ (K.subschemeι ⁻¹ᵁ V).topIso.hom ≫ resApp e V ≫
        (L.subschemeι ⁻¹ᵁ V).topIso.inv := by
    intro K L e g
    rw [Scheme.Hom.comp_appTop]
    simp only [res, resApp, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  have compat : ∀ a i j, resApp (le_sup_left : J i ≤ J i ⊔ J j) V (ψ i a) =
      resApp (le_sup_right : J j ≤ J i ⊔ J j) V (ψ j a) := by
    intro a i j
    have e := congrArg (fun φ => ((J i ⊔ J j).subschemeι ⁻¹ᵁ V).topIso.hom (φ.hom a))
      (congrArg Scheme.Hom.appTop (hh i j))
    simp only [happ, CommRingCat.comp_apply, Iso.inv_hom_id_apply] at e
    exact e
  choose c hc using fun a => hF (fun i => ψ i a) (compat a)
  have uniq : ∀ t t' : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V),
      (∀ i, resApp (hJ i) V t = resApp (hJ i) V t') → t = t' :=
    appLE_inclusion_injective hJ hcov V
  let cR : Γ(W, ⊤) →+* Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) :=
    { toFun := c
      map_one' := uniq _ _ fun i => by rw [hc, map_one, map_one]
      map_mul' := fun a b => uniq _ _ fun i => by rw [hc, map_mul, map_mul, hc, hc]
      map_zero' := uniq _ _ fun i => by rw [hc, map_zero, map_zero]
      map_add' := fun a b => uniq _ _ fun i => by rw [hc, map_add, map_add, hc, hc] }
  obtain ⟨t, ht⟩ := exists_appTop_eq (CommRingCat.ofHom cR ≫ (I.subschemeι ⁻¹ᵁ V).topIso.inv)
  refine ⟨t, fun i => ext_of_isAffine ?_⟩
  rw [happ, ht]
  ext a
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply, CommRingCat.hom_ofHom]
  change ((J i).subschemeι ⁻¹ᵁ V).topIso.inv (resApp (hJ i) V (c a)) = _
  rw [hc]
  simp only [ψ, CommRingCat.comp_apply, Iso.hom_inv_id_apply]

/-- A point of `L ∩ V` lying over a point of `K ∩ V` is sent to it by the inclusion. -/
private theorem res_apply_eq {X : Scheme.{u}} {K L : X.IdealSheafData} (h : K ≤ L) (V : X.Opens)
    (p : (L.subschemeι ⁻¹ᵁ V).toScheme) (q : (K.subschemeι ⁻¹ᵁ V).toScheme)
    (e : L.subschemeι p.1 = K.subschemeι q.1) : res h V p = q := by
  refine Subtype.ext (K.subschemeι.isEmbedding.injective ?_)
  erw [Scheme.Hom.coe_resLE_apply]
  rw [← Scheme.Hom.comp_apply,
    Scheme.IdealSheafData.inclusion_subschemeι, e]

/-- The open cover of `K ∩ U` by the `K ∩ V a`, for opens `V a ≤ U` covering `K ∩ U`. -/
private noncomputable abbrev coverOfLE {X : Scheme.{u}} (K : X.IdealSheafData) (U : X.Opens)
    {α : Type*} (V : α → X.Opens) (hV : ∀ a, V a ≤ U)
    (h : ∀ x : (K.subschemeι ⁻¹ᵁ U).toScheme, ∃ a, K.subschemeι x.1 ∈ V a) :
    (K.subschemeι ⁻¹ᵁ U).toScheme.OpenCover where
  I₀ := α
  X a := K.subschemeι ⁻¹ᵁ V a
  f a := K.subscheme.homOfLE
    (K.subschemeι.preimage_mono (hV a))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨a, ha⟩ := h x
    exact ⟨a, ⟨x.1, ha⟩, Subtype.ext (Scheme.homOfLE_apply (K.subschemeι.preimage_mono (hV a)) _)⟩

/-- A point of `K.support ∩ U` lifts to `K ∩ U`. -/
private theorem exists_subschemeι_eq {X : Scheme.{u}} (K : X.IdealSheafData) {U : X.Opens}
    {x : X} (hxU : x ∈ U) (hK : x ∈ (K.support : Set X)) :
    ∃ w : (K.subschemeι ⁻¹ᵁ U).toScheme, K.subschemeι w.1 = x := by
  rw [← Scheme.IdealSheafData.range_subschemeι] at hK
  obtain ⟨w, hw⟩ := hK
  exact ⟨⟨w, show K.subschemeι w ∈ U by rw [hw]; exact hxU⟩, hw⟩

/-- Compatible morphisms `J i ∩ U ⟶ Z` agree at points lying over the same point of `X`. -/
private theorem apply_eq_of_subschemeι_eq {X : Scheme.{u}} {ι : Type*}
    {J : ι → X.IdealSheafData} {U : X.Opens} {Z : Scheme.{u}}
    (g : ∀ i, ((J i).subschemeι ⁻¹ᵁ U).toScheme ⟶ Z)
    (hg : ∀ i j, res (le_sup_left : J i ≤ J i ⊔ J j) U ≫ g i =
      res (le_sup_right : J j ≤ J i ⊔ J j) U ≫ g j)
    {i j : ι} (p : ((J i).subschemeι ⁻¹ᵁ U).toScheme) (q : ((J j).subschemeι ⁻¹ᵁ U).toScheme)
    (hpq : (J i).subschemeι p.1 = (J j).subschemeι q.1) : g i p = g j q := by
  have hp : (J i).subschemeι p.1 ∈ ((J i).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨p.1, rfl⟩
  have hq : (J i).subschemeι p.1 ∈ ((J j).support : Set X) := by
    rw [hpq, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨q.1, rfl⟩
  obtain ⟨r, hr⟩ := exists_subschemeι_eq (J i ⊔ J j) (U := U) p.2 (by
    rw [Scheme.IdealSheafData.support_sup]; exact ⟨hp, hq⟩)
  have := congrArg (fun φ => φ r) (hg i j)
  simpa only [Scheme.Hom.comp_apply, res_apply_eq _ U r p hr,
    res_apply_eq _ U r q (hr.trans hpq)] using this

/-- Near a point `x ∈ U` whose lifts all map into `W`, the morphisms `J i ∩ U ⟶ Z` map
`J i ∩ V` into `W` for some open `x ∈ V ≤ U`. -/
private theorem exists_open_mapsTo {X Z : Scheme.{u}} {ι : Type*} [Finite ι]
    {J : ι → X.IdealSheafData} {U : X.Opens} (g : ∀ i, ((J i).subschemeι ⁻¹ᵁ U).toScheme ⟶ Z)
    (W : Z.Opens) {x : X} (hxU : x ∈ U)
    (hxW : ∀ i (w : ((J i).subschemeι ⁻¹ᵁ U).toScheme), (J i).subschemeι w.1 = x → g i w ∈ W) :
    ∃ V : X.Opens, ∃ hVU : V ≤ U, x ∈ V ∧ ∀ i (w : ((J i).subschemeι ⁻¹ᵁ V).toScheme),
      g i ((J i).subscheme.homOfLE ((J i).subschemeι.preimage_mono hVU) w) ∈ W := by
  have hO : ∀ i, ∃ O : Set X, IsOpen O ∧ (J i).subschemeι ⁻¹' O =
      ((J i).subschemeι ⁻¹ᵁ U).ι '' (g i ⁻¹' (W : Set Z)) := fun i =>
    (J i).subschemeι.isEmbedding.isInducing.isOpen_iff.mp
      ((((J i).subschemeι ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap _ (g i ⁻¹ᵁ W).2))
  choose O hOo hO using hO
  let O' : Set X := (U : Set X) ∩ ⋂ i, (O i ∪ ((J i).support : Set X)ᶜ)
  have hO'o : IsOpen O' := U.2.inter (isOpen_iInter_of_finite fun i =>
    (hOo i).union (J i).support.isClosed.isOpen_compl)
  have hxO' : x ∈ O' := by
    refine ⟨hxU, Set.mem_iInter.mpr fun i => ?_⟩
    by_cases hi : x ∈ ((J i).support : Set X)
    · obtain ⟨p, hp⟩ := exists_subschemeι_eq (J i) hxU hi
      left
      rw [← hp]
      change p.1 ∈ (J i).subschemeι ⁻¹' O i
      rw [hO]
      exact ⟨p, hxW i p hp, rfl⟩
    · exact Or.inr hi
  have hVU : (⟨O', hO'o⟩ : X.Opens) ≤ U := fun a ha => ha.1
  refine ⟨⟨O', hO'o⟩, hVU, hxO', fun i w => ?_⟩
  have hw : (J i).subschemeι w.1 ∈ O' := w.2
  have h1 : (J i).subschemeι w.1 ∈ O i := by
    refine (Set.mem_iInter.mp hw.2 i).resolve_right fun hc => hc ?_
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w.1, rfl⟩
  have h2 : w.1 ∈ (J i).subschemeι ⁻¹' O i := h1
  rw [hO] at h2
  obtain ⟨v, hv, hvw⟩ := h2
  have : (J i).subscheme.homOfLE ((J i).subschemeι.preimage_mono hVU) w = v :=
    Subtype.ext (by erw [Scheme.homOfLE_apply]; exact hvw.symm)
  rw [this]; exact hv

/-- **The local step.** Near every point of `I ∩ U`, all the compatible morphisms `J i ∩ U ⟶ Z`
land in a single affine open of `Z`, and there they glue. -/
private theorem exists_local_glue {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsReduced I.subscheme] {ι : Type*} [Finite ι] {J : ι → X.IdealSheafData}
    (hJ : ∀ i, I ≤ J i) (hcov : (I.support : Set X) ⊆ ⋃ i, ((J i).support : Set X))
    (U : X.Opens)
    (hF : ∀ V ≤ U, ∀ s : ∀ i, Γ((J i).subscheme, (J i).subschemeι ⁻¹ᵁ V),
      (∀ i j, resApp (le_sup_left : J i ≤ J i ⊔ J j) V (s i) =
        resApp (le_sup_right : J j ≤ J i ⊔ J j) V (s j)) →
      ∃ t : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V), ∀ i, resApp (hJ i) V t = s i)
    {Z : Scheme.{u}} (g : ∀ i, ((J i).subschemeι ⁻¹ᵁ U).toScheme ⟶ Z)
    (hg : ∀ i j, res (le_sup_left : J i ≤ J i ⊔ J j) U ≫ g i =
      res (le_sup_right : J j ≤ J i ⊔ J j) U ≫ g j)
    (y : (I.subschemeι ⁻¹ᵁ U).toScheme) :
    ∃ V : X.Opens, ∃ hVU : V ≤ U, I.subschemeι y.1 ∈ V ∧
      ∃ tV : (I.subschemeι ⁻¹ᵁ V).toScheme ⟶ Z, ∀ i, res (hJ i) V ≫ tV =
        (J i).subscheme.homOfLE ((J i).subschemeι.preimage_mono hVU) ≫ g i := by
  set x := I.subschemeι y.1
  have hxU : x ∈ U := y.2
  obtain ⟨i0, hi0⟩ : ∃ i0, x ∈ ((J i0).support : Set X) := by
    have hxI : x ∈ (I.support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y.1, rfl⟩
    exact Set.mem_iUnion.mp (hcov hxI)
  obtain ⟨p0, hp0⟩ := exists_subschemeι_eq (J i0) hxU hi0
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g i0 p0)) isOpen_univ
  obtain ⟨V, hVU, hxV, hland⟩ := exists_open_mapsTo g W hxU fun i w hw => by
    rw [apply_eq_of_subschemeι_eq g hg w p0 (hw.trans hp0.symm)]; exact hzW
  have : IsAffine W := hW
  let h : ∀ i, ((J i).subschemeι ⁻¹ᵁ V).toScheme ⟶ W := fun i =>
    IsOpenImmersion.lift (Scheme.Opens.ι W)
      ((J i).subscheme.homOfLE ((J i).subschemeι.preimage_mono hVU) ≫ g i)
      (Set.range_subset_iff.mpr fun w => by
        rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]; exact hland i w)
  obtain ⟨tW, htW⟩ := exists_glue_affine_target hJ hcov V (hF V hVU) h (fun i j => by
    rw [← cancel_mono (Scheme.Opens.ι W)]
    simp only [Category.assoc, h, IsOpenImmersion.lift_fac]
    rw [← Category.assoc, res_homOfLE (le_sup_left : J i ≤ J i ⊔ J j) hVU, Category.assoc, hg,
      ← Category.assoc, ← res_homOfLE (le_sup_right : J j ≤ J i ⊔ J j) hVU, Category.assoc])
  refine ⟨V, hVU, hxV, tW ≫ (Scheme.Opens.ι W), fun i => ?_⟩
  rw [← Category.assoc, htW, IsOpenImmersion.lift_fac]

/-- Local morphisms `I ∩ V a ⟶ Z` restricting to the given `g i` agree on the overlaps of the
cover `coverOfLE`. -/
private theorem coverOfLE_pullback_compat {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsReduced I.subscheme] {ι : Type*} {J : ι → X.IdealSheafData}
    (hJ : ∀ i, I ≤ J i) (hcov : (I.support : Set X) ⊆ ⋃ i, ((J i).support : Set X))
    {U : X.Opens} {Z : Scheme.{u}} (g : ∀ i, ((J i).subschemeι ⁻¹ᵁ U).toScheme ⟶ Z)
    (V : (I.subschemeι ⁻¹ᵁ U).toScheme → X.Opens) (hVU : ∀ a, V a ≤ U)
    (hyV : ∀ a : (I.subschemeι ⁻¹ᵁ U).toScheme, I.subschemeι a.1 ∈ V a)
    (tV : ∀ a, (I.subschemeι ⁻¹ᵁ V a).toScheme ⟶ Z)
    (htV : ∀ a i, res (hJ i) (V a) ≫ tV a =
      (J i).subscheme.homOfLE ((J i).subschemeι.preimage_mono (hVU a)) ≫ g i)
    (a b : (I.subschemeι ⁻¹ᵁ U).toScheme) :
    let 𝒰 := coverOfLE I U V hVU fun y => ⟨y, hyV y⟩
    Limits.pullback.fst (𝒰.f a) (𝒰.f b) ≫ tV a = Limits.pullback.snd _ _ ≫ tV b := by
  intro 𝒰
  have hinf : I.subscheme.homOfLE (I.subschemeι.preimage_mono inf_le_left) ≫ tV a =
      I.subscheme.homOfLE (I.subschemeι.preimage_mono inf_le_right) ≫ tV b := by
    refine hom_ext_of_isReduced (fun i => res (hJ i) (V a ⊓ V b))
      (fun y => exists_resLE_inclusion_eq hJ hcov _ y) _ _ fun i => ?_
    have key : ∀ (c : (I.subschemeι ⁻¹ᵁ U).toScheme) (hc : V a ⊓ V b ≤ V c),
        res (hJ i) (V a ⊓ V b) ≫ I.subscheme.homOfLE (I.subschemeι.preimage_mono hc) ≫ tV c =
          (J i).subscheme.homOfLE ((J i).subschemeι.preimage_mono (hc.trans (hVU c))) ≫
            g i := by
      intro c hc
      rw [← Category.assoc, res_homOfLE (hJ i) hc, Category.assoc, htV,
        Scheme.homOfLE_homOfLE_assoc]
    exact (key a inf_le_left).trans (key b inf_le_right).symm
  have hrange : Set.range (Limits.pullback.fst (𝒰.f a) (𝒰.f b) ≫ 𝒰.f a) ⊆
      Set.range (I.subscheme.homOfLE (I.subschemeι.preimage_mono
        ((inf_le_left : V a ⊓ V b ≤ V a).trans (hVU a)))) := by
    rintro _ ⟨p, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
    refine ⟨?_, ?_⟩
    · change I.subschemeι ((Limits.pullback.fst (𝒰.f a) (𝒰.f b) ≫ 𝒰.f a) p).1 ∈ V a
      rw [Scheme.Hom.comp_apply]
      erw [Scheme.homOfLE_apply (I.subschemeι.preimage_mono (hVU a))]
      exact (Limits.pullback.fst (𝒰.f a) (𝒰.f b) p).2
    · change I.subschemeι ((Limits.pullback.fst (𝒰.f a) (𝒰.f b) ≫ 𝒰.f a) p).1 ∈ V b
      rw [Limits.pullback.condition, Scheme.Hom.comp_apply]
      erw [Scheme.homOfLE_apply (I.subschemeι.preimage_mono (hVU b))]
      exact (Limits.pullback.snd (𝒰.f a) (𝒰.f b) p).2
  let q := IsOpenImmersion.lift _ _ hrange
  have hq1 : q ≫ I.subscheme.homOfLE (I.subschemeι.preimage_mono inf_le_left) =
      Limits.pullback.fst _ _ := by
    rw [← cancel_mono (𝒰.f a), ← IsOpenImmersion.lift_fac _ _ hrange, Category.assoc]
    simp only [𝒰, coverOfLE, Scheme.homOfLE_homOfLE]
    rfl
  have hq2 : q ≫ I.subscheme.homOfLE (I.subschemeι.preimage_mono inf_le_right) =
      Limits.pullback.snd _ _ := by
    rw [← cancel_mono (𝒰.f b), ← Limits.pullback.condition, ← IsOpenImmersion.lift_fac _ _ hrange,
      Category.assoc]
    simp only [𝒰, coverOfLE, Scheme.homOfLE_homOfLE]
    rfl
  rw [← hq1, ← hq2, Category.assoc, Category.assoc, hinf]

/-- **Gluing morphisms along a finite closed cover.** If compatible functions glue on every
`I ∩ V`, `V ≤ U`, then compatible morphisms `J i ∩ U ⟶ Z` glue to `I ∩ U`. -/
private theorem exists_glue_hom {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsReduced I.subscheme] {ι : Type*} [Finite ι] {J : ι → X.IdealSheafData}
    (hJ : ∀ i, I ≤ J i) (hcov : (I.support : Set X) ⊆ ⋃ i, ((J i).support : Set X))
    (U : X.Opens)
    (hF : ∀ V ≤ U, ∀ s : ∀ i, Γ((J i).subscheme, (J i).subschemeι ⁻¹ᵁ V),
      (∀ i j, resApp (le_sup_left : J i ≤ J i ⊔ J j) V (s i) =
        resApp (le_sup_right : J j ≤ J i ⊔ J j) V (s j)) →
      ∃ t : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V), ∀ i, resApp (hJ i) V t = s i)
    {Z : Scheme.{u}} (g : ∀ i, ((J i).subschemeι ⁻¹ᵁ U).toScheme ⟶ Z)
    (hg : ∀ i j, res (le_sup_left : J i ≤ J i ⊔ J j) U ≫ g i =
      res (le_sup_right : J j ≤ J i ⊔ J j) U ≫ g j) :
    ∃ t : (I.subschemeι ⁻¹ᵁ U).toScheme ⟶ Z, ∀ i, res (hJ i) U ≫ t = g i := by
  choose V hVU hyV tV htV using exists_local_glue hJ hcov U hF g hg
  let 𝒰 := coverOfLE I U V hVU fun y => ⟨y, hyV y⟩
  have hcompat : ∀ a b : (I.subschemeι ⁻¹ᵁ U).toScheme,
      Limits.pullback.fst (𝒰.f a) (𝒰.f b) ≫ tV a = Limits.pullback.snd _ _ ≫ tV b :=
    coverOfLE_pullback_compat hJ hcov g V hVU hyV tV htV
  refine ⟨𝒰.glueMorphisms tV hcompat, fun i => ?_⟩
  have hmem : ∀ w : ((J i).subschemeι ⁻¹ᵁ U).toScheme, ∃ a, (J i).subschemeι w.1 ∈ V a := by
    intro w
    refine ⟨res (hJ i) U w, ?_⟩
    have := hyV (res (hJ i) U w)
    erw [Scheme.Hom.coe_resLE_apply] at this
    rwa [← Scheme.Hom.comp_apply,
      Scheme.IdealSheafData.inclusion_subschemeι] at this
  refine (coverOfLE (J i) U V hVU hmem).hom_ext _ _ fun a => ?_
  calc (J i).subscheme.homOfLE ((J i).subschemeι.preimage_mono (hVU a)) ≫ res (hJ i) U ≫
        𝒰.glueMorphisms tV hcompat
      = res (hJ i) (V a) ≫ 𝒰.f a ≫ 𝒰.glueMorphisms tV hcompat := by
        rw [← Category.assoc, ← res_homOfLE (hJ i) (hVU a), Category.assoc]
    _ = (J i).subscheme.homOfLE ((J i).subschemeι.preimage_mono (hVU a)) ≫ g i := by
        rw [𝒰.ι_glueMorphisms tV hcompat a, htV a i]

/-- **Gluing along the components of an SNC divisor.** Let `D` be a reduced simple normal
crossing divisor on a smooth variety `X` over a field `k`, with support `F` and components the
prime divisors `E ∈ D.support`. Over every open `U ⊆ X`:

* regular functions on the `E ∩ U` which agree on every scheme-theoretic intersection
  `(E ∩ E') ∩ U` are the restrictions of a unique regular function on `F ∩ U`;
* for every scheme `Z`, morphisms `E ∩ U ⟶ Z` which agree on every `(E ∩ E') ∩ U` are the
  restrictions of a unique morphism `F ∩ U ⟶ Z`. -/
@[mmp "lem_mmp_lc_bpf_snc_closed_gluing"]
public theorem IsSNCDivisor.existsUnique_glue {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} [Smooth f] (hX : MMP.Mori.IsVariety k f) {D : Divisor X}
    (hD : IsSNCDivisor f D) (U : X.Opens) :
    (∀ s : ∀ E : D.support, Γ(E.1.idealSheaf.subscheme, E.1.idealSheaf.subschemeι ⁻¹ᵁ U),
      (∀ E E' : D.support,
        (Scheme.IdealSheafData.inclusion le_sup_left).appLE
            (E.1.idealSheaf.subschemeι ⁻¹ᵁ U) ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ U)
            (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])
            (s E) =
          (Scheme.IdealSheafData.inclusion le_sup_right).appLE
            (E'.1.idealSheaf.subschemeι ⁻¹ᵁ U) ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ U)
            (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])
            (s E')) →
      ∃! t : Γ(D.suppScheme, D.suppIdeal.subschemeι ⁻¹ᵁ U), ∀ E : D.support,
        (Scheme.IdealSheafData.inclusion
            ((suppIdeal_eq_finsetInf D).le.trans (Finset.inf_le E.2))).appLE
          (D.suppIdeal.subschemeι ⁻¹ᵁ U) (E.1.idealSheaf.subschemeι ⁻¹ᵁ U)
          (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]) t =
          s E) ∧
    ∀ (Z : Scheme.{u})
      (g : ∀ E : D.support, (E.1.idealSheaf.subschemeι ⁻¹ᵁ U).toScheme ⟶ Z),
      (∀ E E' : D.support,
        (Scheme.IdealSheafData.inclusion le_sup_left).resLE
            (E.1.idealSheaf.subschemeι ⁻¹ᵁ U) ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ U)
            (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]) ≫
            g E =
          (Scheme.IdealSheafData.inclusion le_sup_right).resLE
            (E'.1.idealSheaf.subschemeι ⁻¹ᵁ U) ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ U)
            (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]) ≫
            g E') →
      ∃! t : (D.suppIdeal.subschemeι ⁻¹ᵁ U).toScheme ⟶ Z, ∀ E : D.support,
        (Scheme.IdealSheafData.inclusion
            ((suppIdeal_eq_finsetInf D).le.trans (Finset.inf_le E.2))).resLE
          (D.suppIdeal.subschemeι ⁻¹ᵁ U) (E.1.idealSheaf.subschemeι ⁻¹ᵁ U)
          (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]) ≫ t =
          g E := by
  have := isReduced_suppScheme D
  have hcov := support_suppIdeal_subset_iUnion D
  refine ⟨fun s hs => ?_, fun Z g hg => ?_⟩
  · obtain ⟨t, ht⟩ := exists_glue_functions hD U s hs
    exact ⟨t, ht, fun t' ht' => appLE_inclusion_injective (J := fun E : D.support => E.1.idealSheaf)
      suppIdeal_le hcov U t' t fun E => (ht' E).trans (ht E).symm⟩
  · obtain ⟨t, ht⟩ := exists_glue_hom (J := fun E : D.support => E.1.idealSheaf) suppIdeal_le
      hcov U (fun V _ s hs => exists_glue_functions hD V s hs) g hg
    exact ⟨t, ht, fun t' ht' => hom_ext_of_isReduced _
      (exists_resLE_inclusion_eq (J := fun E : D.support => E.1.idealSheaf) _ hcov U)
      t' t fun E => (ht' E).trans (ht E).symm⟩

end MMP.Intersection
