module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralTranslateProper
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyLocallyClosed
public import StacksFrontier.Topology.Dimension.UnionDimension

/-!
# General linear sections of constructible subsets of projective space

Let `k` be an algebraically closed field of characteristic zero and `ℙ = 𝐏(k^ι)` the projective
space whose linear forms are the vectors of `k^ι` (so `ℙ = ℙᴺ_k` for `|ι| = N + 1`). For finitely
many constructible subsets `W_u ⊆ ℙ` and `c ≥ 0`, a general ordered `c`-tuple of hyperplanes
`H_1, …, H_c` cuts each `W_u` in the expected dimension: the cut `W_u ∩ H_1 ∩ ⋯ ∩ H_c` is empty
when `c > dim W_u`, and otherwise nonempty of dimension `dim W_u - c`.

## Main results

* `MMP.exists_ne_zero_forall_eval_ne_zero_inter_hyperplanes`: the cut has the expected
  dimension off the zero set of a nonzero polynomial in the coefficients of the `c` linear forms.

## Implementation notes

The parameter space of `c` ordered hyperplanes `((ℙᴺ)^∨)^c` is represented through its affine
cone: a tuple of hyperplanes is a tuple `f : Fin c → ι → k` of linear forms, and "a dense open
subset of the parameter space" is the complement of the zero set of a nonzero polynomial
`P` in the `c · |ι|` coefficients. Over the infinite field `k` such a set is a nonempty, hence
dense, Zariski open of the affine space of coefficients, and its image in `((ℙᴺ)^∨)^c` is a dense
open; conversely every dense open of `((ℙᴺ)^∨)^c` pulls back to an open containing such a set. The
hyperplane of a form `f_i` is `AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace k _
(k ∙ f_i)`; the zero form, which cuts out all of `ℙ`, is excluded by `P` itself.

Dimensions are `topologicalKrullDim` of the subspaces, valued in `WithBot ℕ∞`, and
`dim (cut) = dim W - c` is stated additively, `dim (cut) + c = dim W`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

namespace MMP

section

variable {k : Type u} [Field k] {ι : Type u} [Fintype ι]

private theorem exists_nat_of_add_one_eq (x : WithBot ℕ∞) (q : ℕ) (h : x + 1 = (q : WithBot ℕ∞)) :
    ∃ m : ℕ, x = m ∧ m + 1 = q := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = (⊤ : ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add]
        simp
      rw [this] at h
      exact absurd h (by exact_mod_cast ENat.top_ne_coe q)
    | coe m =>
      refine ⟨m, rfl, ?_⟩
      have : ((m : ℕ∞) : WithBot ℕ∞) + 1 = ((m + 1 : ℕ) : WithBot ℕ∞) := by
        push_cast
        rfl
      rw [this] at h
      exact_mod_cast h

private abbrev cutSet {c : ℕ}
    (f : Fin c → ι → k) : Set (projectiveSpaceOfModule k (ι → k)) :=
  ⋂ i, linearSubspace k (ι → k) (k ∙ f i)

private theorem cutSet_eq {c : ℕ}
    (f : Fin c → ι → k) :
    cutSet f = linearSubspace k (ι → k) (Submodule.span k (Set.range f)) := by
  ext q
  simp only [cutSet, Set.mem_iInter, mem_linearSubspace_iff, Submodule.span_singleton_le_iff_mem,
    Submodule.span_le, Set.range_subset_iff, SetLike.mem_coe, Set.singleton_subset_iff]

private theorem isClosed_cutSet {c : ℕ}
    (f : Fin c → ι → k) : IsClosed (cutSet f) :=
  isClosed_iInter fun i => isClosed_linearSubspace k _ _

private theorem span_range_ne_top {c : ℕ}
    (f : Fin c → ι → k) (hc : c < Fintype.card ι) :
    Submodule.span k (Set.range f) ≠ ⊤ := by
  intro h
  have h1 := finrank_range_le_card (R := k) f
  simp only [Set.finrank] at h1
  rw [h, finrank_top, Module.finrank_pi] at h1
  simp at h1
  omega

/-- A cut by `c` forms has dimension at least `card ι - 1 - c`. -/
private theorem le_dim_cutSet_add {c : ℕ}
    (f : Fin c → ι → k) (hc : c < Fintype.card ι) :
    ((Fintype.card ι - 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥(cutSet f) + c := by
  rw [cutSet_eq]
  obtain ⟨m, hm, hm1⟩ := exists_nat_of_add_one_eq _ _
    (topologicalKrullDim_linearSubspace_add_one (span_range_ne_top f hc))
  rw [hm]
  have h1 := finrank_range_le_card (R := k) f
  simp only [Set.finrank] at h1
  have h2 := Submodule.finrank_quotient_add_finrank (Submodule.span k (Set.range f))
  rw [Module.finrank_pi] at h2
  simp at h1 h2
  exact_mod_cast (by omega : Fintype.card ι - 1 ≤ m + c)

section Generic

variable {X : Type*} [TopologicalSpace X]

private theorem topologicalKrullDim_emptySet : topologicalKrullDim ↥(∅ : Set X) = ⊥ := by
  rw [topologicalKrullDim_eq_bot_iff_isEmpty]
  exact Set.isEmpty_coe_sort.mpr rfl

private theorem dim_add_le_of_subset_biUnion [QuasiSober X] {ι' : Type*} (t : Finset ι')
    {S : Set X} {A : ι' → Set X} (hA : ∀ i, IsClosed (A i)) (hSA : S ⊆ ⋃ i ∈ t, A i) {c : ℕ}
    {D : WithBot ℕ∞} (hc : ∀ i ∈ t, topologicalKrullDim ↥(A i) + c ≤ D) :
    topologicalKrullDim ↥S + c ≤ D := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | ht
  · obtain rfl : S = ∅ := by simpa using hSA
    simp [topologicalKrullDim_emptySet]
  · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup t ht (fun i => topologicalKrullDim ↥(A i))
    have h1 : topologicalKrullDim ↥S ≤ t.sup (fun i => topologicalKrullDim ↥(A i)) :=
      (topologicalKrullDim_le_of_subset hSA).trans
        (topologicalKrullDim_biUnion_le t hA
          (fun i hi => Finset.le_sup (f := fun i => topologicalKrullDim ↥(A i)) hi))
    calc topologicalKrullDim ↥S + c ≤ t.sup (fun i => topologicalKrullDim ↥(A i)) + c := by
          gcongr
      _ = topologicalKrullDim ↥(A a) + c := by rw [hsup]
      _ ≤ D := hc a ha

/-- A finite union of locally closed sets, given by pairs (open, closed). -/
private def Rep (S : Set X) : Prop :=
  ∃ t : Finset (Set X × Set X), (∀ q ∈ t, IsOpen q.1 ∧ IsClosed q.2) ∧ S = ⋃ q ∈ t, q.2 ∩ q.1

private theorem Rep.union {S T : Set X} (hS : Rep S) (hT : Rep T) : Rep (S ∪ T) := by
  classical
  obtain ⟨t, ht, rfl⟩ := hS
  obtain ⟨u, hu, rfl⟩ := hT
  exact ⟨t ∪ u, fun q hq => (Finset.mem_union.mp hq).elim (ht q) (hu q),
    by rw [Finset.set_biUnion_union]⟩

private theorem Rep.inter {S T : Set X} (hS : Rep S) (hT : Rep T) : Rep (S ∩ T) := by
  classical
  obtain ⟨t, ht, rfl⟩ := hS
  obtain ⟨u, hu, rfl⟩ := hT
  refine ⟨(t ×ˢ u).image fun r => (r.1.1 ∩ r.2.1, r.1.2 ∩ r.2.2), fun q hq => ?_, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hr
    exact ⟨(ht _ h1).1.inter (hu _ h2).1, (ht _ h1).2.inter (hu _ h2).2⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_image, Finset.mem_product,
      exists_prop]
    constructor
    · rintro ⟨⟨q, hq, hx⟩, ⟨q', hq', hx'⟩⟩
      exact ⟨_, ⟨(q, q'), ⟨hq, hq'⟩, rfl⟩, ⟨hx.1, hx'.1⟩, hx.2, hx'.2⟩
    · rintro ⟨_, ⟨⟨q, q'⟩, ⟨hq, hq'⟩, rfl⟩, ⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨q, hq, h1, h3⟩, ⟨q', hq', h2, h4⟩⟩

private theorem Rep.univ : Rep (Set.univ : Set X) :=
  ⟨{(Set.univ, Set.univ)}, by simp, by simp⟩

private theorem rep_compl_single {O Z : Set X} (hO : IsOpen O) (hZ : IsClosed Z) :
    Rep ((Z ∩ O)ᶜ) := by
  classical
  refine ⟨{(Set.univ, Oᶜ), (Zᶜ, Set.univ)}, ?_, ?_⟩
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact ⟨isOpen_univ, hO.isClosed_compl⟩
    · exact ⟨hZ.isOpen_compl, isClosed_univ⟩
  · ext x
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_insert,
      Finset.mem_singleton, exists_prop, not_and_or]
    constructor
    · rintro (h | h)
      · exact ⟨_, Or.inr rfl, trivial, h⟩
      · exact ⟨_, Or.inl rfl, h, trivial⟩
    · rintro ⟨q, rfl | rfl, h1, h2⟩
      · exact Or.inr h1
      · exact Or.inl h2

private theorem Rep.compl_of_finset (t : Finset (Set X × Set X))
    (ht : ∀ q ∈ t, IsOpen q.1 ∧ IsClosed q.2) : Rep ((⋃ q ∈ t, q.2 ∩ q.1)ᶜ) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (Rep.univ (X := X))
  | insert q t hq ih =>
    have h1 := ht q (Finset.mem_insert_self _ _)
    rw [Finset.set_biUnion_insert, Set.compl_union]
    exact (rep_compl_single h1.1 h1.2).inter
      (ih fun q' hq' => ht q' (Finset.mem_insert_of_mem hq'))

private theorem Rep.compl {S : Set X} (hS : Rep S) : Rep Sᶜ := by
  obtain ⟨t, ht, rfl⟩ := hS
  exact Rep.compl_of_finset t ht

private theorem exists_pieces [TopologicalSpace.NoetherianSpace X] {W : Set X}
    (hW : Topology.IsConstructible W) :
    ∃ s : Finset (Set X × Set X),
      (∀ p ∈ s, IsOpen p.1 ∧ IsClosed p.2 ∧ IsIrreducible p.2 ∧ (p.2 ∩ p.1).Nonempty) ∧
      W = ⋃ p ∈ s, p.2 ∩ p.1 := by
  classical
  obtain ⟨t, ht, rfl⟩ : Rep W :=
    Topology.IsConstructible.empty_union_induction (p := fun S _ => Rep S)
      (fun U hU _ => ⟨{(U, Set.univ)}, by simpa using hU, by simp⟩)
      (fun _ _ _ _ hs ht => hs.union ht) (fun _ _ hs => hs.compl) hW
  have key : ∀ q : Set X × Set X, ∃ S : Set (Set X), IsClosed q.2 →
      (S.Finite ∧ (∀ z ∈ S, IsClosed z) ∧ (∀ z ∈ S, IsIrreducible z) ∧ q.2 = ⋃₀ S) := by
    intro q
    by_cases h : IsClosed q.2
    · obtain ⟨S, h1, h2, h3, h4⟩ :=
        TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible h
      exact ⟨S, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose S hS using key
  let s' : Set (Set X × Set X) :=
    {p | ∃ q ∈ t, p.1 = q.1 ∧ p.2 ∈ S q ∧ (p.2 ∩ p.1).Nonempty}
  have hfin : s'.Finite := by
    refine (Set.Finite.biUnion t.finite_toSet fun q hq =>
      ((hS q (ht q hq).2).1.image fun z => (q.1, z))).subset ?_
    rintro p ⟨q, hq, h1, h2, -⟩
    exact Set.mem_biUnion hq ⟨p.2, h2, by rw [← h1]⟩
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, h1, h2, h3⟩ := hfin.mem_toFinset.mp hp
    exact ⟨h1 ▸ (ht q hq).1, (hS q (ht q hq).2).2.1 _ h2, (hS q (ht q hq).2).2.2.1 _ h2, h3⟩
  · ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨q, hq, hx2, hx1⟩
      rw [(hS q (ht q hq).2).2.2.2] at hx2
      obtain ⟨z, hz, hxz⟩ := hx2
      exact ⟨(q.1, z), hfin.mem_toFinset.mpr ⟨q, hq, rfl, hz, ⟨x, hxz, hx1⟩⟩, hxz, hx1⟩
    · rintro ⟨p, hp, hx2, hx1⟩
      obtain ⟨q, hq, h1, h2, -⟩ := hfin.mem_toFinset.mp hp
      refine ⟨q, hq, ?_, h1 ▸ hx1⟩
      rw [(hS q (ht q hq).2).2.2.2]
      exact ⟨p.2, h2, hx2⟩

end Generic

private theorem exists_nat_eq_of_le_of_ne_bot {x : WithBot ℕ∞} {n : ℕ} (hx : x ≤ n) (hb : x ≠ ⊥) :
    ∃ r : ℕ, x = r := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl hb
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hx
      have := WithBot.coe_le_coe.mp this
      exact absurd this (by simp)
    | coe m => exact ⟨m, rfl⟩

private theorem lt_of_add_add_one_le_add {x : WithBot ℕ∞} {m c : ℕ} (h : x + c + 1 ≤ m + c) :
    x < m := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + c + 1 = (⊤ : ℕ∞) := by
        rw [← WithBot.coe_natCast, ← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_add]
        simp
      rw [this] at h
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((m + c : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have := WithBot.coe_le_coe.mp h2
      exact absurd this (by simp)
    | coe a =>
      have : ((a : ℕ∞) : WithBot ℕ∞) + c + 1 = ((a + c + 1 : ℕ) : WithBot ℕ∞) := by
        push_cast; rfl
      rw [this] at h
      have h' : a + c + 1 ≤ m + c := by exact_mod_cast h
      exact_mod_cast (by omega : a < m)

private theorem noetherianSpace_projectiveSpaceOfModule {K V : Type u} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] :
    TopologicalSpace.NoetherianSpace (projectiveSpaceOfModule K V) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : IsEmpty (projectiveSpaceOfModule K V) := ⟨fun x => by
      obtain ⟨v, hv⟩ := exists_ι_notMem K V x
      exact hv (by rw [Subsingleton.elim v 0]; simp)⟩
    haveI : Finite (projectiveSpaceOfModule K V) := Finite.of_subsingleton
    exact TopologicalSpace.Finite.to_noetherianSpace
  have := isProper_projectiveSpaceOfModuleToSpec K V
  infer_instance

private theorem noetherianSpace_projectiveSpace :
    TopologicalSpace.NoetherianSpace (projectiveSpaceOfModule k (ι → k)) :=
  noetherianSpace_projectiveSpaceOfModule (V := ι → k)

private theorem exists_card_eq_succ {Z : Set (projectiveSpaceOfModule k (ι → k))}
    (hZ : Z.Nonempty) :
    ∃ n : ℕ, Fintype.card ι = n + 1 := by
  obtain ⟨q, -⟩ := hZ
  obtain ⟨v, hv⟩ := exists_ι_notMem k (ι → k) q
  have hv0 : v ≠ 0 := by rintro rfl; exact hv (by simp)
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hv0 (Subsingleton.elim _ _)
  exact ⟨Fintype.card ι - 1, by have := Fintype.card_pos (α := ι); omega⟩

private theorem topologicalKrullDim_projectiveSpace {n : ℕ} (hn : Fintype.card ι = n + 1) :
    topologicalKrullDim (projectiveSpaceOfModule k (ι → k)) = (n : WithBot ℕ∞) :=
  topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (by simpa using hn)

private theorem exists_nat_dim {n : ℕ} (hn : Fintype.card ι = n + 1)
    {S : Set (projectiveSpaceOfModule k (ι → k))} (hS : S.Nonempty) :
    ∃ r : ℕ, topologicalKrullDim ↥S = r := by
  have hb : topologicalKrullDim ↥S ≠ ⊥ := by
    rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
    obtain ⟨x, hx⟩ := hS
    exact fun h => h.false ⟨x, hx⟩
  have hle : topologicalKrullDim ↥S ≤ n := by
    rw [← topologicalKrullDim_projectiveSpace (k := k) hn]
    exact topologicalKrullDim_subspace_le _ S
  exact exists_nat_eq_of_le_of_ne_bot hle hb

/-- A closed irreducible `Z` meeting the open `O` has boundary `Z ∩ Oᶜ` of strictly smaller
dimension. -/
private theorem dim_inter_compl_add_one_le {Z O : Set (projectiveSpaceOfModule k (ι → k))}
    (hZ : IsClosed Z) (hZi : IsIrreducible Z) (hO : IsOpen O) (hne : (Z ∩ O).Nonempty) :
    topologicalKrullDim ↥(Z ∩ Oᶜ) + 1 ≤ topologicalKrullDim ↥Z := by
  haveI := noetherianSpace_projectiveSpace (k := k) (ι := ι)
  haveI : IrreducibleSpace ↥Z := Subtype.irreducibleSpace hZi
  have hcl : IsClosed ((Subtype.val : Z → _) ⁻¹' (Z ∩ Oᶜ)) :=
    (hZ.inter hO.isClosed_compl).preimage continuous_subtype_val
  have hne' : ((Subtype.val : Z → _) ⁻¹' (Z ∩ Oᶜ)) ≠ Set.univ := by
    intro h
    obtain ⟨x, hxZ, hxO⟩ := hne
    have : (⟨x, hxZ⟩ : Z) ∈ ((Subtype.val : Z → _) ⁻¹' (Z ∩ Oᶜ)) := by rw [h]; trivial
    exact this.2 hxO
  have := Topology.topologicalKrullDim_add_one_le_of_ne_univ hcl hne'
  rwa [topologicalKrullDim_preimage_val Z (Z ∩ Oᶜ) Set.inter_subset_left] at this

/-- A nonempty closed subset of projective space contains an irreducible closed subset of the same
dimension. -/
private theorem exists_isIrreducible_subset_dim_le {S : Set (projectiveSpaceOfModule k (ι → k))}
    (hS : IsClosed S) (hSne : S.Nonempty) :
    ∃ C, IsClosed C ∧ IsIrreducible C ∧ C ⊆ S ∧
      topologicalKrullDim ↥S ≤ topologicalKrullDim ↥C := by
  classical
  haveI := noetherianSpace_projectiveSpace (k := k) (ι := ι)
  obtain ⟨T, hTfin, hTc, hTi, hTeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  haveI : Fintype ↥T := hTfin.fintype
  have hTne : Nonempty ↥T := by
    obtain ⟨x, hx⟩ := hSne
    rw [hTeq] at hx
    obtain ⟨C, hC, -⟩ := hx
    exact ⟨⟨C, hC⟩⟩
  have hSsub : S ⊆ ⋃ C ∈ (Finset.univ : Finset ↥T), C.1 := by
    intro x hx
    rw [hTeq] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    exact Set.mem_biUnion (Finset.mem_univ ⟨C, hC⟩) hxC
  obtain ⟨C, -, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ↥T)
    Finset.univ_nonempty (fun C : ↥T => topologicalKrullDim ↥C.1)
  refine ⟨C.1, hTc _ C.2, hTi _ C.2, fun x hx => by rw [hTeq]; exact ⟨C, C.2, hx⟩, ?_⟩
  refine (topologicalKrullDim_le_of_subset hSsub).trans
    (topologicalKrullDim_biUnion_le (Finset.univ : Finset ↥T)
      (A := fun C : ↥T => C.1) (fun C => hTc C C.2) fun D _ => ?_)
  rw [← hsup]
  exact Finset.le_sup (f := fun C : ↥T => topologicalKrullDim ↥C.1) (Finset.mem_univ D)

/-- The projective dimension theorem for a linear cut: a closed `Z` of dimension at least `c` meets
the cut by `c` forms, in dimension at least `dim Z - c`. -/
private theorem nonempty_inter_cutSet_and_dim_le [IsAlgClosed k]
    {Z : Set (projectiveSpaceOfModule k (ι → k))} (hZ : IsClosed Z) (hZne : Z.Nonempty)
    {c : ℕ} (f : Fin c → ι → k) (hc : (c : WithBot ℕ∞) ≤ topologicalKrullDim ↥Z) :
    (Z ∩ cutSet f).Nonempty ∧
      topologicalKrullDim ↥Z ≤ topologicalKrullDim ↥(Z ∩ cutSet f) + c := by
  classical
  haveI := noetherianSpace_projectiveSpace (k := k) (ι := ι)
  obtain ⟨n, hn⟩ := exists_card_eq_succ (k := k) hZne
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hdimP := topologicalKrullDim_projectiveSpace (k := k) hn
  obtain ⟨d, hd⟩ := exists_nat_dim (k := k) hn hZne
  have hcd : c ≤ d := by rw [hd] at hc; exact_mod_cast hc
  have hdn : d ≤ n := by
    have : topologicalKrullDim ↥Z ≤ n := by
      rw [← hdimP]; exact topologicalKrullDim_subspace_le _ _
    rw [hd] at this; exact_mod_cast this
  have hcard : c < Fintype.card ι := by omega
  have hLc : IsClosed (cutSet f) := isClosed_cutSet f
  have hLd := le_dim_cutSet_add f hcard
  have hLne : (cutSet f).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, topologicalKrullDim_emptySet] at hLd
    simp at hLd
  obtain ⟨l, hl⟩ := exists_nat_dim (k := k) hn hLne
  have hnl : n ≤ l + c := by
    rw [hl] at hLd
    have : Fintype.card ι - 1 = n := by omega
    rw [this] at hLd
    exact_mod_cast hLd
  have hle : topologicalKrullDim (projectiveSpaceOfModule k (ι → k)) ≤
      topologicalKrullDim ↥Z + topologicalKrullDim ↥(cutSet f) := by
    rw [hdimP, hd, hl]; exact_mod_cast (by omega : n ≤ d + l)
  have hSne : (Z ∩ cutSet f).Nonempty :=
    nonempty_inter_projectiveSpaceOfModule hZ hLc hZne hLne hle
  have hdim := add_le_topologicalKrullDim_inter_add_projectiveSpaceOfModule hZ hLc hZne hLne hle
  obtain ⟨m, hm⟩ := exists_nat_dim (k := k) hn hSne
  rw [hd, hl, hm, hdimP] at hdim
  have hdm : d + l ≤ m + n := by exact_mod_cast hdim
  refine ⟨hSne, ?_⟩
  rw [hd, hm]
  exact_mod_cast (by omega : d ≤ m + c)

/-- The lower bound for the cut of one locally closed irreducible piece `Z ∩ O`, granted the upper
bound for its boundary `Z ∩ Oᶜ`. -/
private theorem nonempty_inter_inter_cutSet_and_dim_le [IsAlgClosed k]
    {Z O : Set (projectiveSpaceOfModule k (ι → k))}
    (hZ : IsClosed Z) (hZi : IsIrreducible Z) (hO : IsOpen O) (hne : (Z ∩ O).Nonempty)
    {c : ℕ} (f : Fin c → ι → k) (hc : (c : WithBot ℕ∞) ≤ topologicalKrullDim ↥Z)
    (hB : topologicalKrullDim ↥((Z ∩ Oᶜ) ∩ cutSet f) + c ≤ topologicalKrullDim ↥(Z ∩ Oᶜ)) :
    (Z ∩ O ∩ cutSet f).Nonempty ∧
      topologicalKrullDim ↥Z ≤ topologicalKrullDim ↥(Z ∩ O ∩ cutSet f) + c := by
  haveI := noetherianSpace_projectiveSpace (k := k) (ι := ι)
  have hZne : Z.Nonempty := hne.mono Set.inter_subset_left
  obtain ⟨n, hn⟩ := exists_card_eq_succ (k := k) hZne
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hSne, hZle⟩ := nonempty_inter_cutSet_and_dim_le hZ hZne f hc
  obtain ⟨m, hm⟩ := exists_nat_dim (k := k) hn hSne
  have h1 : topologicalKrullDim ↥((Z ∩ Oᶜ) ∩ cutSet f) + c + 1 ≤ ((m : ℕ) : WithBot ℕ∞) + c := by
    calc topologicalKrullDim ↥((Z ∩ Oᶜ) ∩ cutSet f) + c + 1
        ≤ topologicalKrullDim ↥(Z ∩ Oᶜ) + 1 := by gcongr
      _ ≤ topologicalKrullDim ↥Z := dim_inter_compl_add_one_le hZ hZi hO hne
      _ ≤ topologicalKrullDim ↥(Z ∩ cutSet f) + c := hZle
      _ = m + c := by rw [hm]
  have hlt : topologicalKrullDim ↥((Z ∩ Oᶜ) ∩ cutSet f) < m := lt_of_add_add_one_le_add h1
  obtain ⟨C, hCc, hCi, hCsub, hSle⟩ :=
    exists_isIrreducible_subset_dim_le (hZ.inter (isClosed_cutSet f)) hSne
  have hnot : ¬ (C ⊆ (Z ∩ Oᶜ) ∩ cutSet f) := fun hsub => by
    rw [← hm] at hlt
    exact absurd ((topologicalKrullDim_le_of_subset hsub).trans_lt hlt) (not_lt.mpr hSle)
  obtain ⟨x, hxC, hxnot⟩ := Set.not_subset.mp hnot
  have hxZL : x ∈ Z ∩ cutSet f := hCsub hxC
  have hxO : x ∈ O := not_not.mp fun h => hxnot ⟨⟨hxZL.1, h⟩, hxZL.2⟩
  have hdimCO := topologicalKrullDim_inter_isOpen_eq k
    (projectiveSpaceOfModuleToSpec k (ι → k)) (Z := C) (O := O) hCc hCi hO ⟨x, hxC, hxO⟩
  refine ⟨⟨x, ⟨hxZL.1, hxO⟩, hxZL.2⟩, ?_⟩
  calc topologicalKrullDim ↥Z ≤ topologicalKrullDim ↥(Z ∩ cutSet f) + c := hZle
    _ ≤ topologicalKrullDim ↥C + c := by gcongr
    _ = topologicalKrullDim ↥(C ∩ O) + c := by rw [hdimCO]
    _ ≤ _ := by
      gcongr
      exact topologicalKrullDim_le_of_subset fun y hy => ⟨⟨(hCsub hy.1).1, hy.2⟩, (hCsub hy.1).2⟩

section Moving

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [IsAlgClosed K]
  [FiniteDimensional K V] [Nontrivial V]

/-- A closed point of the parameter space lies in the basic open of a homogeneous form `z` exactly
when `z` does not vanish at a representing endomorphism. -/
private theorem val_mem_basicOpen_iff {n : ℕ}
    {z : SymmetricAlgebra K (Module.Dual K (V →ₗ[K] V))}
    (hz : z ∈ SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V)))
    (p : ClosedPoints K (Module.Dual K (V →ₗ[K] V))) (g : V →ₗ[K] V) (hg : g ≠ 0)
    (hpg : dualEndClosedPointsEquiv K V p = Projectivization.mk K g hg) :
    (p : projectiveSpaceOfModule K (Module.Dual K (V →ₗ[K] V))) ∈
        Proj.basicOpen (fun n => SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V))) z ↔
      SymmetricAlgebra.lift (Module.Dual.eval K (V →ₗ[K] V) g) z ≠ 0 := by
  rw [Proj.mem_basicOpen, val_eq_linearFunctionalPoint K V p g hg hpg]
  refine not_congr ?_
  rw [linearFunctionalPoint_mem, SymPow.symAlgMap_eq_zero_iff_lift_eq_zero _ hz]

/-- There is a homogeneous form `z` on endomorphisms of `V`, nonvanishing at some invertible
endomorphism, such that every invertible endomorphism at which `z` does not vanish is good for the
pair `Y`, `T`. -/
private theorem exists_form_isGoodEndomorphism (Y T : TopologicalSpace.IrreducibleCloseds
    (projectiveSpaceOfModule K V)) :
    ∃ (n : ℕ) (z : SymmetricAlgebra K (Module.Dual K (V →ₗ[K] V))),
      z ∈ SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V)) ∧
      (∃ g0 : V →ₗ[K] V, LinearMap.det g0 ≠ 0 ∧
        SymmetricAlgebra.lift (Module.Dual.eval K (V →ₗ[K] V) g0) z ≠ 0) ∧
      ∀ g : V →ₗ[K] V, LinearMap.det g ≠ 0 →
        SymmetricAlgebra.lift (Module.Dual.eval K (V →ₗ[K] V) g) z ≠ 0 →
        IsGoodEndomorphism K V (Y : Set (projectiveSpaceOfModule K V))
          (T : Set (projectiveSpaceOfModule K V)) g := by
  classical
  obtain ⟨U, hUo, hUne, hU⟩ := exists_isOpen_nonempty_forall_isGoodEndomorphism K V Y T
  haveI : IrreducibleSpace (projectiveSpaceOfModule K (ParameterModule K V)) := by
    obtain ⟨n, hn⟩ : ∃ n, Module.finrank K V = n + 1 :=
      ⟨Module.finrank K V - 1, by have := Module.finrank_pos (R := K) (M := V); omega⟩
    have hm : Module.finrank K (ParameterModule K V) = (n * n + n) + n + 1 := by
      rw [Subspace.dual_finrank_eq, Module.finrank_linearMap, hn]
      ring
    exact irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq K _ hm
  have hinvo : IsOpen ((invertibleLocus K V : TopologicalSpace.Opens _) : Set
      (projectiveSpaceOfModule K (ParameterModule K V))) := (invertibleLocus K V).isOpen
  have hne : (U ∩ (invertibleLocus K V : Set (projectiveSpaceOfModule K
      (ParameterModule K V)))).Nonempty := by
    have := (IrreducibleSpace.isIrreducible_univ
      (projectiveSpaceOfModule K (ParameterModule K V))).isPreirreducible U _ hUo hinvo
      (by simpa using hUne)
      ⟨identityParameterPoint K V, trivial, identityParameterPoint_mem_invertibleLocus K V⟩
    simpa using this
  obtain ⟨u, hu⟩ := hne
  obtain ⟨_, ⟨r, rfl⟩, hur, hrU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (Proj.isBasis_basicOpen (fun n => SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V))))
    (U := ⟨U ∩ (invertibleLocus K V : Set (projectiveSpaceOfModule K
      (ParameterModule K V))), hUo.inter hinvo⟩) (x := u) hu
  rw [Proj.basicOpen_eq_iSup_proj, TopologicalSpace.Opens.mem_iSup] at hur
  obtain ⟨i, hi⟩ := hur
  set z := GradedRing.proj (fun n => SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V))) i r
  have hz : z ∈ SymPow.symmetricPower i K (Module.Dual K (V →ₗ[K] V)) :=
    (DirectSum.decompose (fun n => SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V)))
      r i).2
  have hzr : Proj.basicOpen (fun n => SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V))) z ≤
      Proj.basicOpen (fun n => SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V))) r := by
    rw [Proj.basicOpen_eq_iSup_proj
      (fun n => SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V))) r]
    exact le_iSup (fun i => Proj.basicOpen
      (fun n => SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V)))
      (GradedRing.proj (fun n => SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V))) i r)) i
  have hzU : ∀ q, q ∈ Proj.basicOpen
      (fun n => SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V))) z →
      q ∈ U ∧ q ∈ (invertibleLocus K V : Set (projectiveSpaceOfModule K
        (ParameterModule K V))) := fun q hq => hrU (hzr hq)
  refine ⟨i, z, hz, ?_, ?_⟩
  · haveI : JacobsonSpace (projectiveSpaceOfModule K (Module.Dual K (V →ₗ[K] V))) :=
      LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec K _)
    obtain ⟨q, hq, hqc⟩ := nonempty_inter_closedPoints (X := projectiveSpaceOfModule K
      (Module.Dual K (V →ₗ[K] V))) (Z := (Proj.basicOpen
        (fun n => SymPow.symmetricPower n K (Module.Dual K (V →ₗ[K] V))) z : Set _))
      ⟨u, hi⟩ (Proj.basicOpen _ z).isOpen.isLocallyClosed
    let p0 : ClosedPoints K (Module.Dual K (V →ₗ[K] V)) := ⟨q, hqc⟩
    set g0 := (dualEndClosedPointsEquiv K V p0).rep
    have hg0 : g0 ≠ 0 := Projectivization.rep_nonzero _
    have hpg0 : dualEndClosedPointsEquiv K V p0 = Projectivization.mk K g0 hg0 :=
      (Projectivization.mk_rep _).symm
    refine ⟨g0, ?_, ?_⟩
    · exact (coe_mem_invertibleLocus_iff_det_ne_zero K V p0 g0 hg0 hpg0).mp (hzU q hq).2
    · exact (val_mem_basicOpen_iff hz p0 g0 hg0 hpg0).mp hq
  · intro g hdet hQ
    have hg : g ≠ 0 :=
      ((LinearMap.isUnit_iff_isUnit_det g).mpr (isUnit_iff_ne_zero.mpr hdet)).ne_zero
    set p := (dualEndClosedPointsEquiv K V).symm (Projectivization.mk K g hg)
    have hpg : dualEndClosedPointsEquiv K V p = Projectivization.mk K g hg :=
      Equiv.apply_symm_apply _ _
    exact hU p (hzU _ ((val_mem_basicOpen_iff hz p g hg hpg).mpr hQ)).1 g ⟨hg, hpg⟩

end Moving

section Forward

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- The projective transformation of an endomorphism carries the common zero set of forms `f j`
into the common zero set of forms `e j` with `g (e j) = f j`. -/
private theorem endProjectionImage_inter_subset {c : ℕ} (g : V →ₗ[K] V)
    (S : Set (projectiveSpaceOfModule K V)) (e f : Fin c → V) (hge : ∀ j, g (e j) = f j) :
    endProjectionImage K V g (S ∩ ⋂ j, linearSubspace K V (K ∙ f j)) ⊆
      endProjectionImage K V g S ∩ ⋂ j, linearSubspace K V (K ∙ e j) := by
  rintro _ ⟨y, ⟨hyS, hyc⟩, rfl⟩
  refine ⟨⟨y, hyS, rfl⟩, ?_⟩
  simp only [Set.mem_iInter, mem_linearSubspace_iff, Submodule.span_singleton_le_iff_mem] at hyc ⊢
  intro j
  rw [mem_pointSubmodule_iff K V _ (e j)]
  rw [mem_endProjection_iff K V g y Nat.one_pos (ι_mem_symmetricPower_one K V (e j)),
    SymPow.symAlgMap_ι, hge j]
  exact (mem_pointSubmodule_iff K V _ (f j)).mp (hyc j)

end Forward

section Slice

variable [DecidableEq ι]

/-- Evaluating the lift of `∑ p, eval (endBasis b p) • Mp p` at `x` is evaluation at an
endomorphism whose `endBasis b`-coordinates are the values of the `Mp p` at `x`. -/
private theorem eval_lift_sum_endBasis {σ' : Type*} (b : Module.Basis ι k (ι → k))
    (Mp : ι × ι → MvPolynomial σ' k) (x : σ' → k) (g : (ι → k) →ₗ[k] (ι → k))
    (hg : ∀ p, (endBasis b).repr g p = MvPolynomial.eval x (Mp p))
    (z : SymmetricAlgebra k (Module.Dual k ((ι → k) →ₗ[k] (ι → k)))) :
    MvPolynomial.eval x (SymmetricAlgebra.lift
      (∑ p : ι × ι, (Module.Dual.eval k _ (endBasis b p)).smulRight (Mp p)) z) =
      SymmetricAlgebra.lift (Module.Dual.eval k _ g) z := by
  set Φ : Module.Dual k ((ι → k) →ₗ[k] (ι → k)) →ₗ[k] MvPolynomial σ' k :=
    ∑ p : ι × ι, (Module.Dual.eval k _ (endBasis b p)).smulRight (Mp p) with hΦ
  have h : (MvPolynomial.aeval x).comp (SymmetricAlgebra.lift Φ) =
      SymmetricAlgebra.lift (Module.Dual.eval k _ g) := by
    apply SymmetricAlgebra.algHom_ext
    ext φ
    show (MvPolynomial.aeval x) ((SymmetricAlgebra.lift Φ) (SymmetricAlgebra.ι k _ φ)) =
        (SymmetricAlgebra.lift (Module.Dual.eval k _ g)) (SymmetricAlgebra.ι k _ φ)
    rw [SymmetricAlgebra.lift_ι_apply, SymmetricAlgebra.lift_ι_apply, Module.Dual.eval_apply]
    conv_rhs => rw [← (endBasis b).sum_repr g]
    simp only [hΦ, LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Dual.eval_apply,
      map_sum, map_smul, smul_eq_mul, hg, MvPolynomial.coe_aeval_eq_eval]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  simpa using DFunLike.congr_fun h z

/-- Slicing the endomorphisms by prescribing the images of `c` basis vectors turns a polynomial
function of an endomorphism into a polynomial in the `c` images. -/
private theorem exists_poly_of_form {c : ℕ} (σ : Fin c → ι) (hσ : Function.Injective σ)
    (z : SymmetricAlgebra k (Module.Dual k ((ι → k) →ₗ[k] (ι → k))))
    (g0 : (ι → k) →ₗ[k] (ι → k))
    (hg0 : LinearMap.det g0 ≠ 0 ∧ SymmetricAlgebra.lift (Module.Dual.eval k _ g0) z ≠ 0) :
    ∃ (G : (Fin c → ι → k) → ((ι → k) →ₗ[k] (ι → k))) (P : MvPolynomial (Fin c × ι) k),
      P ≠ 0 ∧ (∀ f j, G f (Pi.single (σ j) 1) = f j) ∧
      ∀ f, MvPolynomial.eval (fun p => f p.1 p.2) P =
        LinearMap.det (G f) * SymmetricAlgebra.lift (Module.Dual.eval k _ (G f)) z := by
  classical
  let b : Module.Basis ι k (ι → k) := Pi.basisFun k ι
  let col : (Fin c → ι → k) → ι → (ι → k) := fun f i =>
    if h : i ∈ Set.range σ then f h.choose else g0 (Pi.single i 1)
  have hcol : ∀ f j, col f (σ j) = f j := by
    intro f j
    have h : σ j ∈ Set.range σ := ⟨j, rfl⟩
    simp only [col, dif_pos h]
    congr 1
    exact hσ h.choose_spec
  let G : (Fin c → ι → k) → ((ι → k) →ₗ[k] (ι → k)) := fun f =>
    Matrix.toLin' (Matrix.of fun l i => col f i l)
  have hG : ∀ f i, G f (Pi.single i 1) = col f i := by
    intro f i
    ext l
    simp [G, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  have hGmat : ∀ f, LinearMap.toMatrix b b (G f) = Matrix.of fun l i => col f i l := by
    intro f
    rw [LinearMap.toMatrix_eq_toMatrix']
    exact LinearMap.toMatrix'_toLin' _
  let Mp : ι × ι → MvPolynomial (Fin c × ι) k := fun p =>
    if h : p.2 ∈ Set.range σ then MvPolynomial.X (h.choose, p.1)
    else MvPolynomial.C (g0 (Pi.single p.2 1) p.1)
  have hMp : ∀ f p, MvPolynomial.eval (fun q : Fin c × ι => f q.1 q.2) (Mp p) =
      col f p.2 p.1 := by
    intro f p
    by_cases h : p.2 ∈ Set.range σ
    · have e : col f p.2 = f h.choose := by simp only [col, dif_pos h]
      rw [e]
      simp only [Mp, dif_pos h, MvPolynomial.eval_X]
    · have e : col f p.2 = g0 (Pi.single p.2 1) := by simp only [col, dif_neg h]
      rw [e]
      simp only [Mp, dif_neg h, MvPolynomial.eval_C]
  let Φ : Module.Dual k ((ι → k) →ₗ[k] (ι → k)) →ₗ[k] MvPolynomial (Fin c × ι) k :=
    ∑ p : ι × ι, (Module.Dual.eval k _ (endBasis b p)).smulRight (Mp p)
  let Dp : MvPolynomial (Fin c × ι) k := (Matrix.of fun l i => Mp (l, i)).det
  have hE1 : ∀ f, MvPolynomial.eval (fun q : Fin c × ι => f q.1 q.2) Dp =
      LinearMap.det (G f) := by
    intro f
    rw [show LinearMap.det (G f) = (Matrix.of fun l i => col f i l).det from
      LinearMap.det_toLin' _]
    simp only [Dp]
    rw [RingHom.map_det]
    congr 1
    ext l i
    simp [RingHom.mapMatrix_apply, hMp]
  have hE2 : ∀ f, MvPolynomial.eval (fun q : Fin c × ι => f q.1 q.2)
      (SymmetricAlgebra.lift Φ z) =
      SymmetricAlgebra.lift (Module.Dual.eval k _ (G f)) z := fun f =>
    eval_lift_sum_endBasis b Mp _ (G f) (fun p => by rw [hMp, endBasis_repr, hGmat]; rfl) z
  refine ⟨G, Dp * SymmetricAlgebra.lift Φ z, ?_, fun f j => ?_, fun f => ?_⟩
  · intro hP0
    set f0 : Fin c → ι → k := fun j => g0 (Pi.single (σ j) 1)
    have hcol0 : ∀ i, col f0 i = g0 (Pi.single i 1) := by
      intro i
      by_cases h : i ∈ Set.range σ
      · obtain ⟨j, rfl⟩ := h
        rw [hcol]
      · simp only [col, dif_neg h]
    have hG0 : G f0 = g0 := by
      refine b.ext fun i => ?_
      rw [show b i = Pi.single i 1 by simp [b], hG, hcol0]
    have := congrArg (MvPolynomial.eval (fun q : Fin c × ι => f0 q.1 q.2)) hP0
    rw [_root_.map_mul, hE1, hE2, hG0, map_zero] at this
    exact mul_ne_zero hg0.1 hg0.2 this
  · rw [hG, hcol]
  · rw [_root_.map_mul, hE1, hE2]

end Slice

/-- More forms than the dimension of the space: general forms span, so the cut is empty. -/
private theorem exists_poly_cutSet_eq_empty_of_card_le {c : ℕ} (hc : Fintype.card ι ≤ c) :
    ∃ P : MvPolynomial (Fin c × ι) k, P ≠ 0 ∧
      ∀ f : Fin c → ι → k, MvPolynomial.eval (fun p => f p.1 p.2) P ≠ 0 → cutSet f = ∅ := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let idx : ι → Fin c := fun i => Fin.castLE hc (e i)
  have hidx : Function.Injective idx := fun i j h => e.injective (Fin.castLE_injective hc h)
  let Mx : Matrix ι ι (MvPolynomial (Fin c × ι) k) := Matrix.of fun i l => MvPolynomial.X (idx i, l)
  have hdet : ∀ f : Fin c → ι → k, MvPolynomial.eval (fun p : Fin c × ι => f p.1 p.2) Mx.det =
      (Matrix.of fun i l => f (idx i) l).det := by
    intro f
    rw [RingHom.map_det]
    congr 1
    ext i l
    simp [Mx]
  refine ⟨Mx.det, ?_, fun f hf => ?_⟩
  · intro h0
    let f0 : Fin c → ι → k := fun j l => if ∃ i, idx i = j ∧ i = l then 1 else 0
    have h1 := congrArg (MvPolynomial.eval (fun p : Fin c × ι => f0 p.1 p.2)) h0
    rw [hdet, map_zero] at h1
    have : (Matrix.of fun i l => f0 (idx i) l) = 1 := by
      ext i l
      simp only [Matrix.of_apply, f0, Matrix.one_apply]
      by_cases h : i = l
      · subst h; simp
      · have : ¬ ∃ i', idx i' = idx i ∧ i' = l := by
          rintro ⟨i', hi', hl⟩
          exact h ((hidx hi').symm.trans hl)
        rw [if_neg this, if_neg h]
    rw [this, Matrix.det_one] at h1
    exact one_ne_zero h1
  · rw [hdet] at hf
    have hli := Matrix.linearIndependent_rows_of_det_ne_zero hf
    have htop : Submodule.span k (Set.range fun i => f (idx i)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by simp)
    rw [cutSet_eq, eq_top_mono (Submodule.span_mono (Set.range_comp_subset_range idx f)) htop,
      linearSubspace_top]

/-- The upper bound for the cut of an irreducible closed set by general hyperplanes, when there are
fewer forms than the dimension of the space. -/
private theorem exists_poly_dim_inter_cutSet_add_le_of_lt_card [IsAlgClosed k]
    {Y : Set (projectiveSpaceOfModule k (ι → k))}
    (hY : IsClosed Y) (hYi : IsIrreducible Y) {c : ℕ} (hc : c < Fintype.card ι) :
    ∃ P : MvPolynomial (Fin c × ι) k, P ≠ 0 ∧
      ∀ f : Fin c → ι → k, MvPolynomial.eval (fun p => f p.1 p.2) P ≠ 0 →
        topologicalKrullDim ↥(Y ∩ cutSet f) + c ≤ topologicalKrullDim ↥Y := by
  classical
  obtain ⟨n, hn⟩ := exists_card_eq_succ (k := k) hYi.nonempty
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let σ : Fin c → ι := fun j => e.symm (Fin.castLE hc.le j)
  have hσ : Function.Injective σ := fun i j h =>
    Fin.castLE_injective hc.le (e.symm.injective h)
  let ej : Fin c → ι → k := fun j => Pi.single (σ j) 1
  have hli : LinearIndependent k ej := by
    have := (Pi.basisFun k ι).linearIndependent.comp σ hσ
    convert this using 1
    ext j l
    simp [ej]
  have hne := span_range_ne_top ej hc
  have hfin : Module.finrank k (Submodule.span k (Set.range ej)) = c := by
    rw [finrank_span_eq_card hli]; simp
  have hq : Module.finrank k ((ι → k) ⧸ Submodule.span k (Set.range ej)) = (n - c) + 1 := by
    have := Submodule.finrank_quotient_add_finrank (Submodule.span k (Set.range ej))
    rw [hfin, Module.finrank_pi] at this
    omega
  have hTirr : IsIrreducible (cutSet ej) := by
    haveI : IrreducibleSpace (projectiveSpaceOfModule k
        ((ι → k) ⧸ Submodule.span k (Set.range ej))) :=
      irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq k _ hq
    haveI : IrreducibleSpace ↥(linearSubspace k (ι → k) (Submodule.span k (Set.range ej))) :=
      (linearSubspaceHomeomorph (Submodule.span k (Set.range ej))).surjective.irreducibleSpace
        (linearSubspaceHomeomorph (Submodule.span k (Set.range ej))).continuous
    have := (IrreducibleSpace.isIrreducible_univ
      ↥(linearSubspace k (ι → k) (Submodule.span k (Set.range ej)))).image Subtype.val
      continuous_subtype_val.continuousOn
    rw [Set.image_univ, Subtype.range_coe] at this
    rwa [cutSet_eq]
  have hTdim' : topologicalKrullDim ↥(cutSet ej) = ((n - c : ℕ) : WithBot ℕ∞) := by
    have h := topologicalKrullDim_linearSubspace_add_one hne
    rw [hq] at h
    obtain ⟨m, hm, hm1⟩ := exists_nat_of_add_one_eq _ _ h
    rw [cutSet_eq, hm]
    have : m = n - c := by omega
    rw [this]
  obtain ⟨_, z, hz, ⟨g0, hdet0, hQ0⟩, hgood⟩ := exists_form_isGoodEndomorphism
    (K := k) (V := ι → k)
    ⟨Y, hYi, hY⟩ ⟨cutSet ej, hTirr, isClosed_cutSet ej⟩
  obtain ⟨G, P, hP0, hGσ, hPeval⟩ := exists_poly_of_form σ hσ z g0 ⟨hdet0, hQ0⟩
  refine ⟨P, hP0, fun f hf => ?_⟩
  rw [hPeval f] at hf
  have hdet := left_ne_zero_of_mul hf
  have hQ := right_ne_zero_of_mul hf
  obtain ⟨hdom, hineq⟩ := hgood (G f) hdet hQ
  have hsub := endProjectionImage_inter_subset (G f) Y ej f (fun j => hGσ f j)
  have hSc : IsClosed (Y ∩ cutSet f) := hY.inter (isClosed_cutSet f)
  have hdomS : (Y ∩ cutSet f) ⊆ (endDomain k (ι → k) (G f) : Set (projectiveSpaceOfModule k
      (ι → k))) := fun x hx => hdom hx.1
  have h1 : topologicalKrullDim ↥(endProjectionImage k (ι → k) (G f) (Y ∩ cutSet f)) =
      topologicalKrullDim ↥(Y ∩ cutSet f) :=
    topologicalKrullDim_endProjectionImage_eq k (ι → k) (G f) hSc hdomS
  have h2 : topologicalKrullDim ↥(endProjectionImage k (ι → k) (G f) Y) =
      topologicalKrullDim ↥Y :=
    topologicalKrullDim_endProjectionImage_eq k (ι → k) (G f) hY hdom
  have h3 : topologicalKrullDim ↥(Y ∩ cutSet f) ≤
      topologicalKrullDim ↥(endProjectionImage k (ι → k) (G f) Y ∩ cutSet ej) := by
    rw [← h1]; exact topologicalKrullDim_le_of_subset hsub
  change topologicalKrullDim ↥(endProjectionImage k (ι → k) (G f) Y ∩ cutSet ej) +
      topologicalKrullDim (projectiveSpaceOfModule k (ι → k)) ≤
    topologicalKrullDim ↥(endProjectionImage k (ι → k) (G f) Y) +
      topologicalKrullDim ↥(cutSet ej) at hineq
  rw [h2, hTdim', topologicalKrullDim_projectiveSpace (k := k) hn] at hineq
  by_cases hS : (Y ∩ cutSet f).Nonempty
  · obtain ⟨s, hs⟩ := exists_nat_dim (k := k) hn hS
    have hXne : (endProjectionImage k (ι → k) (G f) Y ∩ cutSet ej).Nonempty := by
      by_contra hXe
      rw [Set.not_nonempty_iff_eq_empty] at hXe
      rw [hXe, topologicalKrullDim_emptySet, hs] at h3
      simp at h3
    obtain ⟨x, hx⟩ := exists_nat_dim (k := k) hn hXne
    obtain ⟨d, hd⟩ := exists_nat_dim (k := k) hn hYi.nonempty
    rw [hx, hd] at hineq
    rw [hx, hs] at h3
    rw [hs, hd]
    have h3' : s ≤ x := by exact_mod_cast h3
    have hineq' : x + n ≤ d + (n - c) := by exact_mod_cast hineq
    have hcn : c ≤ n := by omega
    exact_mod_cast (by omega : s + c ≤ d)
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    rw [hS, topologicalKrullDim_emptySet]
    simp

/-- The upper bound for the cut of an irreducible closed set by general hyperplanes. -/
private theorem exists_poly_dim_inter_cutSet_add_le_of_isIrreducible [IsAlgClosed k]
    {Y : Set (projectiveSpaceOfModule k (ι → k))}
    (hY : IsClosed Y) (hYi : IsIrreducible Y) (c : ℕ) :
    ∃ P : MvPolynomial (Fin c × ι) k, P ≠ 0 ∧
      ∀ f : Fin c → ι → k, MvPolynomial.eval (fun p => f p.1 p.2) P ≠ 0 →
        topologicalKrullDim ↥(Y ∩ cutSet f) + c ≤ topologicalKrullDim ↥Y := by
  classical
  rcases lt_or_ge c (Fintype.card ι) with h | h
  · exact exists_poly_dim_inter_cutSet_add_le_of_lt_card hY hYi h
  · obtain ⟨P, hP0, hP⟩ := exists_poly_cutSet_eq_empty_of_card_le (k := k) (ι := ι) h
    refine ⟨P, hP0, fun f hf => ?_⟩
    rw [hP f hf, Set.inter_empty, topologicalKrullDim_emptySet]
    simp

/-- The upper bound for the cut of a closed set by general hyperplanes. -/
private theorem exists_poly_dim_inter_cutSet_add_le [IsAlgClosed k]
    {Y : Set (projectiveSpaceOfModule k (ι → k))}
    (hY : IsClosed Y) (c : ℕ) :
    ∃ P : MvPolynomial (Fin c × ι) k, P ≠ 0 ∧
      ∀ f : Fin c → ι → k, MvPolynomial.eval (fun p => f p.1 p.2) P ≠ 0 →
        topologicalKrullDim ↥(Y ∩ cutSet f) + c ≤ topologicalKrullDim ↥Y := by
  classical
  haveI := noetherianSpace_projectiveSpace (k := k) (ι := ι)
  obtain ⟨T, hTfin, hTc, hTi, hTeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hY
  haveI : Fintype ↥T := hTfin.fintype
  choose P hP0 hP using fun C : ↥T =>
    exists_poly_dim_inter_cutSet_add_le_of_isIrreducible (k := k) (ι := ι)
      (hTc C C.2) (hTi C C.2) c
  refine ⟨∏ C : ↥T, P C, Finset.prod_ne_zero_iff.mpr fun C _ => hP0 C, fun f hf => ?_⟩
  rw [map_prod] at hf
  have hCf := fun C => Finset.prod_ne_zero_iff.mp hf C (Finset.mem_univ C)
  refine dim_add_le_of_subset_biUnion (Finset.univ : Finset ↥T)
    (A := fun C : ↥T => C.1 ∩ cutSet f) (fun C => (hTc C C.2).inter (isClosed_cutSet f)) ?_ ?_
  · intro x hx
    have hxY := hx.1
    rw [hTeq] at hxY
    obtain ⟨C, hC, hxC⟩ := hxY
    exact Set.mem_biUnion (Finset.mem_univ ⟨C, hC⟩) ⟨hxC, hx.2⟩
  · intro C _
    refine (hP C f (hCf C)).trans (topologicalKrullDim_le_of_subset ?_)
    rw [hTeq]
    exact fun x hx => ⟨C.1, C.2, hx⟩

private theorem exists_pieces_fin {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] {W : Set X} (hW : Topology.IsConstructible W) :
    ∃ (m : ℕ) (O Z : Fin m → Set X),
      (∀ i, IsOpen (O i) ∧ IsClosed (Z i) ∧ IsIrreducible (Z i) ∧ (Z i ∩ O i).Nonempty) ∧
      W = ⋃ i, Z i ∩ O i := by
  classical
  obtain ⟨s, hs, hWeq⟩ := exists_pieces hW
  refine ⟨s.card, fun i => (s.equivFin.symm i).1.1, fun i => (s.equivFin.symm i).1.2,
    fun i => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hs _ (s.equivFin.symm i).2
    exact ⟨h1, h2, h3, h4⟩
  · rw [hWeq]
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨p, hp, hx⟩
      refine ⟨s.equivFin ⟨p, hp⟩, ?_⟩
      simpa using hx
    · rintro ⟨i, hx⟩
      exact ⟨_, (s.equivFin.symm i).2, hx⟩

private theorem zero_le_dim_of_nonempty {X : Type*} [TopologicalSpace X] {S : Set X}
    (h : S.Nonempty) : 0 ≤ topologicalKrullDim ↥S := by
  have hne : topologicalKrullDim ↥S ≠ ⊥ := by
    rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
    exact fun h' => h'.false ⟨h.some, h.some_mem⟩
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hm]
  exact WithBot.coe_le_coe.mpr bot_le

/-- The dimension count for general linear sections of one constructible set `W`: off the zero
set of a nonzero polynomial in the coefficients, `c` hyperplanes miss `W` when `dim W < c` and
cut it in a nonempty set of dimension `dim W - c` otherwise. -/
private theorem exists_poly_inter_cutSet_dim_eq [IsAlgClosed k]
    {W : Set (projectiveSpaceOfModule k (ι → k))} (hW : Topology.IsConstructible W) (c : ℕ) :
    ∃ P : MvPolynomial (Fin c × ι) k, P ≠ 0 ∧
      ∀ f : Fin c → ι → k, MvPolynomial.eval (fun p => f p.1 p.2) P ≠ 0 →
        (topologicalKrullDim ↥W < c → W ∩ cutSet f = ∅) ∧
        ((c : WithBot ℕ∞) ≤ topologicalKrullDim ↥W →
          (W ∩ cutSet f).Nonempty ∧
          topologicalKrullDim ↥(W ∩ cutSet f) + c = topologicalKrullDim ↥W) := by
  classical
  haveI := noetherianSpace_projectiveSpace (k := k) (ι := ι)
  obtain ⟨m, O, Z, hpc, rfl⟩ := exists_pieces_fin hW
  choose P1 hP10 hP1 using fun i =>
     exists_poly_dim_inter_cutSet_add_le (k := k) (ι := ι) (hpc i).2.1 c
  choose P2 hP20 hP2 using fun i =>
    exists_poly_dim_inter_cutSet_add_le (k := k) (ι := ι)
      ((hpc i).2.1.inter (hpc i).1.isClosed_compl) c
  refine ⟨∏ i, P1 i * P2 i, Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (hP10 i) (hP20 i),
    fun f hf => ?_⟩
  rw [map_prod] at hf
  have hfi : ∀ i, MvPolynomial.eval (fun p : Fin c × ι => f p.1 p.2) (P1 i) *
      MvPolynomial.eval (fun p : Fin c × ι => f p.1 p.2) (P2 i) ≠ 0 := fun i => by
    have := Finset.prod_ne_zero_iff.mp hf i (Finset.mem_univ i)
    rwa [_root_.map_mul] at this
  have hf1 := fun i => (mul_ne_zero_iff.mp (hfi i)).1
  have hf2 := fun i => (mul_ne_zero_iff.mp (hfi i)).2
  set W := ⋃ i, Z i ∩ O i
  have hdimW : topologicalKrullDim ↥W =
      (Finset.univ : Finset (Fin m)).sup (fun i => topologicalKrullDim ↥(Z i)) := by
    refine le_antisymm ?_ ?_
    · refine (topologicalKrullDim_le_of_subset (T := ⋃ i ∈ (Finset.univ : Finset (Fin m)), Z i)
        ?_).trans (topologicalKrullDim_biUnion_le Finset.univ (fun i => (hpc i).2.1)
          (fun i _ => Finset.le_sup (f := fun i => topologicalKrullDim ↥(Z i))
            (Finset.mem_univ i)))
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_biUnion (Finset.mem_univ i) hi.1
    · refine Finset.sup_le fun i _ => ?_
      obtain ⟨n, hn⟩ := exists_card_eq_succ (k := k) ((hpc i).2.2.2.mono Set.inter_subset_left)
      haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
      rw [← topologicalKrullDim_inter_isOpen_eq k (projectiveSpaceOfModuleToSpec k (ι → k))
        (hpc i).2.1 (hpc i).2.2.1 (hpc i).1 (hpc i).2.2.2]
      exact topologicalKrullDim_le_of_subset (Set.subset_iUnion (fun i => Z i ∩ O i) i)
  have hdimZ : ∀ i, topologicalKrullDim ↥(Z i) ≤ topologicalKrullDim ↥W := fun i => by
    rw [hdimW]; exact Finset.le_sup (f := fun i => topologicalKrullDim ↥(Z i)) (Finset.mem_univ i)
  have hup : topologicalKrullDim ↥(W ∩ cutSet f) + c ≤ topologicalKrullDim ↥W := by
    refine dim_add_le_of_subset_biUnion (Finset.univ : Finset (Fin m))
      (A := fun i => Z i ∩ cutSet f) (fun i => (hpc i).2.1.inter (isClosed_cutSet f)) ?_ ?_
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx.1
      exact Set.mem_biUnion (Finset.mem_univ i) ⟨hi.1, hx.2⟩
    · intro i _
      exact (hP1 i f (hf1 i)).trans (hdimZ i)
  refine ⟨fun hlt => ?_, fun hc => ?_⟩
  · refine Set.not_nonempty_iff_eq_empty.mp fun hne => lt_irrefl _
      ((le_add_of_nonneg_left (zero_le_dim_of_nonempty hne)).trans_lt (hup.trans_lt hlt))
  · have hmne : (Finset.univ : Finset (Fin m)).Nonempty := by
      by_contra hmm
      rw [Finset.not_nonempty_iff_eq_empty] at hmm
      rw [hdimW, hmm] at hc
      simp at hc
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin m)) hmne
      (fun i => topologicalKrullDim ↥(Z i))
    have hci : (c : WithBot ℕ∞) ≤ topologicalKrullDim ↥(Z i) := by rwa [← hi, ← hdimW]
    obtain ⟨hne1, hlow⟩ := nonempty_inter_inter_cutSet_and_dim_le
      (hpc i).2.1 (hpc i).2.2.1 (hpc i).1 (hpc i).2.2.2 f hci
      (hP2 i f (hf2 i))
    have hsub : Z i ∩ O i ∩ cutSet f ⊆ W ∩ cutSet f := fun x hx =>
      ⟨Set.mem_iUnion.mpr ⟨i, hx.1⟩, hx.2⟩
    refine ⟨hne1.mono hsub, le_antisymm hup ?_⟩
    calc topologicalKrullDim ↥W = topologicalKrullDim ↥(Z i) := by rw [hdimW, hi]
      _ ≤ topologicalKrullDim ↥(Z i ∩ O i ∩ cutSet f) + c := hlow
      _ ≤ _ := by gcongr; exact topologicalKrullDim_le_of_subset hsub

end

/-- **General linear sections of constructible sets (dimension count).** Let `k` be algebraically
closed of characteristic zero, `ℙ = 𝐏(k^ι)` with `ι` finite, `W_u ⊆ ℙ` (`u ∈ U`, `U` finite)
constructible and `c : ℕ`. There is a nonzero polynomial `P` in the coefficients of `c` linear
forms `f_1, …, f_c` such that whenever `P(f) ≠ 0`, for every `u` the cut
`W_u ∩ V(f_1) ∩ ⋯ ∩ V(f_c)` is empty if `dim W_u < c`, and otherwise is nonempty of dimension
`dim W_u - c`. -/
@[mmp "lem_mmp_foundation_general_linear_sections_constructible"]
public theorem exists_ne_zero_forall_eval_ne_zero_inter_hyperplanes (k : Type u) [Field k]
    [IsAlgClosed k] [CharZero k] {ι : Type u} [Fintype ι] {U : Type*} [Finite U]
    (W : U → Set (projectiveSpaceOfModule k (ι → k))) (hW : ∀ u, Topology.IsConstructible (W u))
    (c : ℕ) :
    ∃ P : MvPolynomial (Fin c × ι) k, P ≠ 0 ∧
      ∀ f : Fin c → ι → k, MvPolynomial.eval (fun p => f p.1 p.2) P ≠ 0 → ∀ u,
        (topologicalKrullDim ↥(W u) < c →
          W u ∩ ⋂ i, linearSubspace k (ι → k) (k ∙ f i) = ∅) ∧
        ((c : WithBot ℕ∞) ≤ topologicalKrullDim ↥(W u) →
          (W u ∩ ⋂ i, linearSubspace k (ι → k) (k ∙ f i)).Nonempty ∧
          topologicalKrullDim ↥(W u ∩ ⋂ i, linearSubspace k (ι → k) (k ∙ f i)) + c =
            topologicalKrullDim ↥(W u)) := by
  have := Fintype.ofFinite U
  choose P hP0 hP using fun u =>
    exists_poly_inter_cutSet_dim_eq (k := k) (ι := ι) (hW u) c
  refine ⟨∏ u, P u, Finset.prod_ne_zero_iff.mpr fun u _ => hP0 u, fun f hf u => hP u f ?_⟩
  rw [map_prod] at hf
  exact Finset.prod_ne_zero_iff.mp hf u (Finset.mem_univ u)

end MMP
