module

public import MMP.AlgebraicGeometry.Semialgebraic.Cells
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Connected.Basic

/-!
# Decomposition of `ℝⁿ` into connected semialgebraic pieces

Every finite family of semialgebraic subsets of `ℝ^σ`, `σ` finite, is *adapted* to a finite
cover of `ℝ^σ` by connected semialgebraic sets: each piece of the cover lies in, or is disjoint
from, each member of the family. This is the topological content of the cylindrical algebraic
decomposition, proved the same way, by induction on the number of coordinates. Write
`ℝ^{Option σ} = ℝ^σ × ℝ` and let `F` be the family of all `t`-derivatives of the polynomials
defining the given sets. Hörmander's theorem (`TarskiSeidenberg.hasSignPatternCover`) covers
`ℝ^σ` by semialgebraic pieces of constant sign pattern of `F`, and by induction these pieces are
refined by a connected semialgebraic cover. Over a connected piece `E` of constant sign pattern
the zeros of `F(a, ·)` are the values of finitely many continuous functions
`ξ₀ < ξ₁ < ⋯` (`continuousOn_familyRootsNth`), and their graphs and the bands between them are
connected, semialgebraic (`isSemialgebraic_graph_familyRootsNth`,
`isSemialgebraic_setOf_inFamilyRootsBand`), and carry constant signs of `F`.

## Main results

* `MMP.exists_isPreconnected_cover_of_sameSignPattern`: the graphs and bands over a
  connected set of constant sign pattern.
* `MMP.isPreconnected_setOf_mem_fiber`: a set over a connected base whose fibres
  are intervals containing a continuous section is connected.
* `MMP.IsSemialgebraic.exists_isPreconnected_cover`: a finite family of
  semialgebraic sets is adapted to a finite cover by connected semialgebraic sets.
* `MMP.IsSemialgebraic.exists_cylindrical_cover`: the cylindrical form, over a
  connected cover of `ℝ^σ` of constant sign pattern of a family closed under `∂/∂t`.
* `MMP.exists_isPreconnected_cover_continuousOn_of_isSemialgebraic_graph`: a
  function with semialgebraic graph is continuous on the pieces of a finite connected
  semialgebraic cover of its domain.
* `MMP.IsSemialgebraic.connectedComponentIn`: the connected components of a
  semialgebraic set are semialgebraic.
* `MMP.IsSemialgebraic.finite_connectedComponents`: a semialgebraic set has
  finitely many connected components.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], §2.3.
-/

@[expose] public section

open Polynomial Set Topology

namespace MMP

/-- The point of `ℝ^{Option σ}` with coordinates `a` and `t`. -/
abbrev optionCons {σ : Type*} (a : σ → ℝ) (t : ℝ) : Option σ → ℝ := fun o ↦ o.elim t a

/-- Restricting `optionCons a t` to the coordinates `σ` gives `a`. -/
theorem optionCons_comp_some {σ : Type*} (a : σ → ℝ) (t : ℝ) : optionCons a t ∘ some = a := rfl

/-- The coordinate `none` of `optionCons a t` is `t`. -/
theorem optionCons_none {σ : Type*} (a : σ → ℝ) (t : ℝ) : optionCons a t none = t := rfl

/-- Every point of `ℝ^{Option σ}` is `optionCons` of its restriction to `σ` and its coordinate
`none`. -/
theorem optionCons_eta {σ : Type*} (x : Option σ → ℝ) : optionCons (x ∘ some) (x none) = x := by
  funext o
  cases o <;> rfl

/-- The map `(a, t) ↦ optionCons a t` from `ℝ^σ × ℝ` to `ℝ^{Option σ}` is continuous. -/
theorem continuous_optionCons {σ : Type*} :
    Continuous fun p : (σ → ℝ) × ℝ ↦ optionCons p.1 p.2 := by
  refine continuous_pi fun o ↦ ?_
  cases o with
  | none => exact continuous_snd
  | some i => exact (continuous_apply i).comp continuous_fst

/-- **Connectedness of cylinders over a connected base.** Let `E ⊆ ℝ^σ` be preconnected and
`U a ⊆ ℝ`, `a ∈ E`, intervals containing `s a` for a function `s` continuous on `E`. Then the set
of `(a, t)` with `a ∈ E`, `t ∈ U a`, is preconnected. -/
theorem isPreconnected_setOf_mem_fiber {σ : Type*} {E : Set (σ → ℝ)} (hE : IsPreconnected E)
    (U : (σ → ℝ) → Set ℝ) (hU : ∀ a ∈ E, (U a).OrdConnected) (s : (σ → ℝ) → ℝ)
    (hs : ContinuousOn s E) (hsU : ∀ a ∈ E, s a ∈ U a) :
    IsPreconnected {x : Option σ → ℝ | x ∘ some ∈ E ∧ x none ∈ U (x ∘ some)} := by
  rcases E.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simpa using isPreconnected_empty
  set B := {x : Option σ → ℝ | x ∘ some ∈ E ∧ x none ∈ U (x ∘ some)}
  set G := (fun a ↦ optionCons a (s a)) '' E
  have hG : IsPreconnected G := hE.image _
    (continuous_optionCons.comp_continuousOn (continuousOn_id.prodMk hs))
  have hGB : G ⊆ B := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨ha, hsU a ha⟩
  refine isPreconnected_of_forall (optionCons a₀ (s a₀)) fun y hy ↦ ?_
  set a := y ∘ some
  set Fa := optionCons a '' U a
  have hFa : IsPreconnected Fa := (hU a hy.1).isPreconnected.image _
    (continuous_optionCons.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hFaB : Fa ⊆ B := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hy.1, ht⟩
  refine ⟨G ∪ Fa, union_subset hGB hFaB, Or.inl ⟨a₀, ha₀, rfl⟩, Or.inr ?_,
    hG.union (optionCons a (s a)) ⟨a, hy.1, rfl⟩ ⟨s a, hsU a hy.1, rfl⟩ hFa⟩
  exact ⟨y none, hy.2, optionCons_eta y⟩

/-- If one point of `X` in `S` forces every point of `X` into `S`, then `X` lies in `S` or is
disjoint from it. -/
theorem subset_or_disjoint_of_forall_mem_iff {α : Type*} {X S : Set α}
    (h : ∀ x ∈ X, ∀ y ∈ X, x ∈ S → y ∈ S) : X ⊆ S ∨ Disjoint X S := by
  by_cases hX : ∃ x ∈ X, x ∈ S
  · obtain ⟨x, hx, hxS⟩ := hX
    exact Or.inl fun y hy ↦ h x hx y hy hxS
  · push Not at hX
    exact Or.inr (Set.disjoint_left.2 hX)

section OverBase

open TarskiSeidenberg

variable {σ ι : Type*} [Fintype ι] {P : ι → (MvPolynomial σ ℝ)[X]}

/-- The root functions over a set of constant sign pattern are continuous. -/
theorem continuousOn_familyRootsNth_specAt (hder : ∀ i, ∃ j, P j = derivative (P i))
    {E : Set (σ → ℝ)}
    (hpat : ∀ a ∈ E, ∀ b ∈ E, SameSignPattern (fun i ↦ specAt a (P i)) (fun i ↦ specAt b (P i)))
    (m : ℕ) : ContinuousOn (fun a ↦ familyRootsNth (fun i ↦ specAt a (P i)) m) E :=
  continuousOn_familyRootsNth (F := fun i a ↦ specAt a (P i)) hpat
    (fun i x ↦ continuous_eval_specAt (P i) x)
    (fun i ↦ (hder i).imp fun _ hj _ ↦ by simp only [hj, specAt_derivative]) m

/-- Each band over a set of constant sign pattern has a continuous section. -/
theorem exists_continuousOn_inFamilyRootsBand (hder : ∀ i, ∃ j, P j = derivative (P i))
    {E : Set (σ → ℝ)} {n : ℕ} (hn : ∀ a ∈ E, (familyRoots fun i ↦ specAt a (P i)).card = n)
    (hpat : ∀ a ∈ E, ∀ b ∈ E, SameSignPattern (fun i ↦ specAt a (P i)) (fun i ↦ specAt b (P i)))
    {j : ℕ} (hj : j ≤ n) :
    ∃ s : (σ → ℝ) → ℝ, ContinuousOn s E ∧
      ∀ a ∈ E, InFamilyRootsBand (fun i ↦ specAt a (P i)) j (s a) := by
  have hc := continuousOn_familyRootsNth_specAt hder hpat
  have hmono : ∀ a ∈ E, ∀ m < n, 0 < m →
      familyRootsNth (fun i ↦ specAt a (P i)) (m - 1) <
        familyRootsNth (fun i ↦ specAt a (P i)) m := fun a ha m hm hm0 ↦
    familyRootsNth_strictMonoOn (by simp only [mem_setOf_eq, hn a ha]; omega)
      (by simp only [mem_setOf_eq, hn a ha]; omega) (by omega)
  by_cases hn0 : n = 0
  · refine ⟨fun _ ↦ 0, continuousOn_const, fun a ha ↦ inFamilyRootsBand_of_lt
      (by rw [hn a ha]; omega) (fun h ↦ by omega) (fun h ↦ by rw [hn a ha] at h; omega)⟩
  by_cases hj0 : j = 0
  · subst hj0
    refine ⟨fun a ↦ familyRootsNth (fun i ↦ specAt a (P i)) 0 - 1, (hc 0).sub continuousOn_const,
      fun a ha ↦ inFamilyRootsBand_of_lt (by omega) (fun h ↦ by omega) (fun _ ↦ by linarith)⟩
  by_cases hjn : j = n
  · subst hjn
    refine ⟨fun a ↦ familyRootsNth (fun i ↦ specAt a (P i)) (j - 1) + 1,
      (hc _).add continuousOn_const, fun a ha ↦ inFamilyRootsBand_of_lt (by rw [hn a ha])
        (fun _ ↦ by linarith) (fun h ↦ by rw [hn a ha] at h; omega)⟩
  refine ⟨fun a ↦ (familyRootsNth (fun i ↦ specAt a (P i)) (j - 1) +
      familyRootsNth (fun i ↦ specAt a (P i)) j) / 2, ((hc _).add (hc _)).div_const 2,
    fun a ha ↦ ?_⟩
  have := hmono a ha j (by omega) (by omega)
  exact inFamilyRootsBand_of_lt (by rw [hn a ha]; omega) (fun _ ↦ by linarith)
    (fun _ ↦ by linarith)

/-- The cells over a preconnected semialgebraic set `E` of constant sign pattern of a family
closed under derivation: the graphs of the root functions and the bands between them are finitely
many preconnected semialgebraic sets covering `E × ℝ`, on each of which every member of the
family has constant sign. -/
theorem exists_isPreconnected_cover_of_sameSignPattern
    (hder : ∀ i, ∃ j, P j = derivative (P i)) {E : Set (σ → ℝ)} (hE : IsSemialgebraic E)
    (hEc : IsPreconnected E)
    (hpat : ∀ a ∈ E, ∀ b ∈ E, SameSignPattern (fun i ↦ specAt a (P i)) (fun i ↦ specAt b (P i))) :
    ∃ (κ : Type) (_ : Fintype κ) (D : κ → Set (Option σ → ℝ)), (∀ k, IsSemialgebraic (D k)) ∧
      (∀ k, IsPreconnected (D k)) ∧ (⋃ k, D k) = {x | x ∘ some ∈ E} ∧
      ∀ k, ∀ x ∈ D k, ∀ y ∈ D k, ∀ i,
        SignType.sign ((specAt (x ∘ some) (P i)).eval (x none)) =
          SignType.sign ((specAt (y ∘ some) (P i)).eval (y none)) := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · refine ⟨Empty, inferInstance, fun _ ↦ ∅, fun k ↦ k.elim, fun k ↦ k.elim, ?_,
      fun k ↦ k.elim⟩
    ext x
    simp
  set n := (familyRoots fun i ↦ specAt a₀ (P i)).card
  have hn : ∀ a ∈ E, (familyRoots fun i ↦ specAt a (P i)).card = n := fun a ha ↦
    (hpat a ha a₀ ha₀).card_familyRoots_eq
  let D : Fin (n + 1) ⊕ Fin n → Set (Option σ → ℝ)
    | .inl j => {x | x ∘ some ∈ E ∧ InFamilyRootsBand (fun i ↦ specAt (x ∘ some) (P i)) j (x none)}
    | .inr j => {x | x ∘ some ∈ E ∧ x none = familyRootsNth (fun i ↦ specAt (x ∘ some) (P i)) j}
  refine ⟨Fin (n + 1) ⊕ Fin n, inferInstance, D, ?_, ?_, ?_, ?_⟩
  · rintro (j | j)
    · exact isSemialgebraic_setOf_inFamilyRootsBand hder hE hpat j
    · exact isSemialgebraic_graph_familyRootsNth hder hE hpat j
  · rintro (j | j)
    · obtain ⟨s, hs, hsU⟩ := exists_continuousOn_inFamilyRootsBand hder hn hpat (j := j)
        (by omega)
      exact isPreconnected_setOf_mem_fiber hEc
        (fun a ↦ {t | InFamilyRootsBand (fun i ↦ specAt a (P i)) j t})
        (fun a _ ↦ ordConnected_setOf_inFamilyRootsBand _ _) s hs hsU
    · exact isPreconnected_setOf_mem_fiber hEc
        (fun a ↦ {familyRootsNth (fun i ↦ specAt a (P i)) j}) (fun a _ ↦ ordConnected_singleton)
        _ (continuousOn_familyRootsNth_specAt hder hpat j) (fun a _ ↦ rfl)
  · ext x
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨(j | j), hx, -⟩ <;> exact hx
    · intro hx
      set f := fun i ↦ specAt (x ∘ some) (P i)
      by_cases hZ : x none ∈ familyRoots f
      · obtain ⟨i, hi⟩ : x none ∈ Set.range ((familyRoots f).orderEmbOfFin rfl) := by
          rwa [Finset.range_orderEmbOfFin]
        refine ⟨.inr ⟨i, hn _ hx ▸ i.2⟩, hx, ?_⟩
        show x none = familyRootsNth f i
        rw [familyRootsNth_eq_orderEmbOfFin rfl i, hi]
      · refine ⟨.inl ⟨((familyRoots f).filter (· < x none)).card, ?_⟩, hx, hZ, rfl⟩
        have := Finset.card_filter_le (familyRoots f) (· < x none)
        rw [hn _ hx] at this
        omega
  · rintro (j | j) x ⟨hx, hxb⟩ y ⟨hy, hyb⟩ i
    · exact (hpat _ hx _ hy).sign_eval_of_inFamilyRootsBand hxb hyb i
    · rw [hxb, hyb]
      exact (hpat _ hx _ hy).sign_eval_familyRootsNth i (by rw [hn _ hx]; exact j.2)

end OverBase

/-! ### The decomposition theorem -/

open TarskiSeidenberg in
/-- **Semialgebraic sets are adapted to a connected semialgebraic cover.** For finitely many
semialgebraic subsets `S l` of `ℝ^σ`, `σ` finite, there is a finite cover of `ℝ^σ` by
preconnected semialgebraic sets each of which lies in or is disjoint from each `S l`. -/
theorem IsSemialgebraic.exists_isPreconnected_cover {σ : Type*} [Finite σ] {ι : Type} [Finite ι]
    (S : ι → Set (σ → ℝ)) (hS : ∀ l, IsSemialgebraic (S l)) :
    ∃ (κ : Type) (_ : Fintype κ) (D : κ → Set (σ → ℝ)), (∀ k, IsSemialgebraic (D k)) ∧
      (∀ k, IsPreconnected (D k)) ∧ (⋃ k, D k) = Set.univ ∧
      ∀ k l, D k ⊆ S l ∨ Disjoint (D k) (S l) := by
  revert ι
  refine Finite.induction_empty_option (P := fun σ ↦ ∀ {ι : Type} [Finite ι]
    (S : ι → Set (σ → ℝ)), (∀ l, IsSemialgebraic (S l)) →
    ∃ (κ : Type) (_ : Fintype κ) (D : κ → Set (σ → ℝ)), (∀ k, IsSemialgebraic (D k)) ∧
      (∀ k, IsPreconnected (D k)) ∧ (⋃ k, D k) = Set.univ ∧
      ∀ k l, D k ⊆ S l ∨ Disjoint (D k) (S l)) ?_ ?_ ?_ σ
  · intro α β e IH ι _ S hS
    obtain ⟨κ, hκ, D, hDs, hDc, hDU, hDad⟩ := IH (fun l ↦ {x : α → ℝ | x ∘ e.symm ∈ S l})
      fun l ↦ IsSemialgebraic.preimage_comp (R := ℝ) e.symm (hS l)
    have hcomp : ∀ y : β → ℝ, (y ∘ e) ∘ e.symm = y := fun y ↦ by simp [Function.comp_assoc]
    have hcomp' : ∀ x : α → ℝ, (x ∘ e.symm) ∘ e = x := fun x ↦ by simp [Function.comp_assoc]
    refine ⟨κ, hκ, fun k ↦ {y | y ∘ e ∈ D k},
      fun k ↦ IsSemialgebraic.preimage_comp (R := ℝ) e (hDs k), fun k ↦ ?_, ?_, fun k l ↦ ?_⟩
    · have : {y : β → ℝ | y ∘ e ∈ D k} = (fun x ↦ x ∘ e.symm) '' D k := by
        ext y
        refine ⟨fun hy ↦ ⟨y ∘ e, hy, hcomp y⟩, ?_⟩
        rintro ⟨x, hx, rfl⟩
        show (x ∘ e.symm) ∘ e ∈ D k
        rwa [hcomp']
      show IsPreconnected {y : β → ℝ | y ∘ e ∈ D k}
      rw [this]
      exact (hDc k).image _ (continuous_pi fun b ↦ continuous_apply _).continuousOn
    · refine eq_univ_of_forall fun y ↦ ?_
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hDU ▸ Set.mem_univ _ : y ∘ e ∈ ⋃ k, D k)
      exact mem_iUnion.2 ⟨k, hk⟩
    · rcases hDad k l with h | h
      · exact Or.inl fun y hy ↦ by simpa only [mem_setOf_eq, hcomp] using h hy
      · refine Or.inr (Set.disjoint_left.2 fun y hy hyS ↦ Set.disjoint_left.1 h hy ?_)
        simpa only [mem_setOf_eq, hcomp] using hyS
  · intro ι _ S hS
    exact ⟨Unit, inferInstance, fun _ ↦ Set.univ, fun _ ↦ IsSemialgebraic.univ,
      fun _ ↦ Set.subsingleton_of_subsingleton.isPreconnected, Set.iUnion_const _,
      fun _ l ↦ subset_or_disjoint_of_forall_mem_iff fun x _ y _ hx ↦ Subsingleton.elim x y ▸ hx⟩
  · intro α _ IH ι _ S hS
    have := Fintype.ofFinite ι
    choose κ hκ Q E hQ using fun l ↦ (hS l).exists_signConditions
    let P₀ : (Σ l, κ l) → (MvPolynomial α ℝ)[X] :=
      fun p ↦ MvPolynomial.optionEquivLeft ℝ α (Q p.1 p.2)
    set P := derivativeClosure P₀
    have hev : ∀ (x : Option α → ℝ) l m, MvPolynomial.eval x (Q l m) =
        (specAt (x ∘ some) (P (⟨l, m⟩, 0))).eval (x none) := fun x l m ↦
      eval_eq_eval_specAt_optionEquivLeft _ _
    obtain ⟨κ', _, C, hC, hCU, hCP⟩ := hasSignPatternCover P (IsSemialgebraic.univ (σ := α))
    obtain ⟨κ₁, _, E₁, hE₁s, hE₁c, hE₁U, hE₁ad⟩ := IH C hC
    have hpat : ∀ k, ∀ a ∈ E₁ k, ∀ b ∈ E₁ k,
        SameSignPattern (fun i ↦ specAt a (P i)) (fun i ↦ specAt b (P i)) := fun k a ha b hb ↦ by
      obtain ⟨k', hk'⟩ := mem_iUnion.1 (hCU ▸ Set.mem_univ a : a ∈ ⋃ k', C k')
      rcases hE₁ad k k' with h | h
      · exact hCP k' a (h ha) b (h hb)
      · exact absurd hk' (Set.disjoint_left.1 h ha)
    choose κ₂ hκ₂ D hDs hDc hDU hDsign using fun k ↦
      exists_isPreconnected_cover_of_sameSignPattern (derivativeClosure_derivative_closed P₀)
        (hE₁s k) (hE₁c k) (hpat k)
    refine ⟨Σ k, κ₂ k, inferInstance, fun p ↦ D p.1 p.2, fun p ↦ hDs _ _, fun p ↦ hDc _ _, ?_,
      fun p l ↦ ?_⟩
    · refine eq_univ_of_forall fun x ↦ ?_
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hE₁U ▸ Set.mem_univ _ : x ∘ some ∈ ⋃ k, E₁ k)
      obtain ⟨c, hc⟩ := mem_iUnion.1 ((hDU k).symm ▸ hk : x ∈ ⋃ c, D k c)
      exact mem_iUnion.2 ⟨⟨k, c⟩, hc⟩
    · refine subset_or_disjoint_of_forall_mem_iff fun x hx y hy hxS ↦ ?_
      rw [hQ l] at hxS ⊢
      simp only [mem_setOf_eq] at hxS ⊢
      convert hxS using 2 with m
      rw [hev, hev]
      exact hDsign _ _ y hy x hx _

open TarskiSeidenberg in
/-- **Cylindrical decomposition.** For finitely many semialgebraic subsets `S l` of
`ℝ^{Option σ} = ℝ^σ × ℝ` and `T l` of `ℝ^σ`, there are a finite cover of `ℝ^σ` by preconnected
semialgebraic sets `E k` adapted to the `T l` and a finite family `P` of polynomials in `t` with
coefficients in `ℝ[a]`, closed under `∂/∂t` and of constant sign pattern on each `E k`, such that
membership in each `S l` only depends on the signs of `P`. -/
theorem IsSemialgebraic.exists_cylindrical_cover {σ : Type*} [Finite σ] {ι ι' : Type} [Finite ι]
    [Finite ι'] (S : ι → Set (Option σ → ℝ)) (hS : ∀ l, IsSemialgebraic (S l))
    (T : ι' → Set (σ → ℝ)) (hT : ∀ l, IsSemialgebraic (T l)) :
    ∃ (κ : Type) (_ : Fintype κ) (E : κ → Set (σ → ℝ)) (ι₂ : Type) (_ : Fintype ι₂)
      (P : ι₂ → (MvPolynomial σ ℝ)[X]), (∀ k, IsSemialgebraic (E k)) ∧
      (∀ k, IsPreconnected (E k)) ∧ (⋃ k, E k) = Set.univ ∧
      (∀ k l, E k ⊆ T l ∨ Disjoint (E k) (T l)) ∧ (∀ i, ∃ j, P j = derivative (P i)) ∧
      (∀ k, ∀ a ∈ E k, ∀ b ∈ E k,
        SameSignPattern (fun i ↦ specAt a (P i)) (fun i ↦ specAt b (P i))) ∧
      ∀ l (x y : Option σ → ℝ), (∀ i, SignType.sign ((specAt (x ∘ some) (P i)).eval (x none)) =
        SignType.sign ((specAt (y ∘ some) (P i)).eval (y none))) → x ∈ S l → y ∈ S l := by
  have := Fintype.ofFinite ι
  choose κ hκ Q E hQ using fun l ↦ (hS l).exists_signConditions
  let P₀ : (Σ l, κ l) → (MvPolynomial σ ℝ)[X] :=
    fun p ↦ MvPolynomial.optionEquivLeft ℝ σ (Q p.1 p.2)
  have hev : ∀ (x : Option σ → ℝ) l m, MvPolynomial.eval x (Q l m) =
      (specAt (x ∘ some) (derivativeClosure P₀ (⟨l, m⟩, 0))).eval (x none) := fun x l m ↦
    eval_eq_eval_specAt_optionEquivLeft _ _
  obtain ⟨κ', _, C, hC, hCU, hCP⟩ :=
    hasSignPatternCover (derivativeClosure P₀) (IsSemialgebraic.univ (σ := σ))
  obtain ⟨κ₁, _, E₁, hE₁s, hE₁c, hE₁U, hE₁ad⟩ :=
    IsSemialgebraic.exists_isPreconnected_cover (Sum.elim C T) fun l ↦ by
      rcases l with l | l
      exacts [hC l, hT l]
  refine ⟨κ₁, inferInstance, E₁, _, inferInstance, derivativeClosure P₀, hE₁s, hE₁c, hE₁U,
    fun k l ↦ hE₁ad k (.inr l), derivativeClosure_derivative_closed P₀, ?_, ?_⟩
  · intro k a ha b hb
    obtain ⟨k', hk'⟩ := mem_iUnion.1 (hCU ▸ Set.mem_univ a : a ∈ ⋃ k', C k')
    rcases hE₁ad k (.inl k') with h | h
    · exact hCP k' a (h ha) b (h hb)
    · exact absurd hk' (Set.disjoint_left.1 h ha)
  · intro l x y hxy hx
    rw [hQ l] at hx ⊢
    simp only [mem_setOf_eq] at hx ⊢
    convert hx using 2 with m
    rw [hev, hev]
    exact (hxy _).symm

open TarskiSeidenberg in
/-- **Semialgebraic functions are piecewise continuous.** A function on a semialgebraic set `E`
with semialgebraic graph is continuous on each piece of a finite cover of `E` by preconnected
semialgebraic sets. -/
theorem exists_isPreconnected_cover_continuousOn_of_isSemialgebraic_graph {σ : Type*}
    [Finite σ] {E : Set (σ → ℝ)} (hE : IsSemialgebraic E) (f : (σ → ℝ) → ℝ)
    (hf : IsSemialgebraic {x : Option σ → ℝ | x ∘ some ∈ E ∧ x none = f (x ∘ some)}) :
    ∃ (κ : Type) (_ : Fintype κ) (E' : κ → Set (σ → ℝ)), (∀ k, IsSemialgebraic (E' k)) ∧
      (∀ k, IsPreconnected (E' k)) ∧ (⋃ k, E' k) = E ∧ ∀ k, ContinuousOn f (E' k) := by
  classical
  obtain ⟨κ, _, E₁, ι₂, _, P, hE₁s, hE₁c, hE₁U, hE₁ad, hder, hpat, hsign⟩ :=
    IsSemialgebraic.exists_cylindrical_cover (fun _ : Unit ↦ _) (fun _ ↦ hf)
      (fun _ : Unit ↦ E) fun _ ↦ hE
  set G := {x : Option σ → ℝ | x ∘ some ∈ E ∧ x none = f (x ∘ some)}
  have hG : ∀ a ∈ E, optionCons a (f a) ∈ G := fun a ha ↦ ⟨ha, rfl⟩
  have hGeq : ∀ a t, optionCons a t ∈ G → t = f a := fun a t h ↦ h.2
  refine ⟨{k // E₁ k ⊆ E}, inferInstance, fun k ↦ E₁ k, fun k ↦ hE₁s k, fun k ↦ hE₁c k, ?_,
    fun ⟨k, hk⟩ ↦ ?_⟩
  · ext a
    simp only [mem_iUnion, Subtype.exists, exists_prop]
    refine ⟨fun ⟨k, hk, ha⟩ ↦ hk ha, fun ha ↦ ?_⟩
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hE₁U ▸ Set.mem_univ a : a ∈ ⋃ k, E₁ k)
    exact ⟨k, (hE₁ad k ()).resolve_right fun h ↦ Set.disjoint_left.1 h hk ha, hk⟩
  rcases (E₁ k).eq_empty_or_nonempty with h0 | ⟨a₀, ha₀⟩
  · simp [h0]
  set F := fun a i ↦ specAt a (P i)
  have hpk := hpat k
  have hroot : f a₀ ∈ familyRoots (F a₀) := by
    by_contra hZ
    have hband : InFamilyRootsBand (F a₀) _ (f a₀) := ⟨hZ, rfl⟩
    have hev : ∀ᶠ t in 𝓝 (f a₀), InFamilyRootsBand (F a₀) _ t :=
      (isOpen_setOf_inFamilyRootsBand (F a₀) _).mem_nhds hband
    obtain ⟨t, ht, htb⟩ := hev.exists_gt
    have := hsign () (optionCons a₀ (f a₀)) (optionCons a₀ t)
      (fun i ↦ hband.sign_eval_eq htb i) (hG a₀ (hk ha₀))
    exact ht.ne' (hGeq a₀ t this)
  obtain ⟨j, hj⟩ : f a₀ ∈ Set.range ((familyRoots (F a₀)).orderEmbOfFin rfl) := by
    rwa [Finset.range_orderEmbOfFin]
  have hfeq : ∀ b ∈ E₁ k, f b = familyRootsNth (F b) j := fun b hb ↦ by
    refine (hGeq b _ (hsign () (optionCons a₀ (f a₀)) (optionCons b (familyRootsNth (F b) j))
      (fun i ↦ ?_) (hG a₀ (hk ha₀)))).symm
    simp only [optionCons_comp_some, optionCons_none]
    rw [← hj, ← familyRootsNth_eq_orderEmbOfFin rfl j]
    exact (hpk a₀ ha₀ b hb).sign_eval_familyRootsNth i j.2
  exact (continuousOn_familyRootsNth_specAt hder hpk j).congr fun b hb ↦ hfeq b hb

/-! ### Connected components -/

/-- If preconnected sets `D k` cover `S` and each lies in or is disjoint from `S`, then a connected
component of `S` is the union of the pieces `D k ⊆ S` that meet it. -/
theorem connectedComponentIn_eq_biUnion {α : Type*} [TopologicalSpace α] {κ : Type*}
    {D : κ → Set α} (hDc : ∀ k, IsPreconnected (D k)) {S : Set α} (hDU : S ⊆ ⋃ k, D k)
    (had : ∀ k, D k ⊆ S ∨ Disjoint (D k) S) (x : α) :
    connectedComponentIn S x =
      ⋃ k ∈ {k | D k ⊆ S ∧ (D k ∩ connectedComponentIn S x).Nonempty}, D k := by
  ext z
  simp only [mem_iUnion, mem_setOf_eq, exists_prop]
  constructor
  · intro hz
    have hzS := connectedComponentIn_subset S x hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hDU hzS)
    have hkS : D k ⊆ S := (had k).resolve_right fun h ↦ Set.disjoint_left.1 h hk hzS
    exact ⟨k, ⟨hkS, z, hk, hz⟩, hk⟩
  · rintro ⟨k, ⟨hkS, y, hyk, hy⟩, hzk⟩
    rw [connectedComponentIn_eq hy]
    exact (hDc k).subset_connectedComponentIn hyk hkS hzk

/-- **The connected components of a semialgebraic set are semialgebraic.** -/
theorem IsSemialgebraic.connectedComponentIn {σ : Type*} [Finite σ] {S : Set (σ → ℝ)}
    (hS : IsSemialgebraic S) (x : σ → ℝ) : IsSemialgebraic (connectedComponentIn S x) := by
  obtain ⟨κ, _, D, hDs, hDc, hDU, hDad⟩ :=
    IsSemialgebraic.exists_isPreconnected_cover (fun _ : Unit ↦ S) fun _ ↦ hS
  rw [connectedComponentIn_eq_biUnion hDc (hDU ▸ Set.subset_univ S) (fun k ↦ hDad k ()) x]
  exact IsSemialgebraic.biUnion (Set.toFinite _) fun k _ ↦ hDs k

/-- A semialgebraic set `S` has finitely many distinct sets `connectedComponentIn S x`, `x ∈ S`. -/
theorem IsSemialgebraic.finite_connectedComponentIn {σ : Type*} [Finite σ] {S : Set (σ → ℝ)}
    (hS : IsSemialgebraic S) : (Set.range fun x : S ↦ _root_.connectedComponentIn S x).Finite := by
  obtain ⟨κ, _, D, hDs, hDc, hDU, hDad⟩ :=
    IsSemialgebraic.exists_isPreconnected_cover (fun _ : Unit ↦ S) fun _ ↦ hS
  refine (Set.finite_univ.image fun T : Set κ ↦ ⋃ k ∈ T, D k).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨_, Set.mem_univ _, (connectedComponentIn_eq_biUnion hDc (hDU ▸ Set.subset_univ S)
    (fun k ↦ hDad k ()) x).symm⟩

/-- **A semialgebraic set has finitely many connected components.** -/
theorem IsSemialgebraic.finite_connectedComponents {σ : Type*} [Finite σ] {S : Set (σ → ℝ)}
    (hS : IsSemialgebraic S) : Finite (ConnectedComponents S) := by
  let g : ConnectedComponents S → Set (σ → ℝ) := fun c ↦ c.lift
    (fun x : S ↦ _root_.connectedComponentIn S x) fun x y h ↦ by
      rw [connectedComponentIn_eq_image x.2, connectedComponentIn_eq_image y.2]
      simp only [Subtype.coe_eta]
      rw [h]
  have hg : Function.Injective g := by
    rintro ⟨x⟩ ⟨y⟩ h
    change _root_.connectedComponentIn S x = _root_.connectedComponentIn S y at h
    rw [connectedComponentIn_eq_image x.2, connectedComponentIn_eq_image y.2,
      Subtype.val_injective.image_injective.eq_iff] at h
    simp only [Subtype.coe_eta] at h
    exact ConnectedComponents.coe_eq_coe.2 h
  have : Set.range g ⊆ Set.range fun x : S ↦ _root_.connectedComponentIn S x := by
    rintro _ ⟨⟨x⟩, rfl⟩
    exact ⟨x, rfl⟩
  have := (hS.finite_connectedComponentIn.subset this).to_subtype
  exact Finite.of_injective_finite_range hg

end MMP
