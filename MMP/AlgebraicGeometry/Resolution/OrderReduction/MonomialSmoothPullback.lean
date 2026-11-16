module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
public import MMP.AlgebraicGeometry.Resolution.SNCPullback
public import MMP.AlgebraicGeometry.Resolution.SNCFieldChange
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.OrderOnePullback
public import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex
public import MMP.AlgebraicGeometry.Resolution.Blowup.PointBlowupSequence
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialStepTermination

/-!
# Monomial order reduction commutes with smooth morphisms and change of fields

Let `(X, E, A)` be monomial data and `m` a marking. Let `h : Y → X` be either a smooth morphism
with `Y` quasi-compact over the ground field `k`, or the projection `X_L = X ×_k L → X` for a
field extension `k → L`. Then the monomial order reduction sequence of `(Y, h⁻¹E, h^*A, m)` is
the pull-back along `h` of the monomial order reduction sequence of `(X, E, A, m)`, with its
empty blow-ups deleted.

## Main results

* `MMP.Resolution.MonomialData.monomialOrderReduction_eq_pullback_reduction`

## Implementation notes

The hypothesis `CharZero C.k` is the standing characteristic-zero convention of Kollár's §3.

The pulled-back data on `Y` are any `MonomialData Y` whose ordered divisor is `h⁻¹E`
(`OrderedDivisor.comap`) and whose divisor is `h^*A`, the divisor with coefficient
`ord_{D'}(h^*𝒪_X(-A))` at a prime divisor `D'` of `Y`; the ground field and structure morphism
of the data on `Y` are arbitrary, as the monomial order reduction sequence does not depend on
them. The projection `X_L → X` is any morphism `h` forming a pull-back square with `X → Spec k`
and `Spec L → Spec k`.

The proof compares the two sequences step by step. Both `h` and all its canonical lifts are flat
with reduced base changes. If the pulled-back centre of a Step-3.`r` blow-up of `(X, E, A)` is
nonempty, it is the Step-3.`r` centre of the data on `Y`, the weights `m_r` agree, and the two
blow-ups correspond; if it is empty, the step is deleted and the data on `Y` stay as they are,
up to an empty entry of the divisor. A Step-3.`r` phase ends on `Y` exactly when it ends on `X`
or all remaining centres pull back to the empty set. Phases beyond the dimension are trivial.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.111]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace MMP.Resolution.MonomialData

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

/-! ### Nonempty entries of an ordered divisor -/

section Flat

variable {X : Scheme.{u}}

open Classical in
/-- The list of the nonempty entries of an ordered divisor, in their order. -/
private noncomputable def flat (E : OrderedDivisor X) : List X.IdealSheafData :=
  (List.ofFn E.E).filter fun D => D ≠ ⊤

open Classical in
/-- The indices of the nonempty entries. -/
private noncomputable def flatIdx (E : OrderedDivisor X) : List (Fin E.s) :=
  (List.finRange E.s).filter fun i => E.E i ≠ ⊤

private theorem exists_flatIdx_get (E : OrderedDivisor X) (i : Fin E.s) (hi : E.E i ≠ ⊤) :
    ∃ j, (flatIdx E).get j = i :=
  List.mem_iff_get.1 (by simp [flatIdx, hi])

private theorem ofFn_deleteEmpty (E : OrderedDivisor X) :
    List.ofFn E.deleteEmpty.E = flat E := by
  show List.ofFn (E.E ∘ (flatIdx E).get) = flat E
  rw [← List.map_ofFn, List.ofFn_get, flatIdx, flat, List.ofFn_eq_map (f := E.E),
    List.filter_map]
  rfl

private theorem eq_of_ofFn_eq {E F : OrderedDivisor X} (h : List.ofFn E.E = List.ofFn F.E) :
    E = F := by
  obtain ⟨s, e⟩ := E
  obtain ⟨t, f⟩ := F
  rw [List.ofFn_inj'] at h
  cases h
  rfl

private theorem deleteEmpty_eq_iff {E F : OrderedDivisor X} :
    E.deleteEmpty = F.deleteEmpty ↔ flat E = flat F := by
  refine ⟨fun h => ?_, fun h => eq_of_ofFn_eq ?_⟩
  · rw [← ofFn_deleteEmpty, ← ofFn_deleteEmpty, h]
  · rw [ofFn_deleteEmpty, ofFn_deleteEmpty, h]

private theorem mem_support_iff (E : OrderedDivisor X) (x : X) :
    x ∈ E.support ↔ ∃ D ∈ flat E, x ∈ D.support := by
  simp only [OrderedDivisor.support, Set.mem_iUnion, flat, List.mem_filter, List.mem_ofFn,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨E.E i, ⟨⟨i, rfl⟩, fun h => by simp [h] at hi⟩, hi⟩
  · rintro ⟨D, ⟨⟨i, rfl⟩, -⟩, hi⟩
    exact ⟨i, hi⟩

private theorem support_eq_of_flat_eq {E F : OrderedDivisor X} (h : flat E = flat F) :
    E.support = F.support := by
  ext x
  rw [mem_support_iff, mem_support_iff, h]

/-- If `T` maps values failing `p` to values failing `p`, then the filtered image of a list
under `T` depends only on the filtered list. -/
private theorem filter_map_eq_of_filter_eq {α β : Type*} (p : α → Bool) (q : β → Bool)
    (T : α → β) (hT : ∀ a, p a = false → q (T a) = false) {l l' : List α}
    (h : l.filter p = l'.filter p) : (l.map T).filter q = (l'.map T).filter q := by
  have key : ∀ l : List α, (l.map T).filter q = ((l.filter p).map T).filter q := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      by_cases ha : p a = true
      · simp [List.filter_cons, ha, ih]
      · have ha' : p a = false := by simpa using ha
        simp [List.filter_cons, ha', hT a ha', ih]
  rw [key l, key l', h]

/-- The birational transform `π⁻¹_*D` of an entry, as in `OrderedDivisor.totalTransform`. -/
private noncomputable def entryTransform (Z : X.IdealSheafData) (D : X.IdealSheafData) :
    (blowUp Z).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
    (blowUpToBase Z ⁻¹' ((D.support : Set X) \ componentsOfCodimAtLeastTwo (Z.support : Set X))))

private theorem entryTransform_top (Z : X.IdealSheafData) : entryTransform Z ⊤ = ⊤ := by
  have : (Closeds.closure (blowUpToBase Z ⁻¹' (((⊤ : X.IdealSheafData).support : Set X) \
      componentsOfCodimAtLeastTwo (Z.support : Set X)))) = ⊥ := by
    ext x
    simp [Scheme.IdealSheafData.support_top]
  rw [entryTransform, this, Scheme.IdealSheafData.vanishingIdeal_bot]

/-- The last entry of `π⁻¹_tot(E)`; it depends only on the support of `E`. -/
private noncomputable def lastEntry (Z : X.IdealSheafData) (S : Set X) :
    (blowUp Z).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
    (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X)) (_ : W ∉ componentsOf S),
      blowUpToBase Z ⁻¹' W))

open Classical in
private theorem flat_totalTransform (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    flat (E.totalTransform Z) =
      ((List.ofFn E.E).map (entryTransform Z)).filter (fun D => D ≠ ⊤) ++
        [lastEntry Z E.support].filter (fun D => D ≠ ⊤) := by
  have h : List.ofFn (E.totalTransform Z).E = List.ofFn (n := E.s + 1)
      (Fin.snoc (α := fun _ => (blowUp Z).IdealSheafData) (fun i => entryTransform Z (E.E i))
        (lastEntry Z E.support)) := rfl
  rw [flat, h, List.ofFn_succ', List.concat_eq_append, List.filter_append, List.map_ofFn]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

open Classical in
private theorem flat_totalTransform_eq {E F : OrderedDivisor X} (h : flat E = flat F)
    (Z : X.IdealSheafData) : flat (E.totalTransform Z) = flat (F.totalTransform Z) := by
  rw [flat_totalTransform, flat_totalTransform, support_eq_of_flat_eq h]
  congr 1
  refine filter_map_eq_of_filter_eq _ _ _ (fun D hD => ?_) h
  simp only [ne_eq, decide_eq_false_iff_not, not_not] at hD ⊢
  rw [hD, entryTransform_top]

end Flat

/-! ### The Step-3.`r` centre only sees the nonempty entries -/

section Monomial

variable {X : Scheme.{u}}

/-- Monomial data with the divisor replaced. -/
private abbrev withEm (C : MonomialData X) (E : OrderedDivisor X) : MonomialData X :=
  { C with E := E }

private theorem strictMono_flatIdx_get (E : OrderedDivisor X) : StrictMono (flatIdx E).get :=
  List.SortedLT.strictMono_get ((List.sortedLT_finRange _).pairwise.filter _).sortedLT

private theorem map_lt_map_of_lex {n s : ℕ} {g : Fin n → Fin s} (hg : StrictMono g)
    {l₁ l₂ : List (Fin n)} (h : List.Lex (· < ·) l₁ l₂) :
    List.Lex (· < ·) (l₁.map g) (l₂.map g) := by
  induction h with
  | nil => exact List.Lex.nil
  | cons h ih => exact List.Lex.cons ih
  | rel h => exact List.Lex.rel (hg h)

private theorem map_le_map_of_le {n s : ℕ} {g : Fin n → Fin s} (hg : StrictMono g)
    {l₁ l₂ : List (Fin n)} (h : l₁ ≤ l₂) : l₁.map g ≤ l₂.map g := by
  rcases le_iff_lt_or_eq.1 h with h | rfl
  · exact le_of_lt (List.lex_lt.1 (map_lt_map_of_lex hg (List.lex_lt.2 h)))
  · exact le_rfl

/-- A finset of `Fin n` is determined by its sorted list. -/
private theorem eq_of_sort_eq {n : ℕ} {J K : Finset (Fin n)}
    (h : J.sort (· ≤ ·) = K.sort (· ≤ ·)) : J = K := by
  classical
  have := congrArg List.toFinset h
  rwa [Finset.sort_toFinset, Finset.sort_toFinset] at this

open Classical in
private theorem stepIndex_spec (D : MonomialData X) (r : ℕ) (h : ∃ J P, D.IsMaxPiece r J P) :
    (∃ P, D.IsMaxPiece r (D.stepIndex r) P) ∧
      ∀ J P, D.IsMaxPiece r J P → (D.stepIndex r).sort (· ≤ ·) ≤ J.sort (· ≤ ·) := by
  unfold MonomialData.stepIndex
  dsimp only
  split
  · next hS =>
    obtain ⟨h1, h2⟩ :=
      (Finset.exists_min_image _ (fun J : Finset (Fin D.E.s) => J.sort (· ≤ ·)) hS).choose_spec
    exact ⟨(Finset.mem_filter.1 h1).2,
      fun J P hP => h2 J (Finset.mem_filter.2 ⟨Finset.mem_univ _, P, hP⟩)⟩
  · next hS =>
    obtain ⟨J, P, hP⟩ := h
    exact absurd ⟨J, Finset.mem_filter.2 ⟨Finset.mem_univ _, P, hP⟩⟩ hS

open Classical in
private theorem stepIndex_of_not (D : MonomialData X) (r : ℕ) (h : ¬ ∃ J P, D.IsMaxPiece r J P) :
    D.stepIndex r = ∅ := by
  unfold MonomialData.stepIndex
  dsimp only
  split
  · next hS =>
    obtain ⟨J, hJ⟩ := hS
    exact absurd ⟨J, (Finset.mem_filter.1 hJ).2⟩ h
  · rfl

section Reindex

variable (C : MonomialData X) {n : ℕ} {g : Fin n → Fin C.E.s} (hg : StrictMono g)
  (hgr : ∀ i, C.E.E i ≠ ⊤ → ∃ j, g j = i)

/-- The monomial data with the entries of the divisor reindexed along `g`. -/
private abbrev reindex (g : Fin n → Fin C.E.s) : MonomialData X := withEm C ⟨n, C.E.E ∘ g⟩

include hg in
private theorem reindex_stratum (J : Finset (Fin n)) :
    (reindex C g).stratum J = C.stratum (J.map ⟨g, hg.injective⟩) := by
  ext x
  simp [MonomialData.stratum]

include hg in
private theorem reindex_stratumWeight (J : Finset (Fin n)) (x : X) :
    (reindex C g).stratumWeight J x = C.stratumWeight (J.map ⟨g, hg.injective⟩) x := by
  simp only [MonomialData.stratumWeight, Finset.sum_map]
  rfl

include hg hgr in
private theorem exists_map_eq_of_mem_stratum {J : Finset (Fin C.E.s)} {x : X}
    (hx : x ∈ C.stratum J) : ∃ J' : Finset (Fin n), J'.map ⟨g, hg.injective⟩ = J := by
  classical
  refine ⟨Finset.univ.filter fun j => g j ∈ J, ?_⟩
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  refine ⟨fun ⟨j, hj, hji⟩ => hji ▸ hj, fun hi => ?_⟩
  have hxi : x ∈ ((C.E.E i).support : Set X) := by
    simp only [MonomialData.stratum, Set.mem_iInter] at hx
    exact hx i hi
  obtain ⟨j, rfl⟩ := hgr i fun h => by
    rw [h, Scheme.IdealSheafData.support_top] at hxi
    exact hxi
  exact ⟨j, hi, rfl⟩

include hg hgr in
private theorem reindex_maxStratumWeight (r : ℕ) :
    (reindex C g).maxStratumWeight r = C.maxStratumWeight r := by
  let F : Finset (Fin C.E.s) → ℕ := fun J =>
    ⨆ (_ : J.card = r) (x : X) (_ : x ∈ C.stratum J), C.stratumWeight J x
  have hF : ∀ J' : Finset (Fin n),
      (⨆ (_ : J'.card = r) (x : X) (_ : x ∈ (reindex C g).stratum J'),
        (reindex C g).stratumWeight J' x) = F (J'.map ⟨g, hg.injective⟩) := by
    intro J'
    simp only [F, Finset.card_map, reindex_stratum C hg, reindex_stratumWeight C hg]
  have h0 : ∀ J, (∀ J' : Finset (Fin n), J'.map ⟨g, hg.injective⟩ ≠ J) → F J = 0 := by
    intro J hJ
    refine Nat.eq_zero_of_le_zero (ciSup_le' fun _ => ciSup_le' fun x => ciSup_le' fun hx => ?_)
    obtain ⟨J', hJ'⟩ := exists_map_eq_of_mem_stratum C hg hgr hx
    exact absurd hJ' (hJ J')
  show (⨆ J' : Finset (Fin n), ⨆ (_ : J'.card = r) (x : X) (_ : x ∈ (reindex C g).stratum J'),
      (reindex C g).stratumWeight J' x) = ⨆ J, F J
  simp only [hF]
  refine le_antisymm (ciSup_le' fun J' => le_ciSup (Finite.bddAbove_range F) _)
    (ciSup_le' fun J => ?_)
  by_cases hJ : ∃ J' : Finset (Fin n), J'.map ⟨g, hg.injective⟩ = J
  · obtain ⟨J', rfl⟩ := hJ
    exact le_ciSup (Finite.bddAbove_range
      (fun J' : Finset (Fin n) => F (J'.map ⟨g, hg.injective⟩))) J'
  · push Not at hJ
    rw [h0 J hJ]
    exact Nat.zero_le _

include hg hgr in
private theorem reindex_isMaxPiece (r : ℕ) (J : Finset (Fin n)) (P : Set X) :
    (reindex C g).IsMaxPiece r J P ↔ C.IsMaxPiece r (J.map ⟨g, hg.injective⟩) P := by
  simp only [MonomialData.IsMaxPiece, Finset.card_map, reindex_stratum C hg,
    reindex_stratumWeight C hg, reindex_maxStratumWeight C hg hgr]

include hg hgr in
private theorem reindex_stepIndex (r : ℕ) :
    C.stepIndex r = ((reindex C g).stepIndex r).map ⟨g, hg.injective⟩ := by
  have hsort : ∀ J' : Finset (Fin n), (J'.map ⟨g, hg.injective⟩).sort (· ≤ ·) =
      (J'.sort (· ≤ ·)).map g := fun J' =>
    (Finset.map_sort _ _ _ _ fun a _ b _ => hg.le_iff_le.symm).symm
  by_cases h : ∃ J P, (reindex C g).IsMaxPiece r J P
  · have h' : ∃ J P, C.IsMaxPiece r J P := by
      obtain ⟨J, P, hP⟩ := h
      exact ⟨_, P, (reindex_isMaxPiece C hg hgr r J P).1 hP⟩
    obtain ⟨⟨P₀, hP₀⟩, h₀⟩ := stepIndex_spec (reindex C g) r h
    obtain ⟨⟨P₁, hP₁⟩, h₁⟩ := stepIndex_spec C r h'
    obtain ⟨x, hx, -⟩ := hP₁.2.1
    obtain ⟨J₁', hJ₁'⟩ := exists_map_eq_of_mem_stratum C hg hgr hx
    have ha := h₁ _ P₀ ((reindex_isMaxPiece C hg hgr r _ P₀).1 hP₀)
    have hb := h₀ J₁' P₁ ((reindex_isMaxPiece C hg hgr r J₁' P₁).2 (hJ₁' ▸ hP₁))
    have hb' := map_le_map_of_le hg hb
    rw [← hsort, ← hsort, hJ₁'] at hb'
    exact eq_of_sort_eq (le_antisymm ha hb')
  · have h' : ¬ ∃ J P, C.IsMaxPiece r J P := by
      rintro ⟨J, P, hP⟩
      obtain ⟨x, hx, -⟩ := hP.2.1
      obtain ⟨J', rfl⟩ := exists_map_eq_of_mem_stratum C hg hgr hx
      exact h ⟨J', P, (reindex_isMaxPiece C hg hgr r J' P).2 hP⟩
    rw [stepIndex_of_not C r h', stepIndex_of_not _ r h, Finset.map_empty]

include hg hgr in
private theorem reindex_stepCenter (r : ℕ) :
    (reindex C g).stepCenter r = C.stepCenter r := by
  unfold MonomialData.stepCenter
  have : {P | (reindex C g).IsMaxPiece r ((reindex C g).stepIndex r) P} =
      {P | C.IsMaxPiece r (C.stepIndex r) P} := by
    ext P
    rw [reindex_stepIndex C hg hgr r]
    exact reindex_isMaxPiece C hg hgr r _ P
  rw [this]

end Reindex

private theorem deleteEmpty_stepCenter (C : MonomialData X) (r : ℕ) :
    (withEm C C.E.deleteEmpty).stepCenter r = C.stepCenter r :=
  reindex_stepCenter C (strictMono_flatIdx_get C.E) (exists_flatIdx_get C.E) r

private theorem deleteEmpty_maxStratumWeight (C : MonomialData X) (r : ℕ) :
    (withEm C C.E.deleteEmpty).maxStratumWeight r = C.maxStratumWeight r :=
  reindex_maxStratumWeight C (strictMono_flatIdx_get C.E) (exists_flatIdx_get C.E) r

/-- The centre of a Step-3.`r` blow-up only sees the nonempty entries of the divisor. -/
private theorem stepCenter_congr (C : MonomialData X) (E : OrderedDivisor X)
    (h : flat E = flat C.E) (r : ℕ) : (withEm C E).stepCenter r = C.stepCenter r := by
  rw [← deleteEmpty_stepCenter (withEm C E), ← deleteEmpty_stepCenter C]
  show (withEm C E.deleteEmpty).stepCenter r = (withEm C C.E.deleteEmpty).stepCenter r
  rw [deleteEmpty_eq_iff.2 h]

/-- `m_r(E, A)` only sees the nonempty entries of the divisor. -/
private theorem maxStratumWeight_congr (C : MonomialData X) (E : OrderedDivisor X)
    (h : flat E = flat C.E) (r : ℕ) : (withEm C E).maxStratumWeight r = C.maxStratumWeight r := by
  rw [← deleteEmpty_maxStratumWeight (withEm C E), ← deleteEmpty_maxStratumWeight C]
  show (withEm C E.deleteEmpty).maxStratumWeight r = (withEm C C.E.deleteEmpty).maxStratumWeight r
  rw [deleteEmpty_eq_iff.2 h]

/-- The Step-3.`r` blow-up of `C` along a given centre `Z`. -/
private noncomputable def stepAt (C : MonomialData X) (m : ℕ) (Z : X.IdealSheafData) :
    MonomialData (blowUp Z) where
  k := C.k
  sX := blowUpToBase Z ≫ C.sX
  E := C.E.totalTransform Z
  A D' :=
    (multAt ((divisorIdeal C.A).comap (blowUpToBase Z)) D'.genericPoint).toNat -
      m * (multAt (Z.comap (blowUpToBase Z)) D'.genericPoint).toNat

private theorem step_eq_stepAt (C : MonomialData X) (m r : ℕ) :
    C.step m r = stepAt C m (C.stepCenter r) := rfl

end Monomial

/-! ### The sequence only depends on `E` and `A` -/

section Congr

private theorem stepCenter_eq_of_eq {X : Scheme.{u}} {C C' : MonomialData X} (hE : C.E = C'.E)
    (hA : C.A = C'.A) (r : ℕ) : C.stepCenter r = C'.stepCenter r := by
  cases C; cases C'
  dsimp only at hE hA
  subst hE; subst hA; rfl

private theorem maxStratumWeight_eq_of_eq {X : Scheme.{u}} {C C' : MonomialData X}
    (hE : C.E = C'.E) (hA : C.A = C'.A) (r : ℕ) : C.maxStratumWeight r = C'.maxStratumWeight r := by
  cases C; cases C'
  dsimp only at hE hA
  subst hE; subst hA; rfl

/-- Transport of a function of `stepAt C m W` along an equality of centres. -/
private theorem stepAt_congr_fun {X : Scheme.{u}} {α : Sort*} {W W' : X.IdealSheafData}
    (e : W = W') (C : MonomialData X) (m : ℕ) (F : ∀ {Y : Scheme.{u}}, MonomialData Y → α) :
    F (stepAt C m W) = F (stepAt C m W') := by
  subst e; rfl

/-- Transport of a blow-up sequence starting with `W` along an equality of centres. -/
private theorem cons_stepAt_congr {X : Scheme.{u}} {W W' : X.IdealSheafData} (e : W = W')
    (C : MonomialData X) (m : ℕ)
    (G : ∀ {Y : Scheme.{u}}, MonomialData Y → ClosedBlowupSequence Y) :
    ClosedBlowupSequence.cons W (G (stepAt C m W)) =
      ClosedBlowupSequence.cons W' (G (stepAt C m W')) := by
  subst e; rfl

private theorem stepAt_E_eq {X : Scheme.{u}} {C C' : MonomialData X} (hE : C.E = C'.E) (m : ℕ)
    (W : X.IdealSheafData) : (stepAt C m W).E = (stepAt C' m W).E := by
  show C.E.totalTransform W = C'.E.totalTransform W
  rw [hE]

private theorem stepAt_A_eq {X : Scheme.{u}} {C C' : MonomialData X} (hA : C.A = C'.A) (m : ℕ)
    (W : X.IdealSheafData) : (stepAt C m W).A = (stepAt C' m W).A := by
  show (fun D' : AlgebraicGeometry.PrimeDivisor (blowUp W) =>
      (multAt ((divisorIdeal C.A).comap (blowUpToBase W)) D'.genericPoint).toNat -
        m * (multAt (W.comap (blowUpToBase W)) D'.genericPoint).toNat) = _
  rw [hA]; rfl

private theorem iterate_mr_eq_of_eq (m r : ℕ) : ∀ (N : ℕ) {X : Scheme.{u}}
    (C C' : MonomialData X), C.E = C'.E → C.A = C'.A →
      (C.iterate m r N).2.maxStratumWeight r = (C'.iterate m r N).2.maxStratumWeight r
  | 0, _, C, C', hE, hA => maxStratumWeight_eq_of_eq hE hA r
  | N + 1, _, C, C', hE, hA => by
    show ((stepAt C m (C.stepCenter r)).iterate m r N).2.maxStratumWeight r =
      ((stepAt C' m (C'.stepCenter r)).iterate m r N).2.maxStratumWeight r
    exact (stepAt_congr_fun (stepCenter_eq_of_eq hE hA r) C m
      (fun D => (D.iterate m r N).2.maxStratumWeight r)).trans
      (iterate_mr_eq_of_eq m r N _ _ (stepAt_E_eq hE m _) (stepAt_A_eq hA m _))

private theorem stepPhase_eq_of_eq (m r : ℕ)
    (K K' : ∀ {Y : Scheme.{u}}, MonomialData Y → ClosedBlowupSequence Y)
    (hK : ∀ {Y : Scheme.{u}} (D D' : MonomialData Y), D.E = D'.E → D.A = D'.A → K D = K' D') :
    ∀ (q : ℕ) {X : Scheme.{u}} (C C' : MonomialData X), C.E = C'.E → C.A = C'.A →
      stepPhase m r K q C = stepPhase m r K' q C'
  | 0, _, C, C', hE, hA => hK C C' hE hA
  | q + 1, _, C, C', hE, hA => by
    show ClosedBlowupSequence.cons (C.stepCenter r)
        (stepPhase m r K q (stepAt C m (C.stepCenter r))) =
      ClosedBlowupSequence.cons (C'.stepCenter r)
        (stepPhase m r K' q (stepAt C' m (C'.stepCenter r)))
    refine (cons_stepAt_congr (stepCenter_eq_of_eq hE hA r) C m
      (fun D => stepPhase m r K q D)).trans ?_
    exact congrArg _ (stepPhase_eq_of_eq m r K K' hK q _ _ (stepAt_E_eq hE m _)
      (stepAt_A_eq hA m _))

/-- The monomial order reduction depends only on the divisors `E` and `A`, not on the ground
field or the structure morphism. -/
private theorem from_eq_of_eq (m : ℕ) : ∀ (j r : ℕ) {X : Scheme.{u}} (C C' : MonomialData X),
    C.E = C'.E → C.A = C'.A →
      monomialOrderReductionFrom m j r C = monomialOrderReductionFrom m j r C'
  | 0, _, _, _, _, _, _ => rfl
  | j + 1, r, _, C, C', hE, hA => by
    have hp : ∀ {N}, (C.iterate m r N).2.maxStratumWeight r < m ↔
        (C'.iterate m r N).2.maxStratumWeight r < m := by
      intro N; rw [iterate_mr_eq_of_eq m r N C C' hE hA]
    have hK := fun {Y : Scheme.{u}} (D D' : MonomialData Y) (hE : D.E = D'.E)
      (hA : D.A = D'.A) => from_eq_of_eq m j (r + 1) D D' hE hA
    simp only [monomialOrderReductionFrom]
    by_cases hex : ∃ N, (C.iterate m r N).2.maxStratumWeight r < m
    · have hex' : ∃ N, (C'.iterate m r N).2.maxStratumWeight r < m := hex.imp fun _ => hp.1
      rw [dif_pos hex, dif_pos hex', Nat.find_congr' hp]
      exact stepPhase_eq_of_eq m r _ _ hK _ C C' hE hA
    · have hex' : ¬ ∃ N, (C'.iterate m r N).2.maxStratumWeight r < m :=
        fun ⟨N, hN⟩ => hex ⟨N, hp.2 hN⟩
      rw [dif_neg hex, dif_neg hex']
      exact hK C C' hE hA

end Congr

/-! ### Pulled-back data -/

section Pullback

/-- The coefficients `ord_{D'}(h^*𝒪_X(-A))` of the pull-back `h^*A`. -/
private noncomputable def pullCoeff {X Y : Scheme.{u}} (h : Y ⟶ X)
    (A : AlgebraicGeometry.PrimeDivisor X → ℕ) : AlgebraicGeometry.PrimeDivisor Y → ℕ :=
  fun D' => (multAt ((divisorIdeal A).comap h) D'.genericPoint).toNat

/-- `D` is the pull-back of `C` along `h`, up to empty entries of the divisor: both are monomial
data in characteristic zero, `h` is flat with reduced base changes, the nonempty entries of the
divisor of `D` are those of `h⁻¹E`, and `D.A = h^*A`. -/
private structure Rel {X Y : Scheme.{u}} (h : Y ⟶ X) (C : MonomialData X) (D : MonomialData Y) :
    Prop where
  monoC : C.IsMonomialData
  charC : CharZero C.k
  monoD : D.IsMonomialData
  charD : CharZero D.k
  flatHom : IsReducedFlatBaseChange h
  flatE : flat D.E = flat (C.E.comap h)
  coeff : D.A = pullCoeff h C.A

/-- When `h⁻¹Z = ∅`, the lift `Y → B_ZX` is `B_{h⁻¹Z}Y ≅ Y` followed by the canonical lift. -/
private theorem blowUpLift_eq_of_comap_eq_top {X Y : Scheme.{u}} (h : Y ⟶ X)
    (Z : X.IdealSheafData) (hZ : Z.comap h = ⊤) [IsIso (blowUpToBase (Z.comap h))] :
    blowUpLift Z h (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h Z hZ) =
      inv (blowUpToBase (Z.comap h)) ≫ canonicalLift h Z :=
  (blowUpLift_unique Z h (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h Z hZ)
    (inv (blowUpToBase (Z.comap h)) ≫ canonicalLift h Z) (by
    rw [Category.assoc, canonicalLift_comp_blowUpToBase, IsIso.inv_hom_id_assoc])).symm

private theorem isReducedFlatBaseChange_blowUpLift {X Y : Scheme.{u}} {h : Y ⟶ X}
    (hh : IsReducedFlatBaseChange h) (Z : X.IdealSheafData) (hZ : Z.comap h = ⊤) :
    IsReducedFlatBaseChange
      (blowUpLift Z h (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h Z hZ)) := by
  haveI := Kollar.isIso_blowUpToBase_of_eq_top hZ
  rw [blowUpLift_eq_of_comap_eq_top h Z hZ]
  exact IsReducedFlatBaseChange.of_isPullback
    (IsPullback.of_horiz_isIso (fst := inv (blowUpToBase (Z.comap h)))
      (snd := inv (blowUpToBase (Z.comap h)) ≫ canonicalLift h Z) (f := canonicalLift h Z)
      (g := 𝟙 _) ⟨by simp⟩) (hh.canonicalLift Z)

open Classical in
/-- The prime divisors through `x` with nonzero coefficient in `A`. -/
private noncomputable def throughDivisors {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) (x : X) : Finset (AlgebraicGeometry.PrimeDivisor X) :=
  hfin.toFinset.filter fun D => x ∈ (D.support : Set X)

private theorem mem_throughDivisors {X : Scheme.{u}} {C : MonomialData X}
    {hfin : (Function.support C.A).Finite} {x : X} {D : AlgebraicGeometry.PrimeDivisor X} :
    D ∈ throughDivisors C hfin x ↔ C.A D ≠ 0 ∧ x ∈ (D.support : Set X) := by
  simp [throughDivisors]

/-- The stalk of `𝒪_X(-A)` at `x` is `∏_{D ∋ x} (𝒪_X(-D))_x ^ a_D`. -/
private theorem stalk_monomialIdeal_eq_prod {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) (x : X) :
    IdealSheafData.stalk C.monomialIdeal x =
      ∏ D ∈ throughDivisors C hfin x, IdealSheafData.stalk D.idealSheaf x ^ C.A D := by
  classical
  unfold MonomialData.monomialIdeal divisorIdeal
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) fun D hD => by
      simpa using fun h0 => hD (by simp [h0]),
    Aux.stalk_prod, ← Finset.prod_filter_mul_prod_filter_not hfin.toFinset
      fun D => x ∈ (D.support : Set X)]
  conv_rhs => rw [← mul_one (∏ D ∈ _, _)]
  congr 1
  · exact Finset.prod_congr rfl fun D _ => Aux.stalk_pow _ _ _
  · refine Finset.prod_eq_one fun D hD => ?_
    rw [Aux.stalk_pow, (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2
      (Finset.mem_filter.1 hD).2, Ideal.top_pow, Ideal.one_eq_top]

/-- Each prime divisor through `x` with nonzero coefficient is a component of a member of `E`
through `x`. -/
private theorem exists_component_of_mem_throughDivisors {X : Scheme.{u}} {C : MonomialData X}
    (hC : C.IsMonomialData) {x : X} {D : AlgebraicGeometry.PrimeDivisor X}
    (hD : D ∈ throughDivisors C hC.2.2.2.2.1 x) : ∃ i : Fin C.E.s,
      D.support ∈ componentsOf ((C.E.E i).support : Set X) ∧ x ∈ ((C.E.E i).support : Set X) := by
  rw [mem_throughDivisors] at hD
  obtain ⟨i, hi⟩ := hC.2.2.2.2.2 D hD.1
  exact ⟨i, hi, hi.1.2 hD.2⟩

/-- The order of the unit ideal is `0`. -/
private theorem idealOrder_top {R : Type*} [CommRing R] [IsLocalRing R] :
    idealOrder (⊤ : Ideal R) = 0 := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) bot_le
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · exact absurd ((top_le_iff.1 hj).symm ▸ Ideal.pow_le_self hj0.ne' :
      (⊤ : Ideal R) ≤ IsLocalRing.maximalIdeal R)
      fun h' => (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 h')

/-- The order of an ideal sheaf at a point outside its support is `0`. -/
private theorem mem_support_of_multAt_ne_zero {Y : Scheme.{u}} (J : Y.IdealSheafData) (y : Y)
    (h : multAt J y ≠ 0) : y ∈ (J.support : Set Y) := by
  by_contra hy
  apply h
  rw [multAt, (IdealSheafData.stalk_eq_top_iff_notMem_support J y).2 hy, idealOrder_top]

/-- The support of `𝒪_X(-A)` lies in `Supp E`. -/
private theorem exists_mem_E_of_mem_support_monomialIdeal {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) {x : X} (hx : x ∈ (C.monomialIdeal.support : Set X)) :
    ∃ i : Fin C.E.s, x ∈ ((C.E.E i).support : Set X) := by
  classical
  by_contra hno
  push Not at hno
  refine (IdealSheafData.stalk_eq_top_iff_notMem_support _ x).1 ?_ hx
  rw [stalk_monomialIdeal_eq_prod C hC.2.2.2.2.1, ← Ideal.one_eq_top]
  refine Finset.prod_eq_one fun D hD => ?_
  obtain ⟨i, -, hxi⟩ := exists_component_of_mem_throughDivisors hC hD
  exact absurd hxi (hno i)

/-- Two irreducible closed subsets of codimension one are not strictly nested. -/
private theorem not_lt_of_codimension_eq_one {Y : Scheme.{u}} {A B : IrreducibleCloseds Y}
    (hA : codimension A = 1) (hB : codimension B = 1) : ¬ A < B := fun hlt => by
  have h2 : codimension B + 1 ≤ codimension A := Order.coheight_add_one_le hlt
  rw [hA, hB] at h2
  exact absurd h2 (by decide)

/-- In a Noetherian space, a prime divisor whose generic point lies in a closed set of pure
codimension one is an irreducible component of it. -/
private theorem support_mem_componentsOf_of_isPureCodimOne {Y : Scheme.{u}} [NoetherianSpace Y]
    (S : Closeds Y) (hS : MMP.Mori.IsPureCodimOne S) (D : AlgebraicGeometry.PrimeDivisor Y)
    (hD : D.genericPoint ∈ (S : Set Y)) : (D.support : Set Y) ∈ componentsOf (S : Set Y) := by
  have hDS : (D.support : Set Y) ⊆ S := by
    rw [Aux.support_eq_closure_genericPoint]
    exact closure_minimal (Set.singleton_subset_iff.2 hD) S.isClosed
  have hDirr : IsIrreducible (D.support : Set Y) := by
    rw [Aux.support_eq_closure_genericPoint]; exact isIrreducible_singleton.closure
  refine ⟨⟨hDirr, hDS⟩, fun W hW hle => ?_⟩
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
  obtain ⟨V, hV, hWV⟩ := isIrreducible_iff_sUnion_isClosed.mp hW.1 hfin.toFinset
    (fun V hV => Aux.isClosed_of_mem_componentsOf S.isClosed (hfin.mem_toFinset.1 hV))
    (by rw [Set.Finite.coe_toFinset]; exact hW.2.trans hcov)
  rw [Set.Finite.mem_toFinset] at hV
  have hVc : IsClosed V := Aux.isClosed_of_mem_componentsOf S.isClosed hV
  let V' : IrreducibleCloseds Y := ⟨V, hV.1.1, hVc⟩
  have hV1 : codimension V' = 1 := hS V' ⟨hV.1.2, fun W' hW' hle' => hV.2 ⟨W'.2, hW'⟩ hle'⟩
  have hD1 := D.codimension_one
  suffices hDV : (D.support : Set Y) = V from hDV ▸ hWV
  refine (hle.trans hWV).antisymm' ?_ |>.symm
  by_contra hne
  have hlt : IrreducibleCloseds.closureSingleton D.genericPoint < V' := by
    refine lt_of_le_of_ne (fun y hy => ?_) fun heq => hne ?_
    · have : closure {D.genericPoint} ⊆ V := by
        rw [← Aux.support_eq_closure_genericPoint]; exact hle.trans hWV
      exact this hy
    · intro y hy
      have : y ∈ (V' : Set Y) := hy
      rw [← heq] at this
      change y ∈ closure {D.genericPoint} at this
      rwa [← Aux.support_eq_closure_genericPoint] at this
  exact not_lt_of_codimension_eq_one hD1 hV1 hlt

/-- `(X, 𝒪_X, E)` is an snc triple for monomial data `(X, E, A)`. -/
private theorem mem_sncTriples_top {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) :
    (⟨⟨X, ⊤, C.E⟩, C.k, C.sX⟩ : FieldBlowupTriple.{u}) ∈ sncTriples := by
  obtain ⟨hsm, hlft, hqc, hsnc, -, -⟩ := hC
  refine ⟨hk, hsm, hlft, hqc, fun η _ => ?_, hsnc.1, hsnc.2⟩
  rw [Aux.stalk_top]
  exact top_ne_bot

/-- A prime divisor of `Y` along which `h^*A` has a positive coefficient is an irreducible
component of a member of `h⁻¹E`. -/
private theorem isComponent_of_pullCoeff_ne_zero {X Y : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (h : Y ⟶ X) {L : Type u} [Field L]
    (sY : Y ⟶ Spec (.of L)) [LocallyOfFiniteType sY] [QuasiCompact sY]
    (hY : (C.E.comap h).IsOrderedSNC sY)
    (D' : AlgebraicGeometry.PrimeDivisor Y) (hD' : pullCoeff h C.A D' ≠ 0) :
    (C.E.comap h).IsComponent D' := by
  haveI := Aux.noetherianSpace_of_finiteType sY
  have hmult : multAt ((divisorIdeal C.A).comap h) D'.genericPoint ≠ 0 := by
    intro h0
    apply hD'
    simp [pullCoeff, h0]
  have h1 := mem_support_of_multAt_ne_zero _ _ hmult
  rw [Scheme.IdealSheafData.support_comap] at h1
  obtain ⟨i, hi⟩ := exists_mem_E_of_mem_support_monomialIdeal C hC h1
  refine ⟨i, support_mem_componentsOf_of_isPureCodimOne ((C.E.E i).comap h).support
    (hY.2.1 i).2.1 D' ?_⟩
  rw [Scheme.IdealSheafData.support_comap]
  exact hi

/-- Pulled-back data with snc divisor over a field are monomial data. -/
private theorem isMonomialData_of_snc {X Y : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (h : Y ⟶ X) [Flat h] {L : Type u} [Field L]
    (sY : Y ⟶ Spec (.of L)) (hsm : MMP.Mori.IsSmoothScheme sY) (hlft : LocallyOfFiniteType sY)
    (hqc : QuasiCompact sY) (hY : (C.E.comap h).IsOrderedSNC sY) :
    ({ k := L, sX := sY, E := C.E.comap h, A := pullCoeff h C.A } :
      MonomialData Y).IsMonomialData := by
  haveI := hlft
  haveI := hqc
  have hcomp := isComponent_of_pullCoeff_ne_zero C hC h sY hY
  refine ⟨hsm, hlft, hqc, hY, ?_, hcomp⟩
  exact (Aux.finite_primeDivisor_of_isComponent sY (C.E.comap h).E).subset
    fun D' hD' => hcomp D' hD'

/-- The pull-back of monomial data along a smooth morphism `h` with `Y` quasi-compact over `k`
is monomial data over `k`. -/
private theorem isMonomialData_comap_of_smooth {X Y : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) (h : Y ⟶ X) (hsm : Smooth h)
    (hqc : QuasiCompact (h ≫ C.sX)) :
    ({ k := C.k, sX := h ≫ C.sX, E := C.E.comap h, A := pullCoeff h C.A } :
      MonomialData Y).IsMonomialData := by
  haveI := hsm
  haveI := hqc
  obtain ⟨-, hsmY, hlftY, hqcY, -, hdiv, hsnc⟩ :=
    pullback_mem_sncTriples (mem_sncTriples_top C hC hk) h
  exact isMonomialData_of_snc C hC h (h ≫ C.sX) hsmY hlftY hqcY ⟨hdiv, hsnc⟩

/-- The pull-back of monomial data along the projection `X_L → X` of a field extension is
monomial data over `L`. -/
private theorem isMonomialData_comap_of_isPullback {X Y : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) (h : Y ⟶ X) {L : Type u} [Field L]
    (σ : C.k →+* L) (q : Y ⟶ Spec (.of L))
    (sq : IsPullback h q C.sX (Spec.map (CommRingCat.ofHom σ))) :
    ({ k := L, sX := q, E := C.E.comap h, A := pullCoeff h C.A } :
      MonomialData Y).IsMonomialData := by
  haveI : PerfectField C.k := PerfectField.ofCharZero
  have ht := fieldChange_mem_sncTriples (mem_sncTriples_top C hC hk) σ
  set t' := (⟨⟨X, ⊤, C.E⟩, C.k, C.sX⟩ : FieldBlowupTriple.{u}).fieldChange σ
  haveI : QuasiCompact t'.sX := ht.2.2.2.1
  let e := sq.isoPullback
  haveI : IsOpenImmersion e.hom := inferInstance
  let f : Y ⟶ t'.X := e.hom
  haveI : Smooth f := inferInstanceAs (Smooth e.hom)
  haveI : IsIso f := inferInstanceAs (IsIso e.hom)
  haveI : QuasiCompact (f ≫ t'.sX) := inferInstance
  obtain ⟨-, hsmY, hlftY, hqcY, -, hdiv, hsnc⟩ := pullback_mem_sncTriples ht f
  have hq : (t'.pullback f).sX = q := sq.isoPullback_hom_snd
  have hE : (t'.pullback f).E = C.E.comap h := by
    show OrderedDivisor.comap (C.E.comap (pullback.fst _ _)) e.hom = C.E.comap h
    simp only [OrderedDivisor.comap, ← Scheme.IdealSheafData.comap_comp, e,
      sq.isoPullback_hom_fst]
  rw [hq] at hsmY hlftY hqcY hsnc
  rw [hE] at hdiv hsnc
  haveI : Flat h := (IsReducedFlatBaseChange.of_isPullback sq.flip
    (IsReducedFlatBaseChange.specMap σ)).flat
  exact isMonomialData_of_snc C hC h q hsmY hlftY hqcY ⟨hdiv, hsnc⟩

/-- The pulled-back data on `Y`, related to `C`. -/
private theorem exists_rel_init {X : Scheme.{u}} (C : MonomialData X) (hC : C.IsMonomialData)
    (hk : CharZero C.k) {Y : Scheme.{u}} (h : Y ⟶ X)
    (hh : (Smooth h ∧ QuasiCompact (h ≫ C.sX)) ∨
      ∃ (L : Type u) (_ : Field L) (σ : C.k →+* L) (q : Y ⟶ Spec (.of L)),
        IsPullback h q C.sX (Spec.map (CommRingCat.ofHom σ)))
    (D : MonomialData Y) (hE : D.E = C.E.comap h) (hA : D.A = pullCoeff h C.A) :
    ∃ D₀ : MonomialData Y, D₀.E = D.E ∧ D₀.A = D.A ∧ Rel h C D₀ := by
  haveI : PerfectField C.k := PerfectField.ofCharZero
  rcases hh with ⟨hsm, hqc⟩ | ⟨L, _, σ, q, sq⟩
  · haveI := hsm
    exact ⟨⟨C.k, h ≫ C.sX, C.E.comap h, pullCoeff h C.A⟩, hE.symm, hA.symm,
      ⟨hC, hk, isMonomialData_comap_of_smooth C hC hk h hsm hqc, hk,
        IsReducedFlatBaseChange.of_smooth h, rfl, rfl⟩⟩
  · haveI : CharZero L := charZero_of_injective_ringHom σ.injective
    exact ⟨⟨L, q, C.E.comap h, pullCoeff h C.A⟩, hE.symm, hA.symm,
      ⟨hC, hk, isMonomialData_comap_of_isPullback C hC hk h σ q sq, ‹_›,
        IsReducedFlatBaseChange.of_isPullback sq.flip (IsReducedFlatBaseChange.specMap σ),
        rfl, rfl⟩⟩

/-! #### The components of a Step-3.`r` centre -/

private theorem stepCenter_support_subset_stratum {X : Scheme.{u}} (M : MonomialData X) (r : ℕ) :
    ((M.stepCenter r).support : Set X) ⊆ M.stratum (M.stepIndex r) := by
  rw [MonomialData.stepCenter, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure]
  refine closure_minimal ?_ (isClosed_biInter fun j _ => (M.E.E j).support.isClosed)
  rintro y ⟨P, ⟨-, ⟨x0, -, rfl⟩, -⟩, hy⟩
  exact connectedComponentIn_subset _ _ hy

private theorem card_stepIndex_of_mem_stepCenter {X : Scheme.{u}} (M : MonomialData X) {r : ℕ}
    {x : X} (hx : x ∈ ((M.stepCenter r).support : Set X)) : (M.stepIndex r).card = r := by
  rw [MonomialData.stepCenter, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure] at hx
  obtain ⟨P, ⟨hP, -⟩, -⟩ := Set.nonempty_sUnion.1 (closure_nonempty_iff.1 ⟨x, hx⟩)
  exact hP

/-- The union of the max pieces of `E^J` is closed. -/
private theorem isClosed_sUnion_isMaxPiece {X : Scheme.{u}} (M : MonomialData X)
    (hM : M.IsMonomialData) (r : ℕ) (J : Finset (Fin M.E.s)) :
    IsClosed (⋃₀ {P | M.IsMaxPiece r J P}) := by
  obtain ⟨-, hlft, hqc, -, -, -⟩ := id hM
  haveI := hlft
  haveI := hqc
  haveI : NoetherianSpace X := Aux.noetherianSpace_of_finiteType M.sX
  have hS : IsClosed (M.stratum J) := isClosed_biInter fun j _ => (M.E.E j).support.isClosed
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf hS
  have heq : ⋃₀ {P | M.IsMaxPiece r J P} =
      ⋃₀ {W | W ∈ componentsOf (M.stratum J) ∧ ∃ P, M.IsMaxPiece r J P ∧ W ⊆ P} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨P, hP, hy⟩
      obtain ⟨x0, -, rfl⟩ := hP.2.1
      obtain ⟨W, hW, hyW⟩ := Set.mem_sUnion.1 (hcov (connectedComponentIn_subset _ _ hy))
      refine ⟨W, ⟨hW, _, hP, ?_⟩, hyW⟩
      rw [connectedComponentIn_eq hy]
      exact (IsIrreducible.isConnected hW.1.1).isPreconnected.subset_connectedComponentIn hyW hW.1.2
    · rintro y ⟨W, ⟨-, P, hP, hWP⟩, hyW⟩
      exact ⟨P, hP, hWP hyW⟩
  rw [heq]
  refine (hfin.subset fun W hW => hW.1).isClosed_sUnion fun W hW => ?_
  have hW := hW.1
  rw [← closure_subset_iff_isClosed]
  exact hW.2 ⟨hW.1.1.closure, closure_minimal hW.1.2 hS⟩ subset_closure

private theorem coe_support_stepCenter {X : Scheme.{u}} (M : MonomialData X)
    (hM : M.IsMonomialData) (r : ℕ) :
    ((M.stepCenter r).support : Set X) = ⋃₀ {P | M.IsMaxPiece r (M.stepIndex r) P} := by
  rw [MonomialData.stepCenter, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure, (isClosed_sUnion_isMaxPiece M hM r _).closure_eq]

/-- For `r ≥ 2`, every irreducible component of the centre has codimension `≥ 2`: its generic
point lies on two members of the snc divisor `E`. -/
private theorem two_le_codimension_of_mem_componentsOf_stepCenter {X : Scheme.{u}}
    (M : MonomialData X) (hM : M.IsMonomialData) {r : ℕ} (hr : 2 ≤ r) {W : Set X}
    (hW : W ∈ componentsOf ((M.stepCenter r).support : Set X)) :
    2 ≤ codimension (irreducibleClosure hW.1.1) := by
  classical
  obtain ⟨x, hxW⟩ := hW.1.1.nonempty
  have hScard := card_stepIndex_of_mem_stepCenter M (hW.1.2 hxW)
  have hZS := stepCenter_support_subset_stratum M r
  obtain ⟨-, hlft, hqc, hsnc, -⟩ := hM
  haveI : LocallyOfFiniteType M.sX := hlft
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian M.sX
  set S := M.stepIndex r
  set W' := irreducibleClosure hW.1.1
  have hcod : codimension W' = Order.coheight W'.isIrreducible.genericPoint := by
    rw [codimension_eq_coheight]
    exact (Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)) W').symm
  rw [hcod]
  set ξ := W'.isIrreducible.genericPoint
  have hξ : ξ ∈ closure W := by
    have h := W'.isIrreducible.isGenericPoint_genericPoint_closure.mem
    change ξ ∈ closure (closure W) at h
    rwa [closure_closure] at h
  have hξZ : ξ ∈ ((M.stepCenter r).support : Set X) :=
    closure_minimal hW.1.2 (M.stepCenter r).support.isClosed hξ
  have hξS := hZS hξZ
  simp only [MonomialData.stratum, Set.mem_iInter] at hξS
  by_contra hlt
  push Not at hlt
  obtain ⟨n', z', c', hz', -, hinj⟩ := hsnc.2.2 ξ
  have hn' : (n' : ℕ∞) = Order.coheight ξ := by
    have h : (n' : WithBot ℕ∞) = Order.coheight ξ := by
      rw [← hz'.2, AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
    exact_mod_cast h
  have hn'2 : n' ≤ 1 := by
    have : (n' : ℕ∞) < 2 := hn' ▸ hlt
    have : n' < 2 := by exact_mod_cast this
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  haveI : Subsingleton (Fin n') := Fin.subsingleton_iff_le_one.2 hn'2
  exact hab (congrArg Subtype.val
    (hinj (a₁ := ⟨a, hξS a ha⟩) (a₂ := ⟨b, hξS b hb⟩) (Subsingleton.elim _ _)))

/-- An irreducible component of a member of `E`, all of whose members are of pure codimension
one, is an irreducible component of `Supp E`. -/
private theorem mem_componentsOf_support_of_mem_componentsOf_E {X : Scheme.{u}}
    [NoetherianSpace X] (E : OrderedDivisor X)
    (hE : ∀ i, MMP.Mori.IsPureCodimOne (E.E i).support) {j : Fin E.s} {W : Set X}
    (hW : W ∈ componentsOf ((E.E j).support : Set X)) : W ∈ componentsOf E.support := by
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf (E.E j).support.isClosed hW
  let W₀ : IrreducibleCloseds X := ⟨W, hW.1.1, hWc⟩
  have hW1 : codimension W₀ = 1 :=
    hE j W₀ ⟨hW.1.2, fun V hV hle => hW.2 ⟨V.isIrreducible, hV⟩ hle⟩
  refine ⟨⟨hW.1.1, hW.1.2.trans (Set.subset_iUnion (fun i => ((E.E i).support : Set X)) j)⟩,
    fun W' hW' hle => ?_⟩
  have hEc : IsClosed E.support := isClosed_iUnion_of_finite fun i => (E.E i).support.isClosed
  obtain ⟨_, hz, hWz⟩ := isIrreducible_iff_sUnion_isClosed.mp hW'.1.closure
    (Finset.univ.image fun i => ((E.E i).support : Set X))
    (fun z hz => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      exact (E.E i).support.isClosed)
    (by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (closure_minimal hW'.2 hEc hx)
      exact Set.mem_sUnion.2 ⟨_, Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩),
        hi⟩)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf (E.E i).support.isClosed
  obtain ⟨V, hV, hWV⟩ := isIrreducible_iff_sUnion_isClosed.mp hW'.1.closure hfin.toFinset
    (fun V hV => Aux.isClosed_of_mem_componentsOf (E.E i).support.isClosed
      (hfin.mem_toFinset.1 hV))
    (by rw [Set.Finite.coe_toFinset]; exact hWz.trans hcov)
  rw [Set.Finite.mem_toFinset] at hV
  have hVc : IsClosed V := Aux.isClosed_of_mem_componentsOf (E.E i).support.isClosed hV
  let V₀ : IrreducibleCloseds X := ⟨V, hV.1.1, hVc⟩
  have hV1 : codimension V₀ = 1 :=
    hE i V₀ ⟨hV.1.2, fun V' hV' hle' => hV.2 ⟨V'.isIrreducible, hV'⟩ hle'⟩
  suffices hWeq : W = V by
    rw [hWeq]
    exact subset_closure.trans hWV
  by_contra hne
  have hlt : W₀ < V₀ := lt_of_le_of_ne (hle.trans (subset_closure.trans hWV)) fun heq =>
    hne (congrArg (fun T : IrreducibleCloseds X => (T : Set X)) heq)
  exact not_lt_of_codimension_eq_one hW1 hV1 hlt

/-- For `r = 1`, every irreducible component of the centre is an irreducible component of
`Supp E`: the centre is a union of connected components of a member `E^j`. -/
private theorem mem_componentsOf_support_of_mem_componentsOf_stepCenter_one {X : Scheme.{u}}
    (M : MonomialData X) (hM : M.IsMonomialData) {W : Set X}
    (hW : W ∈ componentsOf ((M.stepCenter 1).support : Set X)) : W ∈ componentsOf M.E.support := by
  classical
  obtain ⟨x, hxW⟩ := hW.1.1.nonempty
  have hxZ : x ∈ ((M.stepCenter 1).support : Set X) := hW.1.2 hxW
  have hScard := card_stepIndex_of_mem_stepCenter M hxZ
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hScard
  have hstrat : M.stratum (M.stepIndex 1) = ((M.E.E j).support : Set X) := by
    rw [hj]; simp [MonomialData.stratum]
  have hZcoe := coe_support_stepCenter M hM 1
  obtain ⟨-, hlft, hqc, hsnc, -⟩ := id hM
  haveI := hlft
  haveI := hqc
  haveI : NoetherianSpace X := Aux.noetherianSpace_of_finiteType M.sX
  have hZE : ((M.stepCenter 1).support : Set X) ⊆ (M.E.E j).support :=
    hstrat ▸ stepCenter_support_subset_stratum M 1
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf (M.E.E j).support.isClosed
  obtain ⟨V, hV, hWV⟩ := isIrreducible_iff_sUnion_isClosed.mp hW.1.1 hfin.toFinset
    (fun V hV => Aux.isClosed_of_mem_componentsOf (M.E.E j).support.isClosed
      (hfin.mem_toFinset.1 hV))
    (by rw [Set.Finite.coe_toFinset]; exact (hW.1.2.trans hZE).trans hcov)
  rw [Set.Finite.mem_toFinset] at hV
  -- `V` lies in the max piece through `x`
  have hVZ : V ⊆ ((M.stepCenter 1).support : Set X) := by
    rw [hZcoe] at hxZ ⊢
    obtain ⟨P, hP, hxP⟩ := hxZ
    obtain ⟨x0, hx0, hPeq⟩ := hP.2.1
    have hxS : x ∈ M.stratum (M.stepIndex 1) := by
      rw [hPeq] at hxP; exact connectedComponentIn_subset _ _ hxP
    have hcc : connectedComponentIn (M.stratum (M.stepIndex 1)) x = P := by
      rw [hPeq] at hxP ⊢; exact (connectedComponentIn_eq hxP).symm
    have hsub : V ⊆ connectedComponentIn (M.stratum (M.stepIndex 1)) x :=
      (IsIrreducible.isConnected hV.1.1).isPreconnected.subset_connectedComponentIn (hWV hxW)
        (hstrat ▸ hV.1.2)
    rw [hcc] at hsub
    exact fun v hv => ⟨P, hP, hsub hv⟩
  have hWeq : W = V := hWV.antisymm (hW.2 ⟨hV.1.1, hVZ⟩ hWV)
  rw [hWeq]
  exact mem_componentsOf_support_of_mem_componentsOf_E M.E (fun i => (hsnc.2.1 i).2.1) hV

private theorem componentsOfCodimAtLeastTwo_stepCenter {X : Scheme.{u}} (M : MonomialData X)
    (hM : M.IsMonomialData) {r : ℕ} (hr : 1 ≤ r) :
    componentsOfCodimAtLeastTwo ((M.stepCenter r).support : Set X) =
      if r = 1 then ∅ else ((M.stepCenter r).support : Set X) := by
  obtain ⟨-, hlft, hqc, hsnc, -⟩ := id hM
  haveI := hlft
  haveI := hqc
  haveI : NoetherianSpace X := Aux.noetherianSpace_of_finiteType M.sX
  split_ifs with h1
  · subst h1
    refine Set.eq_empty_of_subset_empty fun y hy => ?_
    obtain ⟨W, hW, h2, -⟩ := (mem_componentsOfCodimAtLeastTwo _ y).1 hy
    exact OrderedDivisor.not_two_le_codimension_of_mem_componentsOf M.E
      (fun i => (hsnc.2.1 i).2.1)
      (mem_componentsOf_support_of_mem_componentsOf_stepCenter_one M hM hW) h2
  · refine Set.Subset.antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨W, hW, -, hyW⟩ := (mem_componentsOfCodimAtLeastTwo _ y).1 hy
      exact hW.1.2 hyW
    · obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf (M.stepCenter r).support.isClosed
      obtain ⟨W, hW, hyW⟩ := hcov hy
      exact (mem_componentsOfCodimAtLeastTwo _ y).2
        ⟨W, hW, two_le_codimension_of_mem_componentsOf_stepCenter M hM (by omega) hW, hyW⟩

private theorem iUnion_lastEntry_stepCenter {X : Scheme.{u}} (M : MonomialData X)
    (hM : M.IsMonomialData) {r : ℕ} (hr : 1 ≤ r) {T : Type*} (f : T → X) :
    (⋃ (W : Set X) (_ : W ∈ componentsOf ((M.stepCenter r).support : Set X))
        (_ : W ∉ componentsOf M.E.support), f ⁻¹' W) =
      f ⁻¹' (if r = 1 then ∅ else ((M.stepCenter r).support : Set X)) := by
  obtain ⟨-, hlft, hqc, hsnc, -⟩ := id hM
  haveI := hlft
  haveI := hqc
  haveI : NoetherianSpace X := Aux.noetherianSpace_of_finiteType M.sX
  split_ifs with h1
  · subst h1
    refine Set.eq_empty_of_subset_empty fun y hy => ?_
    simp only [Set.mem_iUnion] at hy
    obtain ⟨W, hW, hWE, -⟩ := hy
    exact hWE (mem_componentsOf_support_of_mem_componentsOf_stepCenter_one M hM hW)
  · ext y
    simp only [Set.mem_iUnion, Set.mem_preimage]
    refine ⟨fun ⟨W, hW, _, hyW⟩ => hW.1.2 hyW, fun hy => ?_⟩
    obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf (M.stepCenter r).support.isClosed
    obtain ⟨W, hW, hyW⟩ := hcov hy
    exact ⟨W, hW, fun hWE => OrderedDivisor.not_two_le_codimension_of_mem_componentsOf M.E
      (fun i => (hsnc.2.1 i).2.1) hWE
      (two_le_codimension_of_mem_componentsOf_stepCenter M hM (by omega) hW), hyW⟩

private theorem totalTransform_E_castSucc {X : Scheme.{u}} (E : OrderedDivisor X)
    (Z : X.IdealSheafData) (i : Fin E.s) :
    (E.totalTransform Z).E i.castSucc = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (blowUpToBase Z ⁻¹' (((E.E i).support : Set X) \
        componentsOfCodimAtLeastTwo (Z.support : Set X)))) := by
  simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc]

private theorem totalTransform_E_last {X : Scheme.{u}} (E : OrderedDivisor X)
    (Z : X.IdealSheafData) :
    (E.totalTransform Z).E (Fin.last E.s) = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
        (_ : W ∉ componentsOf E.support), blowUpToBase Z ⁻¹' W)) := by
  simp only [OrderedDivisor.totalTransform, Fin.snoc_last]

/-- The reduced closure of `π⁻¹(T)` pulls back along the canonical lift to the reduced closure of
`π⁻¹(h⁻¹T)`. -/
private theorem comap_canonicalLift_vanishingIdeal {X Y : Scheme.{u}} {h : Y ⟶ X}
    (hh : IsReducedFlatBaseChange h) (Z : X.IdealSheafData) (T : Set X) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (blowUpToBase Z ⁻¹' T))).comap
        (canonicalLift h Z) =
      Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (blowUpToBase (Z.comap h) ⁻¹' (h ⁻¹' T))) := by
  have hl := hh.canonicalLift Z
  have := hl.universallyOpen
  refine hl.comap_vanishingIdeal _ _ ?_
  rw [Closeds.coe_closure, Closeds.coe_closure,
    ((canonicalLift h Z).isOpenMap).preimage_closure_eq_closure_preimage
      (canonicalLift h Z).continuous]
  congr 1
  have hfun : ∀ y, blowUpToBase Z (canonicalLift h Z y) = h (blowUpToBase (Z.comap h) y) := by
    intro y
    have := congrArg (fun f : blowUp (Z.comap h) ⟶ X => f y)
      (canonicalLift_comp_blowUpToBase h Z)
    simpa using this
  ext y
  simp only [Set.mem_preimage]
  rw [hfun]

/-- The total transform commutes with the canonical lift along the Step-3.`r` centre. -/
private theorem totalTransform_comap_canonicalLift {X Y : Scheme.{u}} {h : Y ⟶ X}
    {C : MonomialData X} {D : MonomialData Y} (hR : Rel h C D) {r : ℕ} (hr : 1 ≤ r)
    (hc : D.stepCenter r = (C.stepCenter r).comap h) :
    flat ((C.E.comap h).totalTransform ((C.stepCenter r).comap h)) =
      flat ((C.E.totalTransform (C.stepCenter r)).comap (canonicalLift h (C.stepCenter r))) := by
  classical
  set Z := C.stepCenter r with hZ
  set S : Set X := if r = 1 then ∅ else (Z.support : Set X) with hS
  have hWs : (((Z.comap h).support : Set Y)) = h ⁻¹' (Z.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hSY : (if r = 1 then (∅ : Set Y) else ((Z.comap h).support : Set Y)) = h ⁻¹' S := by
    rw [hS]; split_ifs <;> simp [hWs]
  have hC2 : componentsOfCodimAtLeastTwo (Z.support : Set X) = S :=
    componentsOfCodimAtLeastTwo_stepCenter C hR.monoC hr
  have hD2 : componentsOfCodimAtLeastTwo ((Z.comap h).support : Set Y) = h ⁻¹' S := by
    rw [← hSY, ← hc]; exact componentsOfCodimAtLeastTwo_stepCenter D hR.monoD hr
  have hCl : (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
      (_ : W ∉ componentsOf C.E.support), blowUpToBase Z ⁻¹' W) = blowUpToBase Z ⁻¹' S :=
    iUnion_lastEntry_stepCenter C hR.monoC hr _
  have hsuppD : (C.E.comap h).support = D.E.support := support_eq_of_flat_eq hR.flatE.symm
  have hDl : (⋃ (W : Set Y) (_ : W ∈ componentsOf ((Z.comap h).support : Set Y))
      (_ : W ∉ componentsOf (C.E.comap h).support), blowUpToBase (Z.comap h) ⁻¹' W) =
      blowUpToBase (Z.comap h) ⁻¹' (h ⁻¹' S) := by
    rw [hsuppD, ← hSY]
    have := iUnion_lastEntry_stepCenter D hR.monoD hr (blowUpToBase (D.stepCenter r))
    rw [hc] at this
    exact this
  have hent : ∀ i, ((C.E.totalTransform Z).E i).comap (canonicalLift h Z) =
      ((C.E.comap h).totalTransform (Z.comap h)).E i := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      have hr' : ((C.E.comap h).totalTransform (Z.comap h)).E (Fin.last C.E.s) =
          Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (⋃ (W : Set Y) (_ : W ∈ componentsOf ((Z.comap h).support : Set Y))
            (_ : W ∉ componentsOf (C.E.comap h).support), blowUpToBase (Z.comap h) ⁻¹' W)) :=
        totalTransform_E_last (C.E.comap h) (Z.comap h)
      rw [totalTransform_E_last, hr', hCl, hDl]
      exact comap_canonicalLift_vanishingIdeal hR.flatHom Z S
    | cast i =>
      have hEi : (((C.E.E i).comap h).support : Set Y) = h ⁻¹' ((C.E.E i).support : Set X) := by
        rw [Scheme.IdealSheafData.support_comap]; rfl
      have hr' : ((C.E.comap h).totalTransform (Z.comap h)).E i.castSucc =
          Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (blowUpToBase (Z.comap h) ⁻¹' ((((C.E.E i).comap h).support : Set Y) \
            componentsOfCodimAtLeastTwo ((Z.comap h).support : Set Y)))) :=
        totalTransform_E_castSucc (C.E.comap h) (Z.comap h) i
      rw [totalTransform_E_castSucc, hr', hC2, hD2, hEi,
        comap_canonicalLift_vanishingIdeal hR.flatHom Z,
        Set.preimage_diff]
  have : (C.E.totalTransform Z).comap (canonicalLift h Z) =
      (C.E.comap h).totalTransform (Z.comap h) := by
    show (⟨C.E.s + 1, fun i => ((C.E.totalTransform Z).E i).comap (canonicalLift h Z)⟩ :
      OrderedDivisor _) = ⟨C.E.s + 1, ((C.E.comap h).totalTransform (Z.comap h)).E⟩
    congr 1
    funext i
    exact hent i
  rw [this]

/-! #### Orders along prime divisors on schemes with regular local rings -/

section DivisorialIdeals

open IsLocalRing

private theorem primeDivisor_eq_of_support_subset {Y : Scheme.{u}}
    {D D'' : AlgebraicGeometry.PrimeDivisor Y} (h : (D.support : Set Y) ⊆ D''.support) :
    D = D'' := by
  refine Aux.PrimeDivisor.eq_of_support_eq (h.antisymm ?_)
  by_contra hne
  have hlt : IrreducibleCloseds.closureSingleton D.genericPoint <
      IrreducibleCloseds.closureSingleton D''.genericPoint := by
    refine lt_of_le_of_ne (fun y hy => ?_) fun heq => hne ?_
    · have : closure {D.genericPoint} ⊆ closure {D''.genericPoint} := by
        rw [← Aux.support_eq_closure_genericPoint, ← Aux.support_eq_closure_genericPoint]
        exact h
      exact this hy
    · have := congrArg (fun W : IrreducibleCloseds Y => (W : Set Y)) heq
      change closure {D.genericPoint} = closure {D''.genericPoint} at this
      rw [Aux.support_eq_closure_genericPoint, Aux.support_eq_closure_genericPoint, this]
  exact not_lt_of_codimension_eq_one D.codimension_one D''.codimension_one hlt

/-- The order of `𝔪^a` is `a` in a Noetherian local domain which is not a field. -/
private theorem idealOrder_maximalIdeal_pow {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsDomain R] (h : IsLocalRing.maximalIdeal R ≠ ⊥) (a : ℕ) :
    idealOrder (IsLocalRing.maximalIdeal R ^ a) = a := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂_of_le
    (f := fun (j : ℕ) (_ : IsLocalRing.maximalIdeal R ^ a ≤ IsLocalRing.maximalIdeal R ^ j) =>
      (j : ℕ∞)) a le_rfl le_rfl)
  by_contra hlt
  have hlt' : a + 1 ≤ j := by exact_mod_cast Order.add_one_le_of_lt (not_le.1 hlt)
  have heq : IsLocalRing.maximalIdeal R ^ a = IsLocalRing.maximalIdeal R ^ (a + 1) :=
    le_antisymm (hj.trans (Ideal.pow_le_pow_right hlt')) (Ideal.pow_le_pow_right (by omega))
  have := MMP.Resolution.maximalIdeal_pow_injective h heq
  omega

/-- The stalk of `𝒪_X(-A)` at the generic point of a prime divisor `D` is `𝔪^{a_D}`. -/
private theorem stalk_monomialIdeal_genericPoint {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) (D : AlgebraicGeometry.PrimeDivisor X) :
    IdealSheafData.stalk C.monomialIdeal D.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk D.genericPoint) ^ C.A D := by
  classical
  rw [stalk_monomialIdeal_eq_prod C hfin]
  have hT : throughDivisors C hfin D.genericPoint ⊆ {D} := by
    intro D'' hD''
    rw [Finset.mem_singleton]
    refine (primeDivisor_eq_of_support_subset ?_).symm
    rw [Aux.support_eq_closure_genericPoint D]
    exact closure_minimal (Set.singleton_subset_iff.2 (mem_throughDivisors.1 hD'').2)
      D''.idealSheaf.support.isClosed
  rw [Finset.prod_subset hT fun D'' hD'' hnot => by
    rw [Finset.mem_singleton] at hD''
    subst hD''
    have : C.A D'' = 0 := by
      by_contra h0
      exact hnot (mem_throughDivisors.2 ⟨h0, by
        rw [Aux.support_eq_closure_genericPoint]; exact subset_closure rfl⟩)
    rw [this, pow_zero], Finset.prod_singleton, Aux.stalk_idealSheaf_genericPoint]

/-- The order of `𝒪_X(-A)` along a prime divisor `D` is its coefficient `a_D`. -/
private theorem multAt_monomialIdeal_genericPoint {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (D : AlgebraicGeometry.PrimeDivisor X) :
    multAt C.monomialIdeal D.genericPoint = C.A D := by
  obtain ⟨hsm, hlft, -, -, hfin, -⟩ := id hC
  haveI := hlft
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  haveI := Aux.smooth_of_isSmoothScheme' C.sX hsm
  have := isRegularLocalRing_stalk_of_smooth_over_field C.sX D.genericPoint
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk D.genericPoint)
  rw [multAt, stalk_monomialIdeal_genericPoint C hfin]
  exact idealOrder_maximalIdeal_pow (maximalIdeal_stalk_genericPoint_ne_bot D) _

/-- In a local domain of dimension at most one, a nonzero prime is the maximal ideal. -/
private theorem eq_maximalIdeal_of_ringKrullDim_le_one {R : Type*} [CommRing R] [IsLocalRing R]
    [IsDomain R] (h : ringKrullDim R ≤ 1) {p : Ideal R} [p.IsPrime] (hp : p ≠ ⊥) :
    p = IsLocalRing.maximalIdeal R := by
  haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.2 h
  exact IsLocalRing.eq_maximalIdeal
    ((Ring.krullDimLE_one_iff_of_isPrime_bot.1 inferInstance) p hp inferInstance)

/-- In a discrete valuation ring the order of `(x)` is the valuation of `x`. -/
private theorem idealOrder_span_eq_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {x : R} (hx : x ≠ 0) :
    idealOrder (Ideal.span {x}) = IsDiscreteValuationRing.addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ n rfl]
  have hm : maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have key : ∀ j : ℕ, Ideal.span {(u : R) * ϖ ^ n} ≤ maximalIdeal R ^ j ↔ j ≤ n := by
    intro j
    rw [hm, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton,
      Units.dvd_mul_left]
    exact _root_.pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit
  refine le_antisymm (iSup₂_le fun j hj => by exact_mod_cast (key j).1 hj) ?_
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : Ideal.span {(u : R) * ϖ ^ n} ≤
    maximalIdeal R ^ j) => (j : ℕ∞)) n ((key n).2 le_rfl) le_rfl

/-- A regular local ring of dimension one is a discrete valuation ring. -/
private theorem isDiscreteValuationRing_of_ringKrullDim_eq_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] (h : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid R
  have hnf : ¬ IsField R := fun hf => by
    have := ringKrullDim_eq_zero_of_isField hf
    rw [h] at this
    exact absurd this (by decide)
  have e := (IsDiscreteValuationRing.TFAE R hnf).out 1 4
  refine e.2 ⟨inferInstance, maximalIdeal R,
    ⟨fun h0 => hnf ((isField_iff_maximalIdeal_eq).2 h0), inferInstance⟩, fun P hP => ?_⟩
  haveI := hP.2
  exact eq_maximalIdeal_of_ringKrullDim_le_one h.le hP.1

private theorem maximalIdeal_eq_span_of_isLocalization {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsLocalRing S] [Algebra R S] {p : R} (hp : Prime p)
    [(Ideal.span {p}).IsPrime] [IsLocalization.AtPrime S (Ideal.span {p})] :
    maximalIdeal S = Ideal.span {algebraMap R S p} ∧ maximalIdeal S ≠ ⊥ := by
  have hm : maximalIdeal S = Ideal.span {algebraMap R S p} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {p}) S, Ideal.map_span,
      Set.image_singleton]
  refine ⟨hm, ?_⟩
  rw [hm, Ne, Ideal.span_singleton_eq_bot]
  intro h0
  obtain ⟨⟨c, hc⟩, hc0⟩ := (IsLocalization.map_eq_zero_iff (Ideal.span {p}).primeCompl S p).1 h0
  have : c = 0 := (mul_eq_zero.1 hc0).resolve_right hp.ne_zero
  exact hc (by rw [this]; exact Ideal.zero_mem _)

private theorem idealOrder_span_algebraMap_eq_emultiplicity {R S : Type*} [CommRing R]
    [IsDomain R] [UniqueFactorizationMonoid R] [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsDomain S] [Algebra R S] {p : R} (hp : Prime p) [(Ideal.span {p}).IsPrime]
    [IsLocalization.AtPrime S (Ideal.span {p})] {f : R} (hf : f ≠ 0) :
    idealOrder (Ideal.span {algebraMap R S f}) = emultiplicity p f := by
  have hfin := FiniteMultiplicity.of_prime_left hp hf
  obtain ⟨h, hfh, hndvd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [hfin.emultiplicity_eq_multiplicity]
  generalize multiplicity p f = e at hfh ⊢
  have hunit : IsUnit (algebraMap R S h) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff S _ h).2 (by
      change h ∉ Ideal.span {p}
      rwa [Ideal.mem_span_singleton])
  obtain ⟨hm, hm0⟩ := maximalIdeal_eq_span_of_isLocalization (S := S) hp
  have hspan : Ideal.span {algebraMap R S f} = maximalIdeal S ^ e := by
    rw [hfh, map_mul, map_pow, ← Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_eq_top.2 hunit, Ideal.mul_top, ← Ideal.span_singleton_pow, ← hm]
  rw [hspan]
  exact idealOrder_maximalIdeal_pow hm0 _

private theorem coheight_and_multAt_fromSpecStalk {Y : Scheme.{u}}
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (x : Y)
    {p : Y.presheaf.stalk x} (hp : Prime p) (q : PrimeSpectrum (Y.presheaf.stalk x))
    (hq : q.asIdeal = Ideal.span {p}) :
    Order.coheight (Y.fromSpecStalk x q) = 1 ∧
      ∀ (J : Y.IdealSheafData) (f : Y.presheaf.stalk x), IdealSheafData.stalk J x =
        Ideal.span {f} → f ≠ 0 → multAt J (Y.fromSpecStalk x q) = emultiplicity p f := by
  obtain ⟨I, hI⟩ := q
  simp only at hq
  subst hq
  have hyx := fromSpecStalk_specializes_self x ⟨Ideal.span {p}, hI⟩
  letI : Algebra (Y.presheaf.stalk x) (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) :=
    (Y.presheaf.stalkSpecializes hyx).hom.toAlgebra
  haveI hloc := Stacks.Chow.isLocalization_stalk_of_specializes hyx ⟨Ideal.span {p}, hI⟩ rfl
  haveI := hreg x
  haveI := hreg (Y.fromSpecStalk x ⟨_, hI⟩)
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk x)
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩))
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk x)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩))
      (Ideal.span {p}) := hloc
  obtain ⟨hm, hm0⟩ := maximalIdeal_eq_span_of_isLocalization
    (S := Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) hp
  have hnf : ¬ IsField (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) :=
    fun hf => hm0 ((isField_iff_maximalIdeal_eq).1 hf)
  have hdvr : IsDiscreteValuationRing (Y.presheaf.stalk (Y.fromSpecStalk x ⟨_, hI⟩)) :=
    ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).2 (show (maximalIdeal _).IsPrincipal from
      ⟨⟨_, hm⟩⟩)
  refine ⟨?_, fun J f hJ hf => ?_⟩
  · have h1 := ringKrullDim_stalk_eq_coheight (Y.fromSpecStalk x ⟨_, hI⟩)
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
    exact_mod_cast h1.symm
  · rw [multAt, Aux.stalk_eq_map_stalkSpecializes J hyx, hJ, Ideal.map_span, Set.image_singleton]
    exact idealOrder_span_algebraMap_eq_emultiplicity hp hf

/-- Invertible ideals on a scheme with regular local rings are determined by their orders along
prime divisors. -/
private theorem eq_of_forall_multAt_genericPoint_eq {Y : Scheme.{u}}
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (J₁ J₂ : Y.IdealSheafData)
    (h₁ : Stacks.Divisors.IsEffectiveCartierDivisor J₁)
    (h₂ : Stacks.Divisors.IsEffectiveCartierDivisor J₂)
    (h : ∀ D : AlgebraicGeometry.PrimeDivisor Y,
      multAt J₁ D.genericPoint = multAt J₂ D.genericPoint) : J₁ = J₂ := by
  refine AlgebraicGeometry.IdealSheafData.eq_of_stalk_eq _ _ fun x => ?_
  haveI := hreg x
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk x)
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk x)
  obtain ⟨f, hf, hJf⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ h₁ x
  obtain ⟨g, hg, hJg⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ h₂ x
  have key : ∀ p, Prime p → emultiplicity p f = emultiplicity p g := fun p hp => by
    obtain ⟨hcoh, hmult⟩ := coheight_and_multAt_fromSpecStalk hreg x hp
      ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩ rfl
    have := h (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh)
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] at this
    rw [← hmult J₁ f hJf hf.ne_zero, ← hmult J₂ g hJg hg.ne_zero, this]
  rw [hJf, hJg, Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd
    ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hf.ne_zero).2 fun p hp => (key p hp).le)
    ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hg.ne_zero).2 fun p hp => (key p hp).ge)

/-- The ideal sheaf `𝒪_Y(-A)` of an effective divisor on a smooth scheme is invertible. -/
private theorem isEffectiveCartierDivisor_divisorIdeal {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hY : MMP.Mori.IsSmoothScheme sY)
    (A : AlgebraicGeometry.PrimeDivisor Y → ℕ) (hA : (Function.support A).Finite) :
    Stacks.Divisors.IsEffectiveCartierDivisor (divisorIdeal A) := by
  classical
  have hM : divisorIdeal A = ∏ D ∈ hA.toFinset, D.idealSheaf ^ A D := by
    unfold divisorIdeal
    refine finprod_eq_prod_of_mulSupport_subset _ fun D hD => ?_
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro h0
    exact hD (by show D.idealSheaf ^ A D = 1; rw [h0, pow_zero])
  rw [hM]
  exact Stacks.Divisors.isEffectiveCartierDivisor_prod _ _ _
    fun D _ => Aux.isEffectiveCartierDivisor_idealSheaf sY hY D

/-- The pull-back of an effective Cartier divisor along a flat morphism to a scheme with
integral local rings is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_comap_of_flat {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
    [IsLocallyNoetherian Y] (hdom : ∀ y : Y, IsDomain (Y.presheaf.stalk y))
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    Stacks.Divisors.IsEffectiveCartierDivisor (I.comap h) := by
  refine AlgebraicGeometry.isEffectiveCartierDivisor_of_stalk_regular_principal _
    fun y _ => ?_
  obtain ⟨f, hf, hIf⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor I hI (h y)
  refine ⟨(h.stalkMap y).hom f, ?_, ?_⟩
  · haveI := hdom y
    have hne : (h.stalkMap y).hom f ≠ 0 := fun h0 =>
      hf.ne_zero (h.stalkMap_injective_of_flat y (h0.trans (map_zero _).symm))
    exact ⟨fun a b hab => mul_left_cancel₀ hne hab, fun a b hab => mul_right_cancel₀ hne hab⟩
  · rw [IdealSheafData.stalk_comap, hIf, Ideal.map_span, Set.image_singleton]

/-- An effective Cartier divisor has finite order along a prime divisor of a scheme with regular
local rings. -/
private theorem multAt_ne_top_of_isEffectiveCartierDivisor {Y : Scheme.{u}}
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (J : Y.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (D : AlgebraicGeometry.PrimeDivisor Y) :
    multAt J D.genericPoint ≠ ⊤ := by
  haveI := hreg D.genericPoint
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk D.genericPoint)
  haveI := isDiscreteValuationRing_of_ringKrullDim_eq_one D.ringKrullDim_stalk_genericPoint_eq_one
  obtain ⟨g, hg, hJg⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hJ
    D.genericPoint
  rw [multAt, hJg, idealOrder_span_eq_addVal hg.ne_zero, Ne,
    IsDiscreteValuationRing.addVal_eq_top_iff]
  exact hg.ne_zero

private theorem idealOrder_bot {R : Type*} [CommRing R] [IsLocalRing R] :
    idealOrder (⊥ : Ideal R) = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : (⊥ : Ideal R) ≤ maximalIdeal R ^ j) => (j : ℕ∞))
    n bot_le le_rfl

/-- In a discrete valuation ring the order is additive. -/
private theorem idealOrder_mul_of_isDiscreteValuationRing {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (I J : Ideal R) :
    idealOrder (I * J) = idealOrder I + idealOrder J := by
  obtain ⟨a, rfl⟩ := Submodule.IsPrincipal.principal I
  obtain ⟨b, rfl⟩ := Submodule.IsPrincipal.principal J
  change idealOrder (Ideal.span {a} * Ideal.span {b}) =
    idealOrder (Ideal.span {a}) + idealOrder (Ideal.span {b})
  rw [Ideal.span_singleton_mul_span_singleton]
  by_cases ha : a = 0
  · subst ha
    simp [Ideal.span_singleton_eq_bot.2 rfl, idealOrder_bot]
  by_cases hb : b = 0
  · subst hb
    simp [Ideal.span_singleton_eq_bot.2 rfl, idealOrder_bot]
  rw [idealOrder_span_eq_addVal (mul_ne_zero ha hb), idealOrder_span_eq_addVal ha,
    idealOrder_span_eq_addVal hb, IsDiscreteValuationRing.addVal_mul]

/-- The order along a prime divisor of `J · K^m` is `ord J + m · ord K`. -/
private theorem multAt_mul_pow {Y : Scheme.{u}}
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (J K : Y.IdealSheafData) (m : ℕ)
    (D : AlgebraicGeometry.PrimeDivisor Y) :
    multAt (J * K ^ m) D.genericPoint = multAt J D.genericPoint + m * multAt K D.genericPoint := by
  haveI := hreg D.genericPoint
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk D.genericPoint)
  haveI := isDiscreteValuationRing_of_ringKrullDim_eq_one D.ringKrullDim_stalk_genericPoint_eq_one
  rw [multAt, multAt, multAt, Aux.stalk_mul, Aux.stalk_pow,
    idealOrder_mul_of_isDiscreteValuationRing]
  congr 1
  induction m with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top, Nat.cast_zero, zero_mul]
    exact idealOrder_top
  | succ n ih =>
    rw [pow_succ, idealOrder_mul_of_isDiscreteValuationRing, ih]
    push_cast
    ring

end DivisorialIdeals

/-- `𝒪_Y(-D.A) = h^*𝒪_X(-A)` for related data. -/
private theorem divisorIdeal_eq_comap {X Y : Scheme.{u}} {h : Y ⟶ X} {C : MonomialData X}
    {D : MonomialData Y} (hR : Rel h C D) : divisorIdeal D.A = (divisorIdeal C.A).comap h := by
  obtain ⟨hsmD, hlftD, -, -, hfinD, -⟩ := id hR.monoD
  obtain ⟨hsmC, hlftC, -, -, hfinC, -⟩ := id hR.monoC
  haveI := hlftD
  haveI := hlftC
  haveI := Aux.smooth_of_isSmoothScheme' D.sX hsmD
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian D.sX
  have hreg : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y) := fun y =>
    isRegularLocalRing_stalk_of_smooth_over_field D.sX y
  haveI := hR.flatHom.flat
  have hJ₂ := isEffectiveCartierDivisor_comap_of_flat h
    (fun y => IsRegularLocalRing.isDomain (Y.presheaf.stalk y)) _
    (isEffectiveCartierDivisor_divisorIdeal C.sX hsmC C.A hfinC)
  refine eq_of_forall_multAt_genericPoint_eq hreg _ _
    (isEffectiveCartierDivisor_divisorIdeal D.sX hsmD D.A hfinD) hJ₂ fun D' => ?_
  have h1 : multAt (divisorIdeal D.A) D'.genericPoint = D.A D' :=
    multAt_monomialIdeal_genericPoint D hR.monoD D'
  rw [h1, hR.coeff]
  exact ENat.coe_toNat (multAt_ne_top_of_isEffectiveCartierDivisor hreg _ hJ₂ D')

/-! #### The coefficient of the component through a point -/

private theorem codimension_closureSingleton' {X : Scheme.{u}} (x : X) :
    codimension (IrreducibleCloseds.closureSingleton x) = Order.coheight x := by
  rw [codimension_eq_coheight]
  refine (Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)) _).symm.trans ?_
  congr 1
  have h1 :=
    (IrreducibleCloseds.closureSingleton x).isIrreducible.isGenericPoint_genericPoint_closure
  have h2 : IsGenericPoint x (closure ((IrreducibleCloseds.closureSingleton x : Set X))) := by
    change IsGenericPoint x (closure (closure {x}))
    rw [closure_closure]; exact isGenericPoint_closure
  exact h1.eq h2

/-- A point of a closed set of pure codimension one lies on an irreducible component of it
which is the support of a prime divisor. -/
private theorem exists_primeDivisor_mem_componentsOf {X : Scheme.{u}} [NoetherianSpace X]
    (S : Closeds X) (hS : MMP.Mori.IsPureCodimOne S) {x : X} (hx : x ∈ (S : Set X)) :
    ∃ P : AlgebraicGeometry.PrimeDivisor X,
      (P.support : Set X) ∈ componentsOf (S : Set X) ∧ x ∈ (P.support : Set X) := by
  obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
  obtain ⟨W, hW, hxW⟩ := hcov hx
  obtain ⟨ξ, -, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf S.isClosed hW
  have h1 : codimension (IrreducibleCloseds.closureSingleton ξ) = 1 :=
    hS _ ⟨hW.1.2, fun V hV hle => hW.2 ⟨V.isIrreducible, hV⟩ hle⟩
  rw [codimension_closureSingleton'] at h1
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ h1, ?_, ?_⟩ <;>
    rw [Aux.support_eq_closure_genericPoint,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  · exact hW
  · exact hxW

/-- When the `j`-th member is smooth, `a_j(x)` is the coefficient of the prime divisor through
`x` which is a component of `E^j`. -/
private theorem coeffAt_eq_of_mem {X : Scheme.{u}} (M : MonomialData X) {k : Type u} [Field k]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] (j : Fin M.E.s)
    (hsm : MMP.Mori.IsSmoothScheme ((M.E.E j).subschemeι ≫ s))
    (P : AlgebraicGeometry.PrimeDivisor X)
    (hP : (P.support : Set X) ∈ componentsOf ((M.E.E j).support : Set X)) {x : X}
    (hx : x ∈ (P.support : Set X)) : M.coeffAt j x = M.A P := by
  classical
  unfold MonomialData.coeffAt
  rw [finsum_eq_single _ P fun P' hP' => ?_]
  · simp [hP, hx]
  · rw [if_neg]
    rintro ⟨hP'c, hxP'⟩
    exact hP' (Aux.PrimeDivisor.eq_of_support_eq
      (Aux.eq_of_mem_componentsOf_of_isSmoothScheme s _ hsm hP'c hP hxP' hx))

private theorem coeffAt_eq_zero_of_notMem {X : Scheme.{u}} (M : MonomialData X) (j : Fin M.E.s)
    {x : X} (hx : x ∉ ((M.E.E j).support : Set X)) : M.coeffAt j x = 0 := by
  classical
  unfold MonomialData.coeffAt
  refine finsum_eq_zero_of_forall_eq_zero fun P => ?_
  rw [if_neg]
  rintro ⟨hPc, hxP⟩
  exact hx (hPc.1.2 hxP)

/-- The coefficient of `h^*A` along a component of `h⁻¹E^j` is the coefficient of `A` along the
component of `E^j` below it: the generic point maps to the generic point (`h` is flat), and
there `h^*𝔪 = 𝔪` (the inverse image of a prime divisor is reduced). -/
private theorem pullCoeff_eq_of_mem_componentsOf {X Y : Scheme.{u}} {h : Y ⟶ X}
    {C : MonomialData X} {D : MonomialData Y} (hR : Rel h C D) (j : Fin C.E.s)
    (Q : AlgebraicGeometry.PrimeDivisor Y)
    (hQ : (Q.support : Set Y) ∈ componentsOf ((((C.E.E j).comap h).support : Set Y)))
    (P : AlgebraicGeometry.PrimeDivisor X)
    (hP : (P.support : Set X) ∈ componentsOf ((C.E.E j).support : Set X)) {y : Y}
    (hyQ : y ∈ (Q.support : Set Y)) (hyP : h y ∈ (P.support : Set X)) :
    pullCoeff h C.A Q = C.A P := by
  obtain ⟨hsmC, hlftC, hqcC, hsncC, hfinC, -⟩ := id hR.monoC
  obtain ⟨hsmD, hlftD, -⟩ := id hR.monoD
  haveI := hlftC
  haveI := hqcC
  haveI := hlftD
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian D.sX
  haveI : NoetherianSpace X := Aux.noetherianSpace_of_finiteType C.sX
  haveI := Aux.smooth_of_isSmoothScheme' D.sX hsmD
  haveI := hR.flatHom.flat
  -- the generic point of `Q` maps to the generic point of `P`
  have hξE : h Q.genericPoint ∈ ((C.E.E j).support : Set X) := by
    have : Q.genericPoint ∈ (((C.E.E j).comap h).support : Set Y) := hQ.1.2 (by
      rw [Aux.support_eq_closure_genericPoint]; exact subset_closure rfl)
    rw [Scheme.IdealSheafData.support_comap] at this
    exact this
  have hspec : h Q.genericPoint ⤳ h y := by
    have : Q.genericPoint ⤳ y := by
      rwa [specializes_iff_mem_closure, ← Aux.support_eq_closure_genericPoint]
    exact this.map h.continuous
  have hξP : h Q.genericPoint ∈ (P.support : Set X) := by
    obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf (C.E.E j).support.isClosed
    obtain ⟨W', hW', hξW'⟩ := hcov hξE
    have hyW' : h y ∈ W' :=
      (Aux.isClosed_of_mem_componentsOf (C.E.E j).support.isClosed hW').closure_subset_iff.2
        (Set.singleton_subset_iff.2 hξW') (specializes_iff_mem_closure.1 hspec)
    have := Aux.eq_of_mem_componentsOf_of_isSmoothScheme C.sX _ (hsncC.2.1 j).2.2 hW' hP hyW' hyP
    exact this ▸ hξW'
  have hcohξ : Order.coheight (h Q.genericPoint) ≤ 1 := by
    have := ringKrullDim_stalk_le_of_flat h Q.genericPoint
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      Q.coheight_genericPoint] at this
    exact_mod_cast this
  have hξeq : h Q.genericPoint = P.genericPoint := by
    by_contra hne
    have hsp : P.genericPoint ⤳ h Q.genericPoint := by
      rwa [specializes_iff_mem_closure, ← Aux.support_eq_closure_genericPoint]
    have hle : h Q.genericPoint ≤ P.genericPoint := hsp
    have hlt : h Q.genericPoint < P.genericPoint :=
      lt_of_le_not_ge hle fun hge => hne (Specializes.antisymm (show h Q.genericPoint ⤳
        P.genericPoint from hge) hsp).eq
    have e := Order.coheight_add_one_le hlt
    rw [P.coheight_genericPoint] at e
    have := e.trans hcohξ
    exact absurd this (by decide)
  -- stalks at the generic points
  have hdom : IsDomain (Y.presheaf.stalk Q.genericPoint) :=
    (isRegularLocalRing_stalk_of_smooth_over_field D.sX Q.genericPoint).isDomain
  have key : ∀ x : X, x = P.genericPoint →
      ∀ (φ : X.presheaf.stalk x ⟶ Y.presheaf.stalk Q.genericPoint),
      IsLocalHom φ.hom → Function.Injective φ.hom →
      IdealSheafData.stalk ((divisorIdeal C.A).comap h) Q.genericPoint =
        (IdealSheafData.stalk (divisorIdeal C.A) x).map φ.hom →
      IdealSheafData.stalk (P.idealSheaf.comap h) Q.genericPoint =
        (IdealSheafData.stalk P.idealSheaf x).map φ.hom →
      multAt ((divisorIdeal C.A).comap h) Q.genericPoint = C.A P := by
    rintro x rfl φ hloc hinj hA hP'
    have hm := Aux.stalk_idealSheaf_genericPoint P
    have hA' : IdealSheafData.stalk (divisorIdeal C.A) P.genericPoint =
        IsLocalRing.maximalIdeal _ ^ C.A P := stalk_monomialIdeal_genericPoint C hfinC P
    -- the pulled-back ideal of `P` is the maximal ideal at the generic point of `Q`
    haveI : IsReduced P.idealSheaf.subscheme := by haveI := P.integral; infer_instance
    have hPv : P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal P.idealSheaf.support :=
      Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
    have hcl : IsClosed (h ⁻¹' (P.support : Set X)) :=
      P.idealSheaf.support.isClosed.preimage h.continuous
    have hPc : P.idealSheaf.comap h = Scheme.IdealSheafData.vanishingIdeal ⟨_, hcl⟩ := by
      conv_lhs => rw [hPv]
      exact hR.flatHom.comap_vanishingIdeal _ _ rfl
    have hrad : (IdealSheafData.stalk (P.idealSheaf.comap h) Q.genericPoint).IsRadical := by
      rw [hPc]; exact isRadical_stalk_vanishingIdeal _ _
    have htop : IdealSheafData.stalk (P.idealSheaf.comap h) Q.genericPoint ≠ ⊤ := by
      rw [Ne, IdealSheafData.stalk_eq_top_iff_notMem_support, Scheme.IdealSheafData.support_comap,
        not_not]
      show h Q.genericPoint ∈ (P.support : Set X)
      exact hξP
    have hbot : IdealSheafData.stalk (P.idealSheaf.comap h) Q.genericPoint ≠ ⊥ := by
      rw [hP', hm]
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (maximalIdeal_stalk_genericPoint_ne_bot P)
      intro h0
      have : φ.hom a ∈ (IsLocalRing.maximalIdeal _).map φ.hom := Ideal.mem_map_of_mem _ ha
      rw [h0, Ideal.mem_bot] at this
      exact ha0 (hinj (this.trans (map_zero _).symm))
    have hKm : IdealSheafData.stalk (P.idealSheaf.comap h) Q.genericPoint =
        IsLocalRing.maximalIdeal _ := by
      rw [← hrad.radical, Ideal.radical_eq_sInf]
      refine le_antisymm (sInf_le ⟨IsLocalRing.le_maximalIdeal htop, inferInstance⟩)
        (le_sInf fun p ⟨hKp, hp⟩ => ?_)
      have hp0 : p ≠ ⊥ := fun h0 => hbot (le_bot_iff.1 (h0 ▸ hKp))
      exact (eq_maximalIdeal_of_ringKrullDim_le_one Q.ringKrullDim_stalk_genericPoint_eq_one.le
        hp0).ge
    have hmap : (IsLocalRing.maximalIdeal (X.presheaf.stalk P.genericPoint)).map φ.hom =
        IsLocalRing.maximalIdeal _ := by
      rw [← hm, ← hP', hKm]
    rw [multAt, hA, hA', Ideal.map_pow, hmap,
      idealOrder_maximalIdeal_pow (maximalIdeal_stalk_genericPoint_ne_bot Q)]
  -- the stalk map
  have hmult := key _ hξeq (h.stalkMap Q.genericPoint) (h.prop Q.genericPoint)
    (h.stalkMap_injective_of_flat Q.genericPoint) (IdealSheafData.stalk_comap _ _ _)
    (IdealSheafData.stalk_comap _ _ _)
  show (multAt ((divisorIdeal C.A).comap h) Q.genericPoint).toNat = C.A P
  rw [hmult, ENat.toNat_coe]

/-- The coefficient of the component of `h⁻¹E^j` through `y` is the coefficient of the component
of `E^j` through `h(y)`. -/
private theorem coeffAt_comap {X Y : Scheme.{u}} {h : Y ⟶ X} {C : MonomialData X}
    {D : MonomialData Y} (hR : Rel h C D) (j : Fin C.E.s) (y : Y) :
    (withEm D (C.E.comap h)).coeffAt j y = C.coeffAt j (h y) := by
  classical
  have hyiff : y ∈ (((C.E.E j).comap h).support : Set Y) ↔ h y ∈ ((C.E.E j).support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  by_cases hy : h y ∈ ((C.E.E j).support : Set X)
  · obtain ⟨hsmC, hlftC, hqcC, hsncC, -⟩ := id hR.monoC
    obtain ⟨hsmD, hlftD, hqcD, hsncD, -⟩ := id hR.monoD
    haveI := hlftC
    haveI := hqcC
    haveI := hlftD
    haveI := hqcD
    haveI : NoetherianSpace X := Aux.noetherianSpace_of_finiteType C.sX
    haveI : NoetherianSpace Y := Aux.noetherianSpace_of_finiteType D.sX
    have hy' := hyiff.2 hy
    have hne : (C.E.E j).comap h ≠ ⊤ := by
      intro htop
      rw [htop, Scheme.IdealSheafData.support_top] at hy'
      exact hy'
    obtain ⟨i, hi⟩ : ∃ i, D.E.E i = (C.E.E j).comap h := by
      have hmem : (C.E.E j).comap h ∈ flat (C.E.comap h) := by
        simp only [flat, List.mem_filter, List.mem_ofFn, decide_eq_true_eq]
        exact ⟨⟨j, rfl⟩, hne⟩
      rw [← hR.flatE] at hmem
      simp only [flat, List.mem_filter, List.mem_ofFn] at hmem
      obtain ⟨⟨i, hi⟩, -⟩ := hmem
      exact ⟨i, hi⟩
    have hsmY : MMP.Mori.IsSmoothScheme (((C.E.E j).comap h).subschemeι ≫ D.sX) :=
      hi ▸ (hsncD.2.1 i).2.2
    have hpureY : MMP.Mori.IsPureCodimOne ((C.E.E j).comap h).support :=
      hi ▸ (hsncD.2.1 i).2.1
    obtain ⟨P, hP, hyP⟩ := exists_primeDivisor_mem_componentsOf _ (hsncC.2.1 j).2.1 hy
    obtain ⟨Q, hQ, hyQ⟩ := exists_primeDivisor_mem_componentsOf _ hpureY hy'
    rw [coeffAt_eq_of_mem (withEm D (C.E.comap h)) D.sX j hsmY Q hQ hyQ,
      coeffAt_eq_of_mem C C.sX j (hsncC.2.1 j).2.2 P hP hyP]
    show D.A Q = C.A P
    rw [hR.coeff]
    exact pullCoeff_eq_of_mem_componentsOf hR j Q hQ P hP hyQ hyP
  · rw [coeffAt_eq_zero_of_notMem C j hy]
    exact coeffAt_eq_zero_of_notMem (withEm D (C.E.comap h)) j fun h' => hy (hyiff.1 h')

/-- The new coefficients of a Step-3.`r` blow-up are pulled back along the canonical lift. -/
private theorem stepAt_A_eq_pullCoeff {X Y : Scheme.{u}} {h : Y ⟶ X} {C : MonomialData X}
    {D : MonomialData Y} (hR : Rel h C D) {m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight r) (hc : D.stepCenter r = (C.stepCenter r).comap h)
    (hw : D.maxStratumWeight r = C.maxStratumWeight r) :
    (stepAt D m ((C.stepCenter r).comap h)).A =
      pullCoeff (canonicalLift h (C.stepCenter r)) (C.step m r).A := by
  set Z := C.stepCenter r with hZ
  set W := Z.comap h with hW
  set h' := canonicalLift h Z with hh'
  obtain ⟨⟨hcodim, hsnc, hord⟩, -, hbt, -⟩ := step_spec C hR.monoC hR.charC hr hm hmr
  obtain ⟨hsmC, hlftC, -⟩ := hR.monoC
  haveI := hlftC
  haveI := hR.charC
  have hZsm := isSmoothScheme_subschemeι_of_hasSNCWith C.sX hsmC Z hsnc
  have hmul := MarkedIdeal.birationalTransform_mul_eq C.sX hsmC Z hZsm hcodim
    ⟨C.monomialIdeal, m⟩ hord
  rw [hbt] at hmul
  change divisorIdeal (C.step m r).A * Z.comap (blowUpToBase Z) ^ m =
    (divisorIdeal C.A).comap (blowUpToBase Z) at hmul
  have hcomm : h' ≫ blowUpToBase Z = blowUpToBase W ≫ h := canonicalLift_comp_blowUpToBase h Z
  have key : (divisorIdeal (C.step m r).A).comap h' * (W.comap (blowUpToBase W)) ^ m =
      (divisorIdeal D.A).comap (blowUpToBase W) := by
    have := congrArg (fun I => I.comap h') hmul
    rw [Stacks.IdealSheaf.comap_mul, Stacks.IdealSheaf.comap_pow,
      ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, hcomm, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_comp, ← divisorIdeal_eq_comap hR] at this
    exact this
  -- the data on `B_W Y` are monomial data, so `B_W Y` has regular local rings
  have hD := (step_spec D hR.monoD hR.charD hr hm (hw ▸ hmr)).2.2.2.1
  rw [step_eq_stepAt, hc] at hD
  obtain ⟨hsmY, hlftY, -⟩ := hD
  haveI := hlftY
  haveI := Aux.smooth_of_isSmoothScheme' _ hsmY
  have hreg : ∀ y, IsRegularLocalRing ((blowUp W).presheaf.stalk y) := fun y =>
    isRegularLocalRing_stalk_of_smooth_over_field (stepAt D m W).sX y
  funext D''
  show (multAt ((divisorIdeal D.A).comap (blowUpToBase W)) D''.genericPoint).toNat -
      m * (multAt (W.comap (blowUpToBase W)) D''.genericPoint).toNat =
    (multAt ((divisorIdeal (C.step m r).A).comap h') D''.genericPoint).toNat
  rw [← key]
  have hK : multAt (W.comap (blowUpToBase W)) D''.genericPoint ≠ ⊤ :=
    multAt_ne_top_of_isEffectiveCartierDivisor hreg _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal W) D''
  rw [multAt_mul_pow hreg]
  generalize multAt ((divisorIdeal (C.step m r).A).comap h') D''.genericPoint = a
  generalize hb : multAt (W.comap (blowUpToBase W)) D''.genericPoint = b at hK
  induction a using ENat.recTopCoe with
  | top => simp
  | coe a =>
    lift b to ℕ using hK
    rw [show ((a : ℕ∞) + (m : ℕ∞) * (b : ℕ∞)) = ((a + m * b : ℕ) : ℕ∞) by push_cast; ring,
      ENat.toNat_coe, ENat.toNat_coe, ENat.toNat_coe]
    omega

/-- If the Step-3.`r` centre pulls back to the empty set, the new coefficients pull back to the
old ones along the lift `Y → B_ZX`. -/
private theorem pullCoeff_step_of_comap_eq_top {X Y : Scheme.{u}} {h : Y ⟶ X}
    {C : MonomialData X} {D : MonomialData Y} (hR : Rel h C D) {m r : ℕ} (hr : 1 ≤ r)
    (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r) (hZ : (C.stepCenter r).comap h = ⊤) :
    pullCoeff h C.A = pullCoeff (blowUpLift (C.stepCenter r) h
      (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h _ hZ)) (C.step m r).A := by
  set L := blowUpLift (C.stepCenter r) h
    (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h _ hZ) with hL
  obtain ⟨⟨hcodim, hsnc, hord⟩, -, hbt, -⟩ := step_spec C hR.monoC hR.charC hr hm hmr
  obtain ⟨hsm, hlft, -⟩ := hR.monoC
  haveI := hlft
  haveI := hR.charC
  have hZsm := isSmoothScheme_subschemeι_of_hasSNCWith C.sX hsm (C.stepCenter r) hsnc
  have hmul := MarkedIdeal.birationalTransform_mul_eq C.sX hsm (C.stepCenter r) hZsm hcodim
    ⟨C.monomialIdeal, m⟩ hord
  rw [hbt] at hmul
  have hLπ : L ≫ blowUpToBase (C.stepCenter r) = h := blowUpLift_comp _ _ _
  have e1 : ((C.stepCenter r).comap (blowUpToBase (C.stepCenter r))).comap L = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, hLπ, hZ]
  have key := congrArg (fun I => I.comap L) hmul
  simp only at key
  rw [Stacks.IdealSheaf.comap_mul, Stacks.IdealSheaf.comap_pow, e1,
    ← Scheme.IdealSheafData.one_eq_top, one_pow, mul_one, ← Scheme.IdealSheafData.comap_comp,
    hLπ] at key
  change (divisorIdeal (C.step m r).A).comap L = (divisorIdeal C.A).comap h at key
  funext D'
  show (multAt ((divisorIdeal C.A).comap h) D'.genericPoint).toNat =
    (multAt ((divisorIdeal (C.step m r).A).comap L) D'.genericPoint).toNat
  rw [key]

/-- If the Step-3.`r` centre pulls back to the empty set, the total transform pulls back to
`h⁻¹E` followed by an empty entry. -/
private theorem flat_comap_totalTransform_of_comap_eq_top {X Y : Scheme.{u}} {h : Y ⟶ X}
    {C : MonomialData X} {D : MonomialData Y} (hR : Rel h C D) {r : ℕ}
    (hZ : (C.stepCenter r).comap h = ⊤) :
    flat ((C.E.totalTransform (C.stepCenter r)).comap (blowUpLift (C.stepCenter r) h
      (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h _ hZ))) = flat (C.E.comap h) := by
  classical
  set Z := C.stepCenter r with hZdef
  set L := blowUpLift Z h (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h _ hZ) with hLdef
  have hL : IsReducedFlatBaseChange L := isReducedFlatBaseChange_blowUpLift hR.flatHom Z hZ
  have hopen : IsOpenMap L := by
    haveI := hL.universallyOpen
    exact L.isOpenMap
  have hLπ : ∀ S : Set X, ⇑L ⁻¹' (⇑(blowUpToBase Z) ⁻¹' S) = ⇑h ⁻¹' S := by
    intro S
    rw [← Set.preimage_comp]
    congr 1
    funext y
    have := congrArg (fun f : Y ⟶ X => f y) (blowUpLift_comp Z h
      (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h _ hZ))
    simpa using this
  have hZe : ⇑h ⁻¹' (Z.support : Set X) = ∅ := by
    have := congrArg (fun I : Y.IdealSheafData => (I.support : Set Y)) hZ
    simp only [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_top] at this
    exact this
  have hsub : ∀ W ∈ componentsOf (Z.support : Set X), ⇑h ⁻¹' W = ∅ := fun W hW =>
    Set.eq_empty_of_subset_empty ((Set.preimage_mono hW.1.2).trans hZe.le)
  have hentry : ∀ i, (entryTransform Z (C.E.E i)).comap L = (C.E.E i).comap h := by
    intro i
    haveI : IsReduced (C.E.E i).subscheme := (hR.monoC.2.2.2.1.1 i).1
    have hEi : C.E.E i = Scheme.IdealSheafData.vanishingIdeal (C.E.E i).support :=
      Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
    have hcl : IsClosed (⇑h ⁻¹' ((C.E.E i).support : Set X)) :=
      (C.E.E i).support.isClosed.preimage h.continuous
    have h1 : (C.E.E i).comap h = Scheme.IdealSheafData.vanishingIdeal ⟨_, hcl⟩ := by
      conv_lhs => rw [hEi]
      exact hR.flatHom.comap_vanishingIdeal _ _ rfl
    rw [h1]
    refine hL.comap_vanishingIdeal _ _ ?_
    rw [Closeds.coe_closure, hopen.preimage_closure_eq_closure_preimage L.continuous, hLπ,
      Set.preimage_diff]
    have hZ2 : ⇑h ⁻¹' componentsOfCodimAtLeastTwo (Z.support : Set X) = ∅ := by
      refine Set.eq_empty_of_subset_empty ?_
      intro y hy
      simp only [componentsOfCodimAtLeastTwo, Set.preimage_iUnion, Set.mem_iUnion] at hy
      obtain ⟨W, hW, -, hyW⟩ := hy
      rw [hsub W hW] at hyW
      exact hyW
    rw [hZ2, Set.diff_empty, hcl.closure_eq]
    rfl
  have hlast : (lastEntry Z C.E.support).comap L = ⊤ := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_bot (X := Y)]
    refine hL.comap_vanishingIdeal _ _ ?_
    rw [Closeds.coe_closure, hopen.preimage_closure_eq_closure_preimage L.continuous]
    simp only [Set.preimage_iUnion, hLπ]
    have : (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
        (_ : W ∉ componentsOf C.E.support), ⇑h ⁻¹' W) = ∅ := by
      refine Set.eq_empty_of_subset_empty ?_
      intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨W, hW, -, hyW⟩ := hy
      rw [hsub W hW] at hyW
      exact hyW
    rw [this, closure_empty]
    rfl
  have hlist : List.ofFn ((C.E.totalTransform Z).comap L).E =
      List.ofFn (C.E.comap h).E ++ [⊤] := by
    show List.ofFn (n := C.E.s + 1) (fun i => ((C.E.totalTransform Z).E i).comap L) = _
    rw [List.ofFn_succ', List.concat_eq_append]
    congr 1
    · congr 1
      funext i
      show ((C.E.totalTransform Z).E i.castSucc).comap L = (C.E.E i).comap h
      simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc]
      exact hentry i
    · show [((C.E.totalTransform Z).E (Fin.last _)).comap L] = [⊤]
      simp only [OrderedDivisor.totalTransform, Fin.snoc_last]
      exact congrArg (fun I => [I]) hlast
  unfold flat
  rw [hlist, List.filter_append]
  simp

end Pullback

/-! ### Weights and centres of pulled-back data -/

section Centre

private theorem coeffAt_le_finsum {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) (j : Fin C.E.s) (x : X) :
    C.coeffAt j x ≤ ∑ᶠ D, C.A D := by
  classical
  unfold MonomialData.coeffAt
  refine finsum_le_finsum' (hfin.subset fun D hD => ?_) hfin fun D => ?_
  · by_contra h
    exact hD (by simp [Function.notMem_support.1 h])
  · dsimp only
    split_ifs <;> simp

private theorem bddAbove_range_of_le {ι : Sort*} {f : ι → ℕ} {B : ℕ} (h : ∀ i, f i ≤ B) :
    BddAbove (Set.range f) :=
  ⟨B, Set.forall_mem_range.2 h⟩

private theorem stratumWeight_le_maxStratumWeight {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) {r : ℕ} {J : Finset (Fin C.E.s)} (hJ : J.card = r)
    {x : X} (hx : x ∈ C.stratum J) : C.stratumWeight J x ≤ C.maxStratumWeight r := by
  have hB : ∀ J' : Finset (Fin C.E.s), J'.card = r → ∀ x',
      C.stratumWeight J' x' ≤ r * ∑ᶠ D, C.A D := fun J' hJ' x' => by
    unfold MonomialData.stratumWeight
    rw [← hJ', ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun j _ => coeffAt_le_finsum C hfin j x'
  unfold MonomialData.maxStratumWeight
  exact le_ciSup_of_le (bddAbove_range_of_le fun J' => ciSup_le' fun hJ' => ciSup_le' fun x' =>
      ciSup_le' fun _ => hB J' hJ' x') J <|
    le_ciSup_of_le (bddAbove_range_of_le fun hJ' => ciSup_le' fun x' => ciSup_le' fun _ =>
      hB J hJ' x') hJ <|
    le_ciSup_of_le (bddAbove_range_of_le fun x' => ciSup_le' fun _ => hB J hJ x') x <|
    le_ciSup_of_le (bddAbove_range_of_le fun _ => hB J hJ x) hx le_rfl

/-- The union of the pieces of `E^J` of maximal weight. -/
private theorem sUnion_isMaxPiece {X : Scheme.{u}} (M : MonomialData X) {r : ℕ}
    {J : Finset (Fin M.E.s)} (hJ : J.card = r)
    (hconst : ∀ x ∈ M.stratum J, ∀ y ∈ connectedComponentIn (M.stratum J) x,
      M.stratumWeight J y = M.stratumWeight J x) :
    ⋃₀ {P | M.IsMaxPiece r J P} =
      {x | x ∈ M.stratum J ∧ M.stratumWeight J x = M.maxStratumWeight r} := by
  ext x
  simp only [Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨P, ⟨-, ⟨x₀, hx₀, rfl⟩, hw⟩, hx⟩
    exact ⟨connectedComponentIn_subset _ _ hx, hw x hx⟩
  · rintro ⟨hx, hw⟩
    exact ⟨connectedComponentIn (M.stratum J) x,
      ⟨hJ, ⟨x, hx, rfl⟩, fun y hy => (hconst x hx y hy).trans hw⟩, mem_connectedComponentIn hx⟩

variable {X Y : Scheme.{u}} {h : Y ⟶ X} {C : MonomialData X} {D : MonomialData Y}

private theorem stratum_withEm_comap (h : Y ⟶ X) (C : MonomialData X) (D : MonomialData Y)
    (J : Finset (Fin C.E.s)) : (withEm D (C.E.comap h)).stratum J = h ⁻¹' C.stratum J := by
  ext y
  simp only [MonomialData.stratum, Set.mem_iInter, Set.mem_preimage]
  refine forall_congr' fun j => forall_congr' fun _ => ?_
  show y ∈ (((C.E.E j).comap h).support : Set Y) ↔ _
  rw [Scheme.IdealSheafData.support_comap]
  rfl

private theorem stratumWeight_withEm_comap (hR : Rel h C D) (J : Finset (Fin C.E.s)) (y : Y) :
    (withEm D (C.E.comap h)).stratumWeight J y = C.stratumWeight J (h y) :=
  Finset.sum_congr rfl fun j _ => coeffAt_comap hR j y

private theorem maxStratumWeight_withEm_le (hR : Rel h C D) (r : ℕ) :
    (withEm D (C.E.comap h)).maxStratumWeight r ≤ C.maxStratumWeight r := by
  refine ciSup_le' fun J => ciSup_le' fun hJ => ciSup_le' fun y => ciSup_le' fun hy => ?_
  have hy' : h y ∈ C.stratum J := (Set.ext_iff.1 (stratum_withEm_comap h C D J) y).1 hy
  exact (stratumWeight_withEm_comap hR J y).trans_le
    (stratumWeight_le_maxStratumWeight C hR.monoC.2.2.2.2.1 hJ hy')

/-- `m_r` of the data on `Y` is at most `m_r` of the data on `X`. -/
private theorem maxStratumWeight_le (hR : Rel h C D) (r : ℕ) :
    D.maxStratumWeight r ≤ C.maxStratumWeight r := by
  rw [← maxStratumWeight_congr D (C.E.comap h) hR.flatE.symm r]
  exact maxStratumWeight_withEm_le hR r

private theorem stratumWeight_const_withEm (hR : Rel h C D) (J : Finset (Fin C.E.s)) :
    ∀ x ∈ (withEm D (C.E.comap h)).stratum J,
      ∀ y ∈ connectedComponentIn ((withEm D (C.E.comap h)).stratum J) x,
        (withEm D (C.E.comap h)).stratumWeight J y =
          (withEm D (C.E.comap h)).stratumWeight J x := by
  intro y hy z hz
  rw [stratumWeight_withEm_comap hR, stratumWeight_withEm_comap hR]
  have hy' : h y ∈ C.stratum J := by rwa [stratum_withEm_comap] at hy
  have hpre : _root_.IsPreconnected
      (h '' connectedComponentIn ((withEm D (C.E.comap h)).stratum J) y) :=
    isPreconnected_connectedComponentIn.image _ h.continuous.continuousOn
  have hsub := hpre.subset_connectedComponentIn ⟨y, mem_connectedComponentIn hy, rfl⟩ (by
    rintro _ ⟨w, hw, rfl⟩
    have := connectedComponentIn_subset _ _ hw
    rw [stratum_withEm_comap] at this
    exact this)
  exact C.stratumWeight_eq_of_mem_connectedComponentIn hR.monoC J hy' (hsub ⟨z, hz, rfl⟩)

/-- If the Step-3.`r` centre of `C` pulls back to a nonempty subscheme, it is the Step-3.`r`
centre of `D`, and the weights `m_r` agree. -/
private theorem stepCenter_comap (hR : Rel h C D) {r : ℕ}
    (hne : (C.stepCenter r).comap h ≠ ⊤) :
    D.maxStratumWeight r = C.maxStratumWeight r ∧ D.stepCenter r = (C.stepCenter r).comap h := by
  classical
  have hfl := hR.flatE.symm
  rw [← maxStratumWeight_congr D (C.E.comap h) hfl r, ← stepCenter_congr D (C.E.comap h) hfl r]
  set D₁ := withEm D (C.E.comap h) with hD₁
  have hopen : IsOpenMap h := by
    haveI := hR.flatHom.universallyOpen
    exact h.isOpenMap
  set SC := ⋃₀ {P | C.IsMaxPiece r (C.stepIndex r) P} with hSC
  have hcomap : (C.stepCenter r).comap h =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (h ⁻¹' SC)) :=
    hR.flatHom.comap_vanishingIdeal _ _ (by
      rw [Closeds.coe_closure, Closeds.coe_closure,
        hopen.preimage_closure_eq_closure_preimage h.continuous])
  have hne' : (h ⁻¹' SC).Nonempty := by
    by_contra hem
    rw [Set.not_nonempty_iff_eq_empty] at hem
    apply hne
    rw [hcomap, ← Scheme.IdealSheafData.vanishingIdeal_bot]
    congr 1
    ext y
    simp [hem]
  obtain ⟨y, P, hP, hyP⟩ := hne'
  set J₀ := C.stepIndex r with hJ₀
  have hP' : C.IsMaxPiece r J₀ P := hP
  have hcard : J₀.card = r := hP'.1
  have hyS : h y ∈ C.stratum J₀ := by
    obtain ⟨x₀, -, hPeq⟩ := hP'.2.1
    rw [hPeq] at hyP
    exact connectedComponentIn_subset _ _ hyP
  have hyw : C.stratumWeight J₀ (h y) = C.maxStratumWeight r := hP'.2.2 _ hyP
  have hyD : y ∈ D₁.stratum J₀ := by rwa [stratum_withEm_comap]
  have hfinD : (Function.support D₁.A).Finite := hR.monoD.2.2.2.2.1
  have hmr : D₁.maxStratumWeight r = C.maxStratumWeight r := by
    refine le_antisymm (maxStratumWeight_withEm_le hR r) ?_
    have := stratumWeight_le_maxStratumWeight D₁ hfinD hcard hyD
    rwa [stratumWeight_withEm_comap hR, hyw] at this
  refine ⟨hmr, ?_⟩
  -- the max pieces of `D₁` and of `C`
  have hU : ∀ J : Finset (Fin C.E.s), J.card = r →
      ⋃₀ {P | D₁.IsMaxPiece r J P} = h ⁻¹' ⋃₀ {P | C.IsMaxPiece r J P} := by
    intro J hJ
    rw [sUnion_isMaxPiece D₁ hJ (stratumWeight_const_withEm hR J),
      sUnion_isMaxPiece C hJ (fun x hx y hy =>
        C.stratumWeight_eq_of_mem_connectedComponentIn hR.monoC J hx hy)]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [stratum_withEm_comap, stratumWeight_withEm_comap hR, hmr]
    rfl
  have hDC : ∀ J P, D₁.IsMaxPiece r J P → ∃ Q, C.IsMaxPiece r J Q := by
    intro J P hJP
    obtain ⟨y₁, hy₁, hPeq⟩ := hJP.2.1
    have hmem : y₁ ∈ ⋃₀ {P | D₁.IsMaxPiece r J P} :=
      ⟨P, hJP, hPeq ▸ mem_connectedComponentIn hy₁⟩
    rw [hU J hJP.1] at hmem
    obtain ⟨Q, hQ, -⟩ := hmem
    exact ⟨Q, hQ⟩
  have hD0 : ∃ P', D₁.IsMaxPiece r J₀ P' := by
    have hmem : y ∈ h ⁻¹' ⋃₀ {P | C.IsMaxPiece r J₀ P} := ⟨P, hP', hyP⟩
    rw [← hU J₀ hcard] at hmem
    obtain ⟨P', hP'', -⟩ := hmem
    exact ⟨P', hP''⟩
  have hidx : D₁.stepIndex r = J₀ := by
    obtain ⟨P₀, hP₀⟩ := hD0
    obtain ⟨⟨P₁, hP₁⟩, h₁⟩ := stepIndex_spec D₁ r ⟨J₀, P₀, hP₀⟩
    obtain ⟨-, h₀⟩ := stepIndex_spec C r ⟨J₀, P, hP'⟩
    obtain ⟨Q₁, hQ₁⟩ := hDC _ _ hP₁
    exact eq_of_sort_eq (le_antisymm (h₁ J₀ P₀ hP₀) (h₀ _ Q₁ hQ₁))
  rw [hcomap]
  show Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (⋃₀ {P | D₁.IsMaxPiece r (D₁.stepIndex r) P})) = _
  rw [hidx, hU J₀ hcard]

end Centre

/-! ### The Step-3.`r` blow-ups and their pull-backs -/

section Step

variable {X Y : Scheme.{u}} {h : Y ⟶ X} {C : MonomialData X} {D : MonomialData Y}

private theorem lower_step {X : Scheme.{u}} {C : MonomialData X} (hC : C.IsMonomialData)
    (hk : CharZero C.k) {m r : ℕ} (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r)
    (hl : ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m) :
    ∀ t, 1 ≤ t → t < r → (C.step m r).maxStratumWeight t < m := by
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · intro t ht1 htr; omega
  · exact maxStratumWeight_step_lt C hC hk hr2 hm hl hmr

private theorem exists_iterate_lt {X : Scheme.{u}} (C : MonomialData X) (hC : C.IsMonomialData)
    (hk : CharZero C.k) {m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hl : ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m) :
    ∃ N, (C.iterate m r N).2.maxStratumWeight r < m := by
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · obtain rfl : r = 1 := by omega
    exact exists_maxStratumWeight_iterate_one_lt C hC hk hm
  · obtain ⟨N, hN⟩ := exists_maxStratumWeight_iterate_lt C hC hk hr2 hm hl
    exact ⟨N, hN r hr le_rfl⟩

/-- A Step-3.`r` blow-up whose centre pulls back to a nonempty subscheme: the blow-ups
correspond along the canonical lift. -/
private theorem rel_step (hR : Rel h C D) {m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight r) (hne : (C.stepCenter r).comap h ≠ ⊤) :
    Rel (canonicalLift h (C.stepCenter r)) (C.step m r)
      (stepAt D m ((C.stepCenter r).comap h)) := by
  obtain ⟨hw, hc⟩ := stepCenter_comap hR hne
  have hD := (step_spec D hR.monoD hR.charD hr hm (hw ▸ hmr)).2.2.2.1
  rw [step_eq_stepAt, hc] at hD
  refine ⟨(step_spec C hR.monoC hR.charC hr hm hmr).2.2.2.1, hR.charC, hD, hR.charD,
    hR.flatHom.canonicalLift _, ?_, stepAt_A_eq_pullCoeff hR hr hm hmr hc hw⟩
  exact (flat_totalTransform_eq hR.flatE _).trans (totalTransform_comap_canonicalLift hR hr hc)

/-- A Step-3.`r` blow-up whose centre pulls back to the empty set: the data on `Y` stay. -/
private theorem rel_skip (hR : Rel h C D) {m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight r) (hZ : (C.stepCenter r).comap h = ⊤) :
    Rel (blowUpLift (C.stepCenter r) h
      (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h _ hZ)) (C.step m r) D :=
  ⟨(step_spec C hR.monoC hR.charC hr hm hmr).2.2.2.1, hR.charC, hR.monoD, hR.charD,
    isReducedFlatBaseChange_blowUpLift hR.flatHom _ hZ,
    hR.flatE.trans (flat_comap_totalTransform_of_comap_eq_top hR hZ).symm,
    hR.coeff.trans (pullCoeff_step_of_comap_eq_top hR hr hm hmr hZ)⟩

/-- One Step-3.`r` phase: the phase on `Y` is the pull-back of the phase on `X` with its empty
blow-ups deleted, and ends at the corresponding data. -/
private theorem phase (m r : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (KC KD : ∀ {Y : Scheme.{u}}, MonomialData Y → ClosedBlowupSequence Y)
    (hK : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) (C : MonomialData X) (D : MonomialData Y),
      Rel h C D → (∀ t, 1 ≤ t → t ≤ r → C.maxStratumWeight t < m) →
        KD D = (KC C).pullbackReduced h) :
    ∀ (q : ℕ) {X Y : Scheme.{u}} (h : Y ⟶ X) (C : MonomialData X) (D : MonomialData Y),
      Rel h C D → (∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m) →
      (C.iterate m r q).2.maxStratumWeight r < m →
      (∀ q' < q, m ≤ (C.iterate m r q').2.maxStratumWeight r) →
      ∃ qD, (D.iterate m r qD).2.maxStratumWeight r < m ∧
        (∀ q' < qD, m ≤ (D.iterate m r q').2.maxStratumWeight r) ∧
        stepPhase m r KD qD D = (stepPhase m r KC q C).pullbackReduced h
  | 0, X, Y, h, C, D, hR, hlow, hq, _ => by
    refine ⟨0, lt_of_le_of_lt (maxStratumWeight_le hR r) hq,
      fun q' hq' => absurd hq' (Nat.not_lt_zero _), ?_⟩
    exact hK h C D hR fun t ht1 htr =>
      (lt_or_eq_of_le htr).elim (hlow t ht1) (fun e => e ▸ hq)
  | q + 1, X, Y, h, C, D, hR, hlow, hq, hmin => by
    have hmr : m ≤ C.maxStratumWeight r := hmin 0 (Nat.succ_pos _)
    have hlow' := lower_step hR.monoC hR.charC hm hmr hlow
    have hq' : ((C.step m r).iterate m r q).2.maxStratumWeight r < m := hq
    have hmin' : ∀ q' < q, m ≤ ((C.step m r).iterate m r q').2.maxStratumWeight r :=
      fun q' h' => hmin (q' + 1) (by omega)
    by_cases hZ : (C.stepCenter r).comap h = ⊤
    · obtain ⟨qD, h1, h2, h3⟩ := phase m r hr hm KC KD hK q _ (C.step m r) D
        (rel_skip hR hr hm hmr hZ) hlow' hq' hmin'
      refine ⟨qD, h1, h2, ?_⟩
      rw [h3]
      show _ = ClosedBlowupSequence.pullbackReduced
        (ClosedBlowupSequence.cons (C.stepCenter r) (stepPhase m r KC q (C.step m r))) h
      simp only [ClosedBlowupSequence.pullbackReduced, hZ, dite_true]
    · obtain ⟨hw, hc⟩ := stepCenter_comap hR hZ
      obtain ⟨qD, h1, h2, h3⟩ := phase m r hr hm KC KD hK q _ (C.step m r)
        (stepAt D m ((C.stepCenter r).comap h)) (rel_step hR hr hm hmr hZ) hlow' hq' hmin'
      refine ⟨qD + 1, ?_, ?_, ?_⟩
      · exact (stepAt_congr_fun hc D m
          (fun D => (D.iterate m r qD).2.maxStratumWeight r)).trans_lt h1
      · intro q' hq'
        rcases q' with _ | q'
        · show m ≤ D.maxStratumWeight r
          rwa [hw]
        · exact (h2 q' (by omega)).trans_eq (stepAt_congr_fun hc D m
            (fun D => (D.iterate m r q').2.maxStratumWeight r)).symm
      · show ClosedBlowupSequence.cons (D.stepCenter r)
            (stepPhase m r KD qD (stepAt D m (D.stepCenter r))) = _
        refine (cons_stepAt_congr hc D m (fun D => stepPhase m r KD qD D)).trans ?_
        rw [h3]
        show _ = ClosedBlowupSequence.pullbackReduced
          (ClosedBlowupSequence.cons (C.stepCenter r) (stepPhase m r KC q (C.step m r))) h
        simp only [ClosedBlowupSequence.pullbackReduced, hZ, dite_false]

/-- The concatenated phases `r, …, r + j - 1` on `Y` are the pull-back of those on `X` with
empty blow-ups deleted. -/
private theorem main (m : ℕ) (hm : 1 ≤ m) : ∀ (j r : ℕ) {X Y : Scheme.{u}} (h : Y ⟶ X)
    (C : MonomialData X) (D : MonomialData Y), Rel h C D → 1 ≤ r →
    (∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m) →
    monomialOrderReductionFrom m j r D = (monomialOrderReductionFrom m j r C).pullbackReduced h
  | 0, r, X, Y, h, C, D, _, _, _ => rfl
  | j + 1, r, X, Y, h, C, D, hR, hr, hlow => by
    have hex := exists_iterate_lt C hR.monoC hR.charC hr hm hlow
    obtain ⟨qD, h1, h2, h3⟩ := phase m r hr hm
      (fun C => monomialOrderReductionFrom m j (r + 1) C)
      (fun D => monomialOrderReductionFrom m j (r + 1) D)
      (fun h' C' D' hR' hl' => main m hm j (r + 1) h' C' D' hR' (by omega)
        fun t ht1 htr => hl' t ht1 (by omega))
      (Nat.find hex) h C D hR hlow (Nat.find_spec hex)
      (fun q' hq' => not_lt.1 (Nat.find_min hex hq'))
    have hexD : ∃ N, (D.iterate m r N).2.maxStratumWeight r < m := ⟨qD, h1⟩
    simp only [monomialOrderReductionFrom, dif_pos hex, dif_pos hexD]
    rw [(Nat.find_eq_iff hexD).2 ⟨h1, fun n hn => not_lt.2 (h2 n hn)⟩]
    exact h3

end Step

/-! ### Phases beyond the dimension -/

section Dimension

/-- Monomial data in characteristic zero on a scheme of dimension at most `d`. -/
private def Inv (d : ℕ) {X : Scheme.{u}} (C : MonomialData X) : Prop :=
  C.IsMonomialData ∧ CharZero C.k ∧ dimNat X ≤ d

/-- A blow-up of a scheme locally of finite type over a field does not raise the dimension. -/
private theorem dimNat_blowUp_le {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (Z : X.IdealSheafData) : dimNat (blowUp Z) ≤ dimNat X := by
  have hle : topologicalKrullDim (blowUp Z) ≤ topologicalKrullDim X :=
    MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents fun C hC => by
      obtain ⟨D, -, h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp sX Z hC
      rw [h]; exact topologicalKrullDim_subspace_le X D
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hne : topologicalKrullDim X ≠ ⊤ := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  unfold dimNat
  generalize topologicalKrullDim X = b at hle hne
  generalize topologicalKrullDim (blowUp Z) = a at hle
  induction b using WithBot.recBotCoe with
  | bot => simp at hle; subst hle; simp
  | coe b =>
    induction a using WithBot.recBotCoe with
    | bot => simp
    | coe a =>
      simp only [WithBot.unbotD_coe]
      have : a ≤ b := WithBot.coe_le_coe.mp hle
      have hb : b ≠ ⊤ := fun h => hne (by simp [h])
      exact ENat.toNat_le_toNat this hb

open Classical in
/-- The members of `E` through `x`. -/
private noncomputable def throughIndex {X : Scheme.{u}} (C : MonomialData X) (x : X) :
    Finset (Fin C.E.s) :=
  Finset.univ.filter fun j => x ∈ ((C.E.E j).support : Set X)

/-- At most `dim X` members of the snc divisor `E` pass through a point. -/
private theorem card_throughIndex_le {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (x : X) : (throughIndex C x).card ≤ dimNat X := by
  classical
  obtain ⟨-, hlft, hqc, hsnc, -, -⟩ := hC
  have : LocallyOfFiniteType C.sX := hlft
  have : QuasiCompact C.sX := hqc
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace C.sX
  have hne : topologicalKrullDim X ≠ ⊤ := topologicalKrullDim_ne_top_of_locallyOfFiniteType C.k C.sX
  obtain ⟨n, z, c, hz, -, hc⟩ := hsnc.2.2 x
  have hcard : (throughIndex C x).card ≤ n := by
    have := Fintype.card_le_of_injective c hc
    simp only [Fintype.card_fin] at this
    refine le_trans (le_of_eq ?_) this
    rw [Fintype.card_subtype]; rfl
  have hdim : ((n : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    have h1 : ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
      rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      exact le_iSup_of_le x le_rfl
    rw [hz.2] at h1; exact_mod_cast h1
  refine hcard.trans ?_
  unfold dimNat
  generalize topologicalKrullDim X = b at hne hdim
  induction b using WithBot.recBotCoe with
  | bot => simp at hdim
  | coe b =>
    simp only [WithBot.unbotD_coe]
    have hb : b ≠ ⊤ := fun h => hne (by simp [h])
    have : (n : ℕ∞) ≤ b := WithBot.coe_le_coe.mp hdim
    exact (ENat.toNat_le_toNat this hb).trans_eq' (by simp)

private theorem maxStratumWeight_eq_zero_of_lt {d : ℕ} {X : Scheme.{u}} {C : MonomialData X}
    (hC : Inv d C) {r : ℕ} (hr : d < r) : C.maxStratumWeight r = 0 := by
  classical
  refine Nat.eq_zero_of_le_zero
    (ciSup_le' fun J => ciSup_le' fun hJ => ciSup_le' fun x => ciSup_le' fun hx => ?_)
  exfalso
  have hsub : J ⊆ throughIndex C x := fun j hj => by
    simp only [throughIndex, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [MonomialData.stratum, Set.mem_iInter] at hx
    exact hx j hj
  have := (Finset.card_le_card hsub).trans (card_throughIndex_le C hC.1 x)
  have := hC.2.2
  omega

private theorem inv_step {d m r : ℕ} {X : Scheme.{u}} {C : MonomialData X} (hC : Inv d C)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ C.maxStratumWeight r) : Inv d (C.step m r) := by
  obtain ⟨hC', hk, hd⟩ := hC
  have hspec := step_spec C hC' hk hr hm hmr
  obtain ⟨-, hlft, hqc, -⟩ := hC'
  haveI : LocallyOfFiniteType C.sX := hlft
  haveI : QuasiCompact C.sX := hqc
  exact ⟨hspec.2.2.2.1, hk, (dimNat_blowUp_le C.sX _).trans hd⟩

private theorem stepPhase_congr_inv {d m r : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (K K' : ∀ {Y : Scheme.{u}}, MonomialData Y → ClosedBlowupSequence Y)
    (hK : ∀ {Y : Scheme.{u}} (D : MonomialData Y), Inv d D → K D = K' D) :
    ∀ (q : ℕ) {X : Scheme.{u}} (C : MonomialData X), Inv d C →
      (∀ q' < q, m ≤ (C.iterate m r q').2.maxStratumWeight r) →
        stepPhase m r K q C = stepPhase m r K' q C
  | 0, _, C, hC, _ => hK C hC
  | q + 1, _, C, hC, hq => by
    have hmr : m ≤ C.maxStratumWeight r := hq 0 (Nat.succ_pos _)
    show ClosedBlowupSequence.cons _ (stepPhase m r K q (C.step m r)) =
      ClosedBlowupSequence.cons _ (stepPhase m r K' q (C.step m r))
    rw [stepPhase_congr_inv hr hm K K' hK q (C.step m r) (inv_step hC hr hm hmr)
      fun q' hq' => hq (q' + 1) (by omega)]

/-- All phases beyond the dimension are empty. -/
private theorem from_eq_nil {d m : ℕ} (hm : 1 ≤ m) : ∀ (j r : ℕ) {X : Scheme.{u}}
    (C : MonomialData X), Inv d C → d < r → monomialOrderReductionFrom m j r C = .nil X
  | 0, _, _, _, _, _ => rfl
  | j + 1, r, X, C, hC, hr => by
    have h0 : (C.iterate m r 0).2.maxStratumWeight r < m := by
      show C.maxStratumWeight r < m
      rw [maxStratumWeight_eq_zero_of_lt hC hr]; omega
    have hex : ∃ N, (C.iterate m r N).2.maxStratumWeight r < m := ⟨0, h0⟩
    simp only [monomialOrderReductionFrom, dif_pos hex]
    rw [(Nat.find_eq_iff hex).2 ⟨h0, fun n hn => absurd hn (Nat.not_lt_zero _)⟩]
    exact from_eq_nil hm j (r + 1) C hC (by omega)

/-- Adding phases beyond the dimension does not change the sequence. -/
private theorem from_add {d m : ℕ} (hm : 1 ≤ m) (e : ℕ) : ∀ (j r : ℕ) {X : Scheme.{u}}
    (C : MonomialData X), Inv d C → 1 ≤ r → d + 1 ≤ r + j →
      monomialOrderReductionFrom m j r C = monomialOrderReductionFrom m (j + e) r C
  | 0, r, X, C, hC, hr, hrj => by
    rw [Nat.zero_add, from_eq_nil hm e r C hC (by omega)]
    rfl
  | j + 1, r, X, C, hC, hr, hrj => by
    rw [show j + 1 + e = (j + e) + 1 by omega]
    simp only [monomialOrderReductionFrom]
    split_ifs with hex
    · exact stepPhase_congr_inv hr hm _ _
        (fun D hD => from_add hm e j (r + 1) D hD (by omega) (by omega)) _ C hC
        (fun q' hq' => not_lt.1 (Nat.find_min hex hq'))
    · exact from_add hm e j (r + 1) C hC (by omega) (by omega)

/-- With marking `0` no phase ever ends, and the sequence is empty. -/
private theorem from_zero : ∀ (j r : ℕ) {X : Scheme.{u}} (C : MonomialData X),
    monomialOrderReductionFrom 0 j r C = .nil X
  | 0, _, _, _ => rfl
  | j + 1, r, X, C => by
    have hex : ¬ ∃ N, (C.iterate 0 r N).2.maxStratumWeight r < 0 :=
      fun ⟨N, hN⟩ => Nat.not_lt_zero _ hN
    simp only [monomialOrderReductionFrom, dif_neg hex]
    exact from_zero j (r + 1) C

end Dimension

/-- **Kollár 3.111, Step 3.** Let `C = (X, E, A)` be monomial data and `h : Y → X` either a
smooth morphism with `Y` quasi-compact over the ground field `k`, or the projection `X_L → X`
for a field extension `k → L`. If `D` is monomial data on `Y` with ordered divisor `h⁻¹E` and
divisor `h^*A`, then for every marking `m` the monomial order reduction sequence of `D` is
`(h^*𝐁)^red`, `𝐁` the monomial order reduction sequence of `C`. -/
@[mmp "lem_kr3e_monomial_order_reduction_commutes_smooth"]
public theorem monomialOrderReduction_eq_pullback_reduction {X : Scheme.{u}}
    (C : MonomialData X) (hC : C.IsMonomialData) (hk : CharZero C.k)
    {Y : Scheme.{u}} (h : Y ⟶ X)
    (hh : (Smooth h ∧ QuasiCompact (h ≫ C.sX)) ∨
      ∃ (L : Type u) (_ : Field L) (σ : C.k →+* L) (q : Y ⟶ Spec (.of L)),
        IsPullback h q C.sX (Spec.map (CommRingCat.ofHom σ)))
    (D : MonomialData Y) (hE : D.E = C.E.comap h)
    (hA : D.A = fun D' => (multAt ((divisorIdeal C.A).comap h) D'.genericPoint).toNat)
    (m : ℕ) :
    D.monomialOrderReduction m = ((C.monomialOrderReduction m).pullback h).reduction := by
  rw [show ((C.monomialOrderReduction m).pullback h).reduction =
      (C.monomialOrderReduction m).pullbackReduced h from
    eq_of_heq (ClosedBlowupSequence.pullback_pullbackReduced_heq _ h (𝟙 Y) h rfl (by simp))]
  obtain ⟨D₀, hE₀, hA₀, hR⟩ := exists_rel_init C hC hk h hh D hE hA
  have hD : D.monomialOrderReduction m = D₀.monomialOrderReduction m :=
    from_eq_of_eq m _ 1 D D₀ hE₀.symm hA₀.symm
  rw [hD]
  show monomialOrderReductionFrom m (dimNat Y) 1 D₀ =
    (monomialOrderReductionFrom m (dimNat X) 1 C).pullbackReduced h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [from_zero, from_zero]; rfl
  · have hC' := from_add (d := dimNat X) hm (dimNat Y) (dimNat X) 1 C ⟨hC, hk, le_rfl⟩ le_rfl
      (by omega)
    have hD' := from_add (d := dimNat Y) hm (dimNat X) (dimNat Y) 1 D₀
      ⟨hR.monoD, hR.charD, le_rfl⟩ le_rfl (by omega)
    rw [hC', hD', Nat.add_comm (dimNat Y)]
    exact main m hm _ 1 h C D₀ hR le_rfl fun t ht1 htr => by omega

end MMP.Resolution.MonomialData
