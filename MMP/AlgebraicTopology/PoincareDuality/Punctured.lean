module

public import MMP.AlgebraicTopology.PoincareDuality.Localize
public import MMP.AlgebraicTopology.PoincareDuality.Homotopy

/-!
# The homology of the punctured space `ℝⁿ - 0`

In the finite model of singular chains, the homology `H_k(ℝⁿ - 0; R)` vanishes for `k ≥ n ≥ 1`.

* Star-shaped sets have vanishing homology in positive degrees.
* Homotopy transfer: if `f : Y → Z` and `g : Z → Y` map `A` into `B` and `B` into `A`, and `g ∘ f`
  is homotopic to the identity through maps sending `A` into `A`, then the vanishing of
  `H_{m+1}(B)` gives the vanishing of `H_{m+1}(A)`.
* Mayer–Vietoris for two disjoint open sets, in every degree.
* `ℝⁿ⁺¹ - 0` is the union of the complements `U`, `V` of the two closed half-axes along the last
  coordinate; both are star-shaped, and `U ∩ V`, the complement of the last axis, deformation
  retracts onto `ℝⁿ - 0` by `Fin.init`. Induction on `n` with Mayer–Vietoris.

## Main results

* `MMP.SingularChain.cycleVanishing_of_starConvex`
* `MMP.SingularChain.CycleVanishing.of_homotopy`
* `MMP.SingularChain.CycleVanishing.union_of_disjoint`
* `MMP.SingularChain.cycleVanishing_compl_zero`: `H_{j+1}(ℝⁿ - 0) = 0` for
  `n ≤ j + 1`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Corollary 2.11 and §2.2, Corollary 2.14
  (homology of spheres).
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

section general

/-- Star-shaped sets have vanishing homology in positive degrees. -/
theorem cycleVanishing_of_starConvex {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {C : Set E} {p : E}
    (hC : StarConvex ℝ p C) (m : ℕ) : CycleVanishing R E m C :=
  fun _ hc hbd ↦ exists_bd_eq_of_starConvex hC hc hbd

/-- **Homotopy transfer** of the vanishing of `H_{m+1}`: if `f` maps `A` into `B`, `g` maps `B`
into `A`, and `F` is a homotopy from `g ∘ f` to the identity sending `A × [0, 1]` into `A`, then
`H_{m+1}(B) = 0` implies `H_{m+1}(A) = 0`. -/
theorem CycleVanishing.of_homotopy {m : ℕ} {A : Set Y} {B : Set Z} (f : C(Y, Z)) (g : C(Z, Y))
    (hf : MapsTo f A B) (hg : MapsTo g B A) (F : C(Y × unitInterval, Y))
    (hF₀ : ∀ y, F (y, 0) = g (f y)) (hF₁ : ∀ y, F (y, 1) = y) (hF : MapsTo F (A ×ˢ univ) A)
    (h : CycleVanishing R Z m B) : CycleVanishing R Y m A := by
  intro z hz hbz
  obtain ⟨w, hw, hbw⟩ := h (postcomp R f (m + 1) z) (postcomp_mem_inside f hf hz)
    (by rw [← postcomp_bd, hbz, map_zero])
  have hP := bd_prism_add_prism_bd (R := R) F (f := g.comp f) (g := ContinuousMap.id Y)
    hF₀ hF₁ m z
  rw [hbz, map_zero, add_zero, postcomp_id, ← postcomp_comp, ← hbw, postcomp_bd] at hP
  refine ⟨prism R F (m + 1) z + postcomp R g (m + 2) w,
    Submodule.add_mem _ (prism_mem_inside F hF hz) (postcomp_mem_inside g hg hw), ?_⟩
  rw [map_add, hP, sub_add_cancel]

/-- A chain supported in the empty set is zero. -/
lemma eq_zero_of_mem_inside_empty {n : ℕ} {c : Chain R Y n} (hc : c ∈ inside R n (∅ : Set Y)) :
    c = 0 := by
  by_contra h0
  obtain ⟨y, hy⟩ := nonempty_of_mem_inside hc h0
  exact hy

/-- Mayer–Vietoris for two disjoint open sets, in every degree: the vanishing of `H_{m+1}(U)` and
`H_{m+1}(V)` gives the vanishing of `H_{m+1}(U ∪ V)`. -/
theorem CycleVanishing.union_of_disjoint {m : ℕ} {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (h₁ : CycleVanishing R Y m U) (h₂ : CycleVanishing R Y m V) :
    CycleVanishing R Y m (U ∪ V) := by
  intro z hz hbz
  set 𝒰 : Set (Set Y) := {U, V}
  have h𝒰 : ∀ W ∈ 𝒰, IsOpen W := by
    rintro W (rfl | rfl) <;> assumption
  have hz' : z ∈ inside R (m + 1) (⋃₀ 𝒰) := by
    simpa [𝒰] using hz
  obtain ⟨a, ha, b, hb, hsplit⟩ :=
    exists_add_of_mem_small_pair (smallChainMap_mem_small h𝒰 (m + 1) hz')
  rw [smallChainMap_succ, hbz, map_zero, sub_zero] at hsplit
  have hab : bd R m a = -bd R m b := by
    have := congrArg (bd R m) hsplit
    rw [map_sub, bd_bd, hbz, sub_zero, map_add] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hba0 : bd R m a = 0 := by
    refine eq_zero_of_mem_inside_empty (Y := Y) ?_
    rw [← hUV.inter_eq, inside_inter]
    refine ⟨bd_mem_inside ha, ?_⟩
    rw [hab]
    exact Submodule.neg_mem _ (bd_mem_inside hb)
  have hbb0 : bd R m b = 0 := by
    rw [← neg_eq_zero, ← hab, hba0]
  obtain ⟨eU, heU, hbeU⟩ := h₁ a ha hba0
  obtain ⟨eV, heV, hbeV⟩ := h₂ b hb hbb0
  refine ⟨smallHomotopy R 𝒰 (m + 1) z + eU + eV, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.add_mem _ (smallHomotopy_mem_inside_of_mem 𝒰 hz)
      (inside_mono _ subset_union_left heU)) (inside_mono _ subset_union_right heV)
  · rw [map_add, map_add, hbeU, hbeV]
    calc _ = bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) z) + (a + b) := by abel
      _ = z := by
        rw [← hsplit]
        abel

end general

section punctured

/-- The complement of the closed half-axis `{t • (-ε) e | t ≥ 0}` along the last coordinate of
`ℝⁿ⁺¹`: the points off the last axis, or on it with `0 < ε xₙ`. -/
def halfAxisCompl (n : ℕ) (ε : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {x | Fin.init x ≠ 0 ∨ 0 < ε * x (Fin.last n)}

/-- `halfAxisCompl n ε` is open. -/
lemma isOpen_halfAxisCompl (n : ℕ) (ε : ℝ) : IsOpen (halfAxisCompl n ε) := by
  refine IsOpen.union ?_ ?_
  · exact (isClosed_eq (continuous_id.finInit) continuous_const).isOpen_compl
  · exact isOpen_lt continuous_const (continuous_const.mul (continuous_apply _))

/-- `Fin.init (a • ε eₙ + b • x) = b • Fin.init x`. -/
lemma init_smul_add_smul_single (n : ℕ) (ε a b : ℝ) (x : Fin (n + 1) → ℝ) :
    Fin.init (a • Pi.single (Fin.last n) ε + b • x) = b • Fin.init x := by
  funext i
  simp [Fin.init]

/-- `halfAxisCompl n ε` is star-shaped about `ε e`. -/
lemma starConvex_halfAxisCompl (n : ℕ) {ε : ℝ} (hε : ε ≠ 0) :
    StarConvex ℝ (Pi.single (Fin.last n) ε) (halfAxisCompl n ε) := by
  intro x hx a b ha hb hab
  have hlast : ε * (a • Pi.single (Fin.last n) ε + b • x : Fin (n + 1) → ℝ) (Fin.last n) =
      a * (ε * ε) + b * (ε * x (Fin.last n)) := by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
    ring
  have hεε : 0 < ε * ε := mul_self_pos.2 hε
  change Fin.init _ ≠ 0 ∨ 0 < ε * _
  rw [init_smul_add_smul_single, hlast]
  rcases hb.eq_or_lt with rfl | hb'
  · right
    rw [add_zero] at hab
    rw [hab, zero_mul, add_zero, one_mul]
    exact hεε
  rcases hx with h | h
  · exact Or.inl (smul_ne_zero hb'.ne' h)
  · exact Or.inr (add_pos_of_nonneg_of_pos (mul_nonneg ha hεε.le) (mul_pos hb' h))

/-- A vector of `ℝⁿ⁺¹` is zero iff its first `n` coordinates and its last coordinate vanish. -/
lemma init_eq_zero_and_last_eq_zero_iff {n : ℕ} (x : Fin (n + 1) → ℝ) :
    Fin.init x = 0 ∧ x (Fin.last n) = 0 ↔ x = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    funext i
    induction i using Fin.lastCases with
    | last => exact h2
    | cast j => exact congrFun h1 j
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- The complements of the two closed half-axes along the last coordinate cover `ℝⁿ⁺¹ - 0`. -/
lemma halfAxisCompl_union (n : ℕ) :
    halfAxisCompl n 1 ∪ halfAxisCompl n (-1) = ({0}ᶜ : Set (Fin (n + 1) → ℝ)) := by
  ext x
  simp only [halfAxisCompl, mem_union, mem_ofPred_eq, mem_compl_iff, mem_singleton_iff,
    ← init_eq_zero_and_last_eq_zero_iff, one_mul, neg_one_mul, neg_pos, not_and_or]
  grind

/-- The intersection of the complements of the two closed half-axes is the complement of the last
axis. -/
lemma halfAxisCompl_inter (n : ℕ) :
    halfAxisCompl n 1 ∩ halfAxisCompl n (-1) = {x : Fin (n + 1) → ℝ | Fin.init x ≠ 0} := by
  ext x
  simp only [halfAxisCompl, mem_inter_iff, mem_ofPred_eq, one_mul, neg_one_mul, neg_pos]
  grind

/-- `Fin.init` as a continuous map. -/
def initMap (n : ℕ) : C(Fin (n + 1) → ℝ, Fin n → ℝ) :=
  ⟨Fin.init, continuous_id.finInit⟩

/-- `y ↦ (y, 0)` as a continuous map. -/
def snocZeroMap (n : ℕ) : C(Fin n → ℝ, Fin (n + 1) → ℝ) :=
  ⟨fun y ↦ Fin.snoc (α := fun _ ↦ ℝ) y (0 : ℝ), by fun_prop⟩

/-- `initMap n x = Fin.init x`. -/
lemma initMap_apply (n : ℕ) (x : Fin (n + 1) → ℝ) : initMap n x = Fin.init x := rfl

/-- `snocZeroMap n y = Fin.snoc y 0`. -/
lemma snocZeroMap_apply (n : ℕ) (y : Fin n → ℝ) :
    snocZeroMap n y = Fin.snoc (α := fun _ ↦ ℝ) y (0 : ℝ) := rfl

/-- The homotopy `(x, t) ↦ (Fin.init x, t xₙ)` from `snocZeroMap ∘ initMap` to the identity. -/
def flattenHomotopy (n : ℕ) : C((Fin (n + 1) → ℝ) × unitInterval, Fin (n + 1) → ℝ) :=
  ⟨fun p ↦ Fin.snoc (α := fun _ ↦ ℝ) (Fin.init p.1) ((p.2 : ℝ) * p.1 (Fin.last n)),
    (continuous_fst.finInit).finSnoc
      ((continuous_subtype_val.comp continuous_snd).mul
        ((continuous_apply _).comp continuous_fst))⟩

/-- `flattenHomotopy n (x, t) = Fin.snoc (Fin.init x) (t xₙ)`. -/
lemma flattenHomotopy_apply (n : ℕ) (x : Fin (n + 1) → ℝ) (t : unitInterval) :
    flattenHomotopy n (x, t) =
      Fin.snoc (α := fun _ ↦ ℝ) (Fin.init x) ((t : ℝ) * x (Fin.last n)) := rfl

/-- `H_{j+1}(ℝⁿ⁺¹ - 0; R) = 0` for `n + 1 ≤ j + 1`. -/
theorem cycleVanishing_compl_zero_succ (n : ℕ) :
    ∀ j, n + 1 ≤ j + 1 → CycleVanishing R (Fin (n + 1) → ℝ) j {0}ᶜ := by
  induction n with
  | zero =>
    intro j _
    rw [← halfAxisCompl_union]
    refine CycleVanishing.union_of_disjoint (isOpen_halfAxisCompl 0 1)
      (isOpen_halfAxisCompl 0 (-1)) ?_
      (cycleVanishing_of_starConvex (starConvex_halfAxisCompl 0 one_ne_zero) j)
      (cycleVanishing_of_starConvex (starConvex_halfAxisCompl 0 (neg_ne_zero.2 one_ne_zero)) j)
    rw [disjoint_iff_inter_eq_empty, halfAxisCompl_inter]
    exact eq_empty_of_forall_notMem fun x hx ↦ hx (Subsingleton.elim _ _)
  | succ n ih =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [← halfAxisCompl_union]
    refine CycleVanishing.union (isOpen_halfAxisCompl _ 1) (isOpen_halfAxisCompl _ (-1))
      (cycleVanishing_of_starConvex (starConvex_halfAxisCompl _ one_ne_zero) _)
      (cycleVanishing_of_starConvex (starConvex_halfAxisCompl _ (neg_ne_zero.2 one_ne_zero)) _)
      ?_
    rw [halfAxisCompl_inter]
    refine CycleVanishing.of_homotopy (initMap (n + 1)) (snocZeroMap (n + 1))
      (fun x hx ↦ hx) (fun y hy ↦ ?_) (flattenHomotopy (n + 1)) (fun x ↦ ?_) (fun x ↦ ?_)
      (fun p hp ↦ ?_) (ih j (by omega))
    · simpa [snocZeroMap_apply, Fin.init_snoc] using hy
    · rw [flattenHomotopy_apply, initMap_apply, snocZeroMap_apply, Set.Icc.coe_zero, zero_mul]
    · rw [flattenHomotopy_apply, Set.Icc.coe_one, one_mul, Fin.snoc_init_self]
    · obtain ⟨x, t⟩ := p
      change Fin.init (flattenHomotopy (n + 1) (x, t)) ≠ 0
      rw [flattenHomotopy_apply, Fin.init_snoc]
      exact hp.1

/-- **The homology of `ℝⁿ - 0` vanishes in degrees `≥ n`**: `H_{j+1}(ℝⁿ - 0; R) = 0` for
`1 ≤ n ≤ j + 1`. -/
theorem cycleVanishing_compl_zero (n : ℕ) (hn : 1 ≤ n) :
    ∀ j, n ≤ j + 1 → CycleVanishing R (Fin n → ℝ) j {0}ᶜ := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact cycleVanishing_compl_zero_succ n

end punctured

end SingularChain

end MMP
