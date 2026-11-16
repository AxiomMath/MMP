module

public import MMP.AlgebraicTopology.BorelMoore.Restriction
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Borel–Moore boundaries from relative boundaries on compact sets

Let `X` be a weakly locally compact, σ-compact space, and `K₀ ⊆ K₁ ⊆ ⋯` a compact exhaustion
(`K_j ⊆ interior K_{j+1}`, `⋃ K_j = X`). A locally finite chain `c` is *off* a set `K` if every
simplex of `c` whose image meets `K` has coefficient `0`; modulo chains off `K`, a locally finite
chain is the finite chain of its simplices meeting `K` (when `K` is compact), so this is the
relative complex `C_•(X) / C_•(X - K)` of singular chains of the pair `(X, X - K)`.

The locally finite chains are the inverse limit of these relative complexes along the
exhaustion. The usual lifting argument for the `lim¹`-term of the Milnor sequence then shows:
**if a locally finite `m`-chain `z` is a boundary modulo chains off `K` for every compact `K`,
and every finite `(m + 1)`-chain whose boundary is off `K` is a boundary modulo chains off `K`
(that is, `H_{m+1}(X, X - K) = 0` for every compact `K`), then `z` is the boundary of a locally
finite chain.** Indeed, with `z - ∂ w_j` off `K_j`, the differences `w_{j+1} - w_j` are relative
cycles of `(X, X - K_j)`, hence relative boundaries, and correcting `w_{j+1}` by a boundary makes
`w_{j+1} - w_j` off `K_j`; the limit `w = lim w_j` is a locally finite chain with `∂ w = z`.

In particular, if `H_{m+1}(X, X - K) = 0` and `H_{m+2}(X, X - K) = 0` for every compact `K`, then
the Borel–Moore homology `H_{m+1} X` vanishes. This is the passage from local homology to
Borel–Moore homology in the proof that `H_i Y = 0` for `i > n` and `H_n Y ≅ R` for a connected
oriented `n`-manifold `Y` (top-degree Poincaré duality, Fulton §19.1, (3)).

## Main definitions

* `MMP.borelMooreHomology.IsOffChain`: a locally finite chain vanishes on the
  simplices meeting `K`.
* `MMP.borelMooreHomology.truncChain`: the finite chain of the simplices of a
  locally finite chain meeting a compact set `K`.
* `MMP.borelMooreHomology.RelVanishingBM`: every finite `(m + 1)`-chain whose
  boundary is off `K` is a boundary modulo chains off `K`, i.e. `H_{m+1}(X, X - K) = 0`.

## Main results

* `MMP.borelMooreHomology.exists_d_eq_of_forall_isCompact`: the lifting argument.
* `MMP.borelMooreHomology.isZero_of_relVanishingBM`: `H_{m+1} X = 0` when
  `H_{m+1}(X, X - K) = H_{m+2}(X, X - K) = 0` for every compact `K`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3 and §3.F (the Milnor sequence).
* [B. Iversen, *Cohomology of Sheaves*][iversen1986], IX.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial

universe u

namespace MMP

namespace borelMooreHomology

open LocallyFiniteChain

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {X : TopCat.{u}}

/-- A locally finite `n`-chain `c` of `X` is *off* `K`: its coefficient on every simplex whose
image meets `K` is zero (it is a chain of `X - K`). -/
def IsOffChain (K : Set X) {n : ℕ} (c : (borelMooreChainComplex R M X).X n) : Prop :=
  ∀ σ, (singularSimplexImage X σ ∩ K).Nonempty → c.1 σ = 0

namespace IsOffChain

variable {K K' : Set X} {n : ℕ} {c c' : (borelMooreChainComplex R M X).X n}

/-- The zero chain is off `K`. -/
lemma zero : IsOffChain K (0 : (borelMooreChainComplex R M X).X n) := fun _ _ ↦ rfl

/-- A sum of chains off `K` is off `K`. -/
lemma add (hc : IsOffChain K c) (hc' : IsOffChain K c') : IsOffChain K (c + c') :=
  fun σ hσ ↦ by
    change c.1 σ + c'.1 σ = 0
    rw [hc σ hσ, hc' σ hσ, add_zero]

/-- The negative of a chain off `K` is off `K`. -/
lemma neg (hc : IsOffChain K c) : IsOffChain K (-c) := fun σ hσ ↦ by
  change -c.1 σ = 0
  rw [hc σ hσ, neg_zero]

/-- A difference of chains off `K` is off `K`. -/
lemma sub (hc : IsOffChain K c) (hc' : IsOffChain K c') : IsOffChain K (c - c') := by
  rw [sub_eq_add_neg]
  exact hc.add hc'.neg

/-- A chain off `K` is off every subset `K'` of `K`. -/
lemma mono (hc : IsOffChain K c) (h : K' ⊆ K) : IsOffChain K' c := fun σ hσ ↦
  hc σ (hσ.mono (inter_subset_inter_right _ h))

/-- If `c - c'` is off `K`, then `c` and `c'` have the same coefficient on every simplex whose
image meets `K`. -/
lemma eq_of_sub (hc : IsOffChain K (c - c')) {σ} (hσ : (singularSimplexImage X σ ∩ K).Nonempty) :
    c.1 σ = c'.1 σ :=
  sub_eq_zero.1 (hc σ hσ)

/-- The boundary of a chain off `K` is off `K`. -/
lemma d {c : (borelMooreChainComplex R M X).X (n + 1)} (hc : IsOffChain K c) :
    IsOffChain K (((borelMooreChainComplex R M X).d (n + 1) n).hom c) := by
  intro τ hτ
  rw [borelMooreChainComplex_d_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [pushforwardFun, finsum_eq_zero_of_forall_eq_zero, smul_zero]
  intro σ
  split_ifs with h
  · refine hc σ (hτ.mono (inter_subset_inter_left _ ?_))
    rw [← h]
    exact singularSimplexImage_map_subset _ σ
  · rfl

end IsOffChain

open Classical in
/-- The chain of the simplices of a locally finite chain `c` whose image meets `K`. -/
def truncChain (K : Set X) {n : ℕ} (c : (borelMooreChainComplex R M X).X n) :
    (borelMooreChainComplex R M X).X n :=
  ⟨fun σ ↦ if (singularSimplexImage X σ ∩ K).Nonempty then c.1 σ else 0,
    IsLocallyFiniteSet.mono c.2 fun σ hσ ↦ by
      by_contra h
      apply hσ
      simp only
      split_ifs
      · exact Function.notMem_support.1 h
      · rfl⟩

open Classical in
/-- The coefficient of `truncChain K c` on `σ` is that of `c` if the image of `σ` meets `K`, and
`0` otherwise. -/
lemma truncChain_apply (K : Set X) {n : ℕ} (c : (borelMooreChainComplex R M X).X n) (σ) :
    (truncChain K c).1 σ =
      if (singularSimplexImage X σ ∩ K).Nonempty then c.1 σ else 0 :=
  rfl

/-- A chain differs from its truncation to `K` by a chain off `K`. -/
lemma isOffChain_sub_truncChain (K : Set X) {n : ℕ} (c : (borelMooreChainComplex R M X).X n) :
    IsOffChain K (c - truncChain K c) := fun σ hσ ↦ by
  change c.1 σ - (truncChain K c).1 σ = 0
  rw [truncChain_apply, if_pos hσ, sub_self]

/-- The truncation of a locally finite chain to a compact set is a finite chain. -/
lemma finite_support_truncChain {K : Set X} (hK : IsCompact K) {n : ℕ}
    (c : (borelMooreChainComplex R M X).X n) : (Function.support (truncChain K c).1).Finite := by
  refine (c.2.finite_inter_compact hK).subset fun σ hσ ↦ ?_
  rw [Function.mem_support, truncChain_apply] at hσ
  split_ifs at hσ with h
  · exact ⟨hσ, h⟩
  · exact absurd rfl hσ

variable (X) in
/-- `H_{m+1}(X, X - K) = 0`, on chains: every finite `(m + 1)`-chain `c` whose boundary is off
`K` (a relative cycle of `(X, X - K)`) is a boundary modulo chains off `K`. -/
def RelVanishingBM (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (m : ℕ) (K : Set X) : Prop :=
  ∀ c : (borelMooreChainComplex R M X).X (m + 1), (Function.support c.1).Finite →
    IsOffChain K (((borelMooreChainComplex R M X).d (m + 1) m).hom c) →
    ∃ w : (borelMooreChainComplex R M X).X (m + 2),
      IsOffChain K (c - ((borelMooreChainComplex R M X).d (m + 2) (m + 1)).hom w)

/-- If `RelVanishingBM X R M m K` holds for a compact `K`, then every locally finite
`(m + 1)`-chain whose boundary is off `K` is a boundary modulo chains off `K`. -/
lemma RelVanishingBM.exists_of_isOffChain_d {m : ℕ} {K : Set X} (hK : IsCompact K)
    (h : RelVanishingBM X R M m K) (c : (borelMooreChainComplex R M X).X (m + 1))
    (hc : IsOffChain K (((borelMooreChainComplex R M X).d (m + 1) m).hom c)) :
    ∃ w : (borelMooreChainComplex R M X).X (m + 2),
      IsOffChain K (c - ((borelMooreChainComplex R M X).d (m + 2) (m + 1)).hom w) := by
  set D := ((borelMooreChainComplex R M X).d (m + 1) m).hom
  have h1 : IsOffChain K (D (truncChain K c)) := by
    have := hc.sub (isOffChain_sub_truncChain K c).d
    rwa [map_sub, sub_sub_cancel] at this
  obtain ⟨w, hw⟩ := h (truncChain K c) (finite_support_truncChain hK c) h1
  refine ⟨w, ?_⟩
  have := (isOffChain_sub_truncChain K c).add hw
  rwa [sub_add_sub_cancel] at this

/-- A sequence of chains whose successive differences are off `K j` has a limit `W` with
`W - s j` off `K j` for every `j`. -/
theorem exists_isOffChain_sub_of_isOffChain_succ_sub (K : CompactExhaustion X) {n : ℕ}
    (s : ℕ → (borelMooreChainComplex R M X).X n)
    (hs : ∀ j, IsOffChain (K j) (s (j + 1) - s j)) :
    ∃ W : (borelMooreChainComplex R M X).X n, ∀ j, IsOffChain (K j) (W - s j) := by
  classical
  have hstab : ∀ σ j, (singularSimplexImage X σ ∩ K j).Nonempty →
      ∀ k, j ≤ k → (s k).1 σ = (s j).1 σ := by
    intro σ j hσ k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [← ih]
      exact (hs k).eq_of_sub (hσ.mono (inter_subset_inter_right _ (K.subset hk)))
  have hex : ∀ σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌),
      ∃ j, (singularSimplexImage X σ ∩ K j).Nonempty := fun σ ↦ by
    obtain ⟨x, hx⟩ := nonempty_singularSimplexImage σ
    obtain ⟨j, hj⟩ := K.exists_mem x
    exact ⟨j, x, hx, hj⟩
  let wfun : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → M := fun σ ↦ (s (Nat.find (hex σ))).1 σ
  have hwfun : ∀ σ j, (singularSimplexImage X σ ∩ K j).Nonempty → wfun σ = (s j).1 σ :=
    fun σ j hσ ↦ (hstab σ _ (Nat.find_spec (hex σ)) _ (Nat.find_min' (hex σ) hσ)).symm
  have hlf : IsLocallyFiniteSet (singularSimplexImage X (n := op ⦋n⦌))
      (Function.support wfun) := by
    intro x
    obtain ⟨j, hj⟩ := K.exists_mem_nhds x
    obtain ⟨V, hV, hfin⟩ := (s j).2 x
    refine ⟨V ∩ K j, Filter.inter_mem hV hj, hfin.subset ?_⟩
    rintro σ ⟨hσ, y, hy, hyV, hyK⟩
    refine ⟨?_, y, hy, hyV⟩
    rw [Function.mem_support, ← hwfun σ j ⟨y, hy, hyK⟩]
    exact hσ
  refine ⟨⟨wfun, hlf⟩, fun j σ hσ ↦ ?_⟩
  change wfun σ - (s j).1 σ = 0
  rw [hwfun σ j hσ, sub_self]

section Exhaustion

variable [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]

/-- **Borel–Moore boundaries from relative boundaries.** On a weakly locally compact σ-compact
space, a locally finite `m`-chain `z` which, for every compact `K`, is a boundary modulo chains
off `K`, is the boundary of a locally finite chain, provided `H_{m+1}(X, X - K) = 0` for every
compact `K`. -/
theorem exists_d_eq_of_forall_isCompact {m : ℕ} (z : (borelMooreChainComplex R M X).X m)
    (hz : ∀ K : Set X, IsCompact K → ∃ w : (borelMooreChainComplex R M X).X (m + 1),
      IsOffChain K (z - ((borelMooreChainComplex R M X).d (m + 1) m).hom w))
    (hB : ∀ K : Set X, IsCompact K → RelVanishingBM X R M m K) :
    ∃ w : (borelMooreChainComplex R M X).X (m + 1),
      ((borelMooreChainComplex R M X).d (m + 1) m).hom w = z := by
  set D := ((borelMooreChainComplex R M X).d (m + 1) m).hom with hD
  set D' := ((borelMooreChainComplex R M X).d (m + 2) (m + 1)).hom with hD'
  have hDD : ∀ e, D (D' e) = 0 := fun e ↦ by
    rw [hD, hD', ← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
    rfl
  let K := CompactExhaustion.choice X
  have step : ∀ (j : ℕ) (w : (borelMooreChainComplex R M X).X (m + 1)),
      IsOffChain (K j) (z - D w) → ∃ w' : (borelMooreChainComplex R M X).X (m + 1),
        IsOffChain (K (j + 1)) (z - D w') ∧ IsOffChain (K j) (w' - w) := by
    intro j w hw
    obtain ⟨w', hw'⟩ := hz (K (j + 1)) (K.isCompact _)
    have hu : IsOffChain (K j) (D (w' - w)) := by
      have := hw.sub (hw'.mono (K.subset_succ j))
      rwa [sub_sub_sub_cancel_left, ← map_sub] at this
    obtain ⟨e, he⟩ := (hB (K j) (K.isCompact j)).exists_of_isOffChain_d (K.isCompact j) _ hu
    refine ⟨w' - D' e, ?_, ?_⟩
    · rwa [map_sub, hDD, sub_zero]
    · rwa [sub_right_comm]
  choose next hnext using step
  obtain ⟨w₀, hw₀⟩ := hz (K 0) (K.isCompact 0)
  let seq : (j : ℕ) →
      {w : (borelMooreChainComplex R M X).X (m + 1) // IsOffChain (K j) (z - D w)} :=
    fun j ↦ Nat.rec ⟨w₀, hw₀⟩ (fun j w ↦ ⟨next j w.1 w.2, (hnext j w.1 w.2).1⟩) j
  obtain ⟨W, hW⟩ := exists_isOffChain_sub_of_isOffChain_succ_sub K (fun j ↦ (seq j).1)
    fun j ↦ (hnext j (seq j).1 (seq j).2).2
  refine ⟨W, Subtype.ext (funext fun τ ↦ ?_)⟩
  obtain ⟨x, hx⟩ := nonempty_singularSimplexImage τ
  obtain ⟨j, hj⟩ := K.exists_mem x
  have hτ : (singularSimplexImage X τ ∩ K j).Nonempty := ⟨x, hx, hj⟩
  have h1 : IsOffChain (K j) (D W - D (seq j).1) := by
    rw [← map_sub]
    exact (hW j).d
  rw [h1.eq_of_sub hτ]
  exact ((seq j).2.eq_of_sub hτ).symm

/-- **Vanishing of Borel–Moore homology from local vanishing.** On a weakly locally compact
σ-compact space `X`, if `H_{m+1}(X, X - K) = 0` and `H_{m+2}(X, X - K) = 0` for every compact
`K` (on finite chains, `RelVanishingBM`), then `H_{m+1} X = 0`. -/
theorem isZero_of_relVanishingBM (m : ℕ)
    (h₁ : ∀ K : Set X, IsCompact K → RelVanishingBM X R M m K)
    (h₂ : ∀ K : Set X, IsCompact K → RelVanishingBM X R M (m + 1) K) :
    IsZero (borelMooreHomology R M X ((m + 1 : ℕ) : ℤ)) := by
  refine IsZero.of_iso ?_ (borelMooreHomologyIsoOfNat R M X (m + 1))
  refine HomologicalComplex.ExactAt.isZero_homology (K := borelMooreChainComplex R M X)
    (i := m + 1) ?_
  rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro z (hz : ((borelMooreChainComplex R M X).d (m + 1) m).hom z = 0)
  exact exists_d_eq_of_forall_isCompact (m := m + 1) z
    (fun K hK ↦ (h₁ K hK).exists_of_isOffChain_d hK z (hz ▸ IsOffChain.zero)) h₂

end Exhaustion

end borelMooreHomology

end MMP
