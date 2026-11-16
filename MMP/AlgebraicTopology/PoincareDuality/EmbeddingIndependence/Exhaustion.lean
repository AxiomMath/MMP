module

public import MMP.AlgebraicTopology.BorelMoore.FiniteChains

/-!
# Borel–Moore boundaries along a given exhaustion, with a Mittag-Leffler condition

A refinement of `MMP.borelMooreHomology.exists_d_eq_of_forall_isCompact`
(`BorelMoore/CompactExhaustion.lean`). There, the passage from local homology to Borel–Moore
homology asks `H_{m+1}(X, X - K) = 0` for **every** compact `K`. That fails in the degree just
below the dimension of a manifold (for `X = ℝⁿ`, `H_n(ℝⁿ, ℝⁿ - K) ≠ 0`), where the vanishing
`H_{n-1} ℝⁿ = 0` of Borel–Moore homology instead comes from the vanishing of a `lim¹`-term: the
maps `H_n(X, X - K_{j+1}) → H_n(X, X - K_j)` along a good exhaustion are **surjective**.

Here the exhaustion `K₀ ⊆ K₁ ⊆ ⋯` is given (compact, increasing, every point in the interior of
some `K_j`), and the hypothesis is the Mittag-Leffler condition `RelSurjBM m (K j) (K (j + 1))`:
every finite `(m + 1)`-chain `c` whose boundary is off `K_j` agrees modulo boundaries and chains
off `K_j` with a chain `e` whose boundary is off `K_{j+1}`. The vanishing `RelVanishingBM m K_j`
is the case `e = 0`.

This is a step of the proof of `lem_ext_c19_borel_moore_independent`:
the convex case of Poincaré duality needs `H_q ℝⁿ = 0` for `q < n`
(`PoincareDuality/EmbeddingIndependence/Euclidean.lean`).

## Main definitions

* `MMP.borelMooreHomology.RelSurjBM`: the Mittag-Leffler condition for `K ⊆ K'`.
* `MMP.SingularChain.RelSurj`: the same condition on finite singular chains.

## Main results

* `MMP.borelMooreHomology.exists_d_eq_of_exhaustion`: the lifting argument.
* `MMP.borelMooreHomology.isZero_of_exhaustion`: `H_{m+1} X = 0` from the
  vanishing of `H_{m+1}(X, X - K_j)` and the Mittag-Leffler condition in degree `m + 2`.
* `MMP.borelMooreHomology.relSurjBM_of_relSurj`: the condition on finite chains implies it on
  locally finite chains.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.F (the Milnor sequence).
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial

universe u

namespace MMP

namespace SingularChain

variable (R : Type*) [CommRing R] (Y : Type*) [TopologicalSpace Y]

/-- The Mittag-Leffler condition for `K ⊆ K'` on finite singular chains: every `(m + 1)`-chain
whose boundary lies in `Y - K` is, modulo boundaries and chains of `Y - K`, a chain whose boundary
lies in `Y - K'` (the map `H_{m+1}(Y, Y - K') → H_{m+1}(Y, Y - K)` is surjective). -/
def RelSurj (m : ℕ) (K K' : Set Y) : Prop :=
  ∀ c : Chain R Y (m + 1), bd R m c ∈ inside R m Kᶜ →
    ∃ e : Chain R Y (m + 1), ∃ w : Chain R Y (m + 2),
      bd R m e ∈ inside R m K'ᶜ ∧ c - e - bd R (m + 1) w ∈ inside R (m + 1) Kᶜ

variable {R Y}

/-- Relative vanishing is the Mittag-Leffler condition with `e = 0`. -/
lemma RelVanishing.relSurj {m : ℕ} {K : Set Y} (h : RelVanishing R Y m K) (K' : Set Y) :
    RelSurj R Y m K K' := fun c hc ↦ by
  obtain ⟨w, hw⟩ := h c hc
  exact ⟨0, w, by simp, by simpa using hw⟩

end SingularChain

namespace borelMooreHomology

open LocallyFiniteChain SingularChain

section general

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {X : TopCat.{u}}

variable (X) in
/-- The Mittag-Leffler condition for `K ⊆ K'` on locally finite chains: every finite
`(m + 1)`-chain whose boundary is off `K` is, modulo boundaries and chains off `K`, a chain whose
boundary is off `K'`. -/
def RelSurjBM (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (m : ℕ) (K K' : Set X) : Prop :=
  ∀ c : (borelMooreChainComplex R M X).X (m + 1), (Function.support c.1).Finite →
    IsOffChain K (((borelMooreChainComplex R M X).d (m + 1) m).hom c) →
    ∃ e : (borelMooreChainComplex R M X).X (m + 1),
      ∃ w : (borelMooreChainComplex R M X).X (m + 2),
        IsOffChain K' (((borelMooreChainComplex R M X).d (m + 1) m).hom e) ∧
          IsOffChain K (c - e - ((borelMooreChainComplex R M X).d (m + 2) (m + 1)).hom w)

/-- Relative vanishing is the Mittag-Leffler condition with `e = 0`. -/
lemma RelVanishingBM.relSurjBM {m : ℕ} {K : Set X} (h : RelVanishingBM X R M m K)
    (K' : Set X) : RelSurjBM X R M m K K' := fun c hc hdc ↦ by
  obtain ⟨w, hw⟩ := h c hc hdc
  exact ⟨0, w, by rw [map_zero]; exact IsOffChain.zero, by rwa [sub_zero]⟩

/-- For compact `K`, the Mittag-Leffler condition `RelSurjBM` applies to every locally finite
`(m + 1)`-chain whose boundary is off `K`, not only to finitely supported ones. -/
lemma RelSurjBM.exists_of_isOffChain_d {m : ℕ} {K K' : Set X} (hK : IsCompact K)
    (h : RelSurjBM X R M m K K') (c : (borelMooreChainComplex R M X).X (m + 1))
    (hc : IsOffChain K (((borelMooreChainComplex R M X).d (m + 1) m).hom c)) :
    ∃ e : (borelMooreChainComplex R M X).X (m + 1),
      ∃ w : (borelMooreChainComplex R M X).X (m + 2),
        IsOffChain K' (((borelMooreChainComplex R M X).d (m + 1) m).hom e) ∧
          IsOffChain K (c - e - ((borelMooreChainComplex R M X).d (m + 2) (m + 1)).hom w) := by
  set D := ((borelMooreChainComplex R M X).d (m + 1) m).hom
  have h1 : IsOffChain K (D (truncChain K c)) := by
    have := hc.sub (map_sub D c _ ▸ (isOffChain_sub_truncChain K c).d)
    rwa [sub_sub_cancel] at this
  obtain ⟨e, w, he, hw⟩ := h (truncChain K c) (finite_support_truncChain hK c) h1
  refine ⟨e, w, he, ?_⟩
  convert (isOffChain_sub_truncChain K c).add hw using 1
  abel

/-- One step of the lifting argument of `exists_d_eq_of_exhaustion`: under the Mittag-Leffler
condition for `K ⊆ K'`, a chain `w` with `z - ∂w` off `K` is corrected, modulo chains off `K`, to
a chain `w''` with `z - ∂w''` off `K'`. -/
lemma RelSurjBM.exists_isOffChain_sub_d {m : ℕ} {K K' : Set X} (hK : IsCompact K)
    (hKK' : K ⊆ K') (h : RelSurjBM X R M m K K') {z : (borelMooreChainComplex R M X).X m}
    {w w' : (borelMooreChainComplex R M X).X (m + 1)}
    (hw : IsOffChain K (z - ((borelMooreChainComplex R M X).d (m + 1) m).hom w))
    (hw' : IsOffChain K' (z - ((borelMooreChainComplex R M X).d (m + 1) m).hom w')) :
    ∃ w'' : (borelMooreChainComplex R M X).X (m + 1),
      IsOffChain K' (z - ((borelMooreChainComplex R M X).d (m + 1) m).hom w'') ∧
        IsOffChain K (w'' - w) := by
  set D := ((borelMooreChainComplex R M X).d (m + 1) m).hom with hD
  set D' := ((borelMooreChainComplex R M X).d (m + 2) (m + 1)).hom with hD'
  have hDD : ∀ e, D (D' e) = 0 := fun e ↦ by
    rw [hD, hD', ← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
    rfl
  have hu : IsOffChain K (D (w' - w)) := by
    have := hw.sub (hw'.mono hKK')
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  obtain ⟨e, e', he, he'⟩ := h.exists_of_isOffChain_d hK _ hu
  refine ⟨w' - e - D' e', ?_, ?_⟩
  · rw [map_sub, hDD, sub_zero, map_sub]
    convert hw'.add he using 1
    abel
  · rwa [show w' - e - D' e' - w = w' - w - e - D' e' by abel]

/-- **Borel–Moore boundaries along an exhaustion.** Let `K₀ ⊆ K₁ ⊆ ⋯` be compact sets such that
every point of `X` has some `K_j` as a neighbourhood. A locally finite `m`-chain `z` which, for
every `j`, is a boundary modulo chains off `K_j`, is the boundary of a locally finite chain,
provided the Mittag-Leffler condition `RelSurjBM m (K j) (K (j + 1))` holds for every `j`. -/
theorem exists_d_eq_of_exhaustion (K : ℕ → Set X) (hKc : ∀ j, IsCompact (K j))
    (hKm : Monotone K) (hKn : ∀ x, ∃ j, K j ∈ 𝓝 x) {m : ℕ}
    (z : (borelMooreChainComplex R M X).X m)
    (hz : ∀ j, ∃ w : (borelMooreChainComplex R M X).X (m + 1),
      IsOffChain (K j) (z - ((borelMooreChainComplex R M X).d (m + 1) m).hom w))
    (hML : ∀ j, RelSurjBM X R M m (K j) (K (j + 1))) :
    ∃ w : (borelMooreChainComplex R M X).X (m + 1),
      ((borelMooreChainComplex R M X).d (m + 1) m).hom w = z := by
  classical
  set D := ((borelMooreChainComplex R M X).d (m + 1) m).hom
  have step : ∀ (j : ℕ) (w : (borelMooreChainComplex R M X).X (m + 1)),
      IsOffChain (K j) (z - D w) → ∃ w' : (borelMooreChainComplex R M X).X (m + 1),
        IsOffChain (K (j + 1)) (z - D w') ∧ IsOffChain (K j) (w' - w) := fun j _ hw ↦
    (hML j).exists_isOffChain_sub_d (hKc j) (hKm (Nat.le_succ j)) hw (hz (j + 1)).choose_spec
  choose next hnext using step
  obtain ⟨w₀, hw₀⟩ := hz 0
  let seq : (j : ℕ) →
      {w : (borelMooreChainComplex R M X).X (m + 1) // IsOffChain (K j) (z - D w)} :=
    fun j ↦ Nat.rec ⟨w₀, hw₀⟩ (fun j w ↦ ⟨next j w.1 w.2, (hnext j w.1 w.2).1⟩) j
  have hstab : ∀ σ j, (singularSimplexImage X σ ∩ K j).Nonempty →
      ∀ k, j ≤ k → (seq k).1.1 σ = (seq j).1.1 σ := by
    intro σ j hσ k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [← ih]
      exact (hnext k (seq k).1 (seq k).2).2.eq_of_sub
        (hσ.mono (inter_subset_inter_right _ (hKm hk)))
  have hex : ∀ σ : (TopCat.toSSet.obj X).obj (op ⦋m + 1⦌),
      ∃ j, (singularSimplexImage X σ ∩ K j).Nonempty := fun σ ↦ by
    obtain ⟨x, hx⟩ := nonempty_singularSimplexImage σ
    obtain ⟨j, hj⟩ := hKn x
    exact ⟨j, x, hx, mem_of_mem_nhds hj⟩
  let wfun : (TopCat.toSSet.obj X).obj (op ⦋m + 1⦌) → M := fun σ ↦ (seq (Nat.find (hex σ))).1.1 σ
  have hwfun : ∀ σ j, (singularSimplexImage X σ ∩ K j).Nonempty → wfun σ = (seq j).1.1 σ :=
    fun σ _ hσ ↦ (hstab σ _ (Nat.find_spec (hex σ)) _ (Nat.find_min' (hex σ) hσ)).symm
  have hlf : IsLocallyFiniteSet (singularSimplexImage X (n := op ⦋m + 1⦌))
      (Function.support wfun) := by
    intro x
    obtain ⟨j, hj⟩ := hKn x
    obtain ⟨V, hV, hfin⟩ := (seq j).1.2 x
    refine ⟨V ∩ K j, Filter.inter_mem hV hj, hfin.subset ?_⟩
    rintro σ ⟨hσ, y, hy, hyV, hyK⟩
    refine ⟨?_, y, hy, hyV⟩
    rwa [Function.mem_support, ← hwfun σ j ⟨y, hy, hyK⟩]
  let W : (borelMooreChainComplex R M X).X (m + 1) := ⟨wfun, hlf⟩
  refine ⟨W, Subtype.ext (funext fun τ ↦ ?_)⟩
  obtain ⟨x, hx⟩ := nonempty_singularSimplexImage τ
  obtain ⟨j, hj⟩ := hKn x
  have hτ : (singularSimplexImage X τ ∩ K j).Nonempty := ⟨x, hx, mem_of_mem_nhds hj⟩
  have hW : IsOffChain (K j) (W - (seq j).1) := fun σ hσ ↦ by
    change wfun σ - (seq j).1.1 σ = 0
    rw [hwfun σ j hσ, sub_self]
  rw [(map_sub D W _ ▸ hW.d : IsOffChain (K j) (D W - D (seq j).1)).eq_of_sub hτ]
  exact ((seq j).2.eq_of_sub hτ).symm

/-- **Vanishing of Borel–Moore homology along an exhaustion.** For an exhaustion
`K₀ ⊆ K₁ ⊆ ⋯` of `X` by compact sets as in `exists_d_eq_of_exhaustion`, if
`H_{m+1}(X, X - K_j) = 0` for every `j` and the maps
`H_{m+2}(X, X - K_{j+1}) → H_{m+2}(X, X - K_j)` are surjective (`RelSurjBM`), then
`H_{m+1} X = 0`. -/
theorem isZero_of_exhaustion (K : ℕ → Set X) (hKc : ∀ j, IsCompact (K j))
    (hKm : Monotone K) (hKn : ∀ x, ∃ j, K j ∈ 𝓝 x) (m : ℕ)
    (h₁ : ∀ j, RelVanishingBM X R M m (K j))
    (h₂ : ∀ j, RelSurjBM X R M (m + 1) (K j) (K (j + 1))) :
    IsZero (borelMooreHomology R M X ((m + 1 : ℕ) : ℤ)) := by
  refine IsZero.of_iso ?_ (borelMooreHomologyIsoOfNat R M X (m + 1))
  refine HomologicalComplex.ExactAt.isZero_homology (K := borelMooreChainComplex R M X)
    (i := m + 1) ?_
  rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro z hz
  have hz' : ((borelMooreChainComplex R M X).d (m + 1) m).hom z = 0 := hz
  exact exists_d_eq_of_exhaustion (m := m + 1) K hKc hKm hKn z
    (fun j ↦ (h₁ j).exists_of_isOffChain_d (hKc j) z (by rw [hz']; exact IsOffChain.zero)) h₂

end general

section finite

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- The Mittag-Leffler condition on finite singular chains gives it for locally finite chains. -/
lemma relSurjBM_of_relSurj {m : ℕ} {K K' : Set X} (h : RelSurj R X m K K') :
    RelSurjBM X R (ModuleCat.of R R) m K K' := by
  intro c hc hdc
  set f := toFinsupp c hc
  have hcf : ofFinsupp f = c := ofFinsupp_toFinsupp c hc
  rw [← hcf, d_ofFinsupp, isOffChain_ofFinsupp_iff] at hdc
  obtain ⟨e, w, he, hw⟩ := h f hdc
  refine ⟨ofFinsupp e, ofFinsupp w, ?_, ?_⟩
  · rwa [d_ofFinsupp, isOffChain_ofFinsupp_iff]
  · rwa [d_ofFinsupp, ← hcf, ← ofFinsupp_sub, ← ofFinsupp_sub, isOffChain_ofFinsupp_iff]

end finite

end borelMooreHomology

end MMP
