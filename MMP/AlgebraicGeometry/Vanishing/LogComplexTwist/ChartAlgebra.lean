module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.LocalExact
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Construction

/-!
# The algebra of a logarithmic chart along one component

Let `Λ` be a ring of forms over a commutative ring `R` of functions, and `θ₁, …, θₙ` square-zero,
pairwise anticommuting elements of `Λ` (the logarithmic coordinate forms of a chart), with wedges
`θ_K = θ_{k₁} ⋯ θ_{k_q}` for `K = {k₁ < ⋯ < k_q}` linearly independent over `R`. Fix an index
`i₀` (the coordinate of a component `E` of the boundary) and put `θ = θ_{i₀}`. The `q`-forms
`∑_K c_K θ_K` with regular coefficients split as `α + θ β`, with `α` and `β` combinations of the
`θ_K` with `i₀ ∉ K`; by independence the `θ`-part `β` is determined, and a form `α + θ β` is
divisible by a function `t` only if `β` is.

A differential `d` with `d(c θ_K) = D(c) θ_K` for an additive `D`, all of whose values are
`a₀ + t a₁ θ` with `a₀` free of `θ`, then gives the data `MMP.LcBpf.ResidueData` of the residue
argument.

## Main definitions

* `MMP.LcBpf.ChartAlgebra.θK`: the wedge `θ_K`.
* `MMP.LcBpf.ChartAlgebra.F`: the combinations of the `θ_K`, `|K| = q`.
* `MMP.LcBpf.ChartAlgebra.L`: the combinations of the `θ_K`, `|K| = q`, `i₀ ∉ K`.
* `MMP.LcBpf.ChartAlgebra.L'`: the combinations of the `θ_K`, `|K| = q`, `i₀ ∈ K`.
* `MMP.LcBpf.ChartAlgebra.combo`: the combination `∑_K c_K θ_K` with given coefficients.
* `MMP.LcBpf.ChartAlgebra.toResidueData`: the residue data of a chart.

## Main results

* `MMP.LcBpf.ChartAlgebra.exists_eq_add_θ_mul`: a combination of degree `q + 1` is `α + θ β`.
* `MMP.LcBpf.ChartAlgebra.add_θ_mul_mem_F`: conversely `α + θ β` is a combination.
* `MMP.LcBpf.ChartAlgebra.eq_smul_of_add_θ_mul_eq_smul`: divisibility of the `θ`-part.
-/

@[expose] public section

namespace MMP.LcBpf

open MMP.FourfoldProofs.FractionalLogComplexProof

namespace ChartAlgebra

variable {R Λ : Type*} [CommRing R] [Ring Λ] [Algebra R Λ] {n : ℕ} (θ : Fin n → Λ)

/-- The wedge `θ_K` of the forms `θᵢ`, `i ∈ K`, in increasing order. -/
def θK (K : Finset (Fin n)) : Λ := ((K.sort (· ≤ ·)).map θ).prod

/-- The combinations `∑_K c_K θ_K` of the wedges of `q` of the forms `θᵢ`. -/
def F (q : ℕ) : Submodule R Λ := Submodule.span R (θK θ '' {K | K.card = q})

/-- The combinations `∑_K c_K θ_K` of the wedges of `q` of the forms `θᵢ`, `i ≠ i₀`. -/
def L (i₀ : Fin n) (q : ℕ) : Submodule R Λ :=
  Submodule.span R (θK θ '' {K | K.card = q ∧ i₀ ∉ K})

/-- The combinations of the wedges `θ_K`, `|K| = q`, with `i₀ ∈ K`. -/
def L' (i₀ : Fin n) (q : ℕ) : Submodule R Λ :=
  Submodule.span R (θK θ '' {K | K.card = q ∧ i₀ ∈ K})

/-- The wedge of no forms is `1`. -/
@[simp]
theorem θK_empty : θK θ ∅ = 1 := by simp [θK]

/-- The wedge `θ_{i}` of one form is `θᵢ`. -/
@[simp]
theorem θK_singleton (i : Fin n) : θK θ {i} = θ i := by simp [θK]

/-- Every combination of the wedges `θ_K` with `i₀ ∉ K` lies in `F θ q`. -/
theorem L_le_F (i₀ : Fin n) (q : ℕ) : L (R := R) θ i₀ q ≤ F θ q :=
  Submodule.span_mono (Set.image_mono fun _ hK => hK.1)

/-- Every combination of the wedges `θ_K` with `i₀ ∈ K` lies in `F θ q`. -/
theorem L'_le_F (i₀ : Fin n) (q : ℕ) : L' (R := R) θ i₀ q ≤ F θ q :=
  Submodule.span_mono (Set.image_mono fun _ hK => hK.1)

/-- The wedge `θ_K` with `|K| = q` and `i₀ ∉ K` lies in `L θ i₀ q`. -/
theorem θK_mem_L {i₀ : Fin n} {q : ℕ} {K : Finset (Fin n)} (hK : K.card = q) (hi : i₀ ∉ K) :
    θK θ K ∈ L (R := R) θ i₀ q :=
  Submodule.subset_span ⟨K, ⟨hK, hi⟩, rfl⟩

/-- The wedge `θ_K` with `|K| = q` and `i₀ ∈ K` lies in `L' θ i₀ q`. -/
theorem θK_mem_L' {i₀ : Fin n} {q : ℕ} {K : Finset (Fin n)} (hK : K.card = q) (hi : i₀ ∈ K) :
    θK θ K ∈ L' (R := R) θ i₀ q :=
  Submodule.subset_span ⟨K, ⟨hK, hi⟩, rfl⟩

/-- The wedge `θ_K` with `|K| = q` lies in `F θ q`. -/
theorem θK_mem_F {q : ℕ} {K : Finset (Fin n)} (hK : K.card = q) : θK θ K ∈ F (R := R) θ q :=
  Submodule.subset_span ⟨K, hK, rfl⟩

/-- In degree `0`, `F θ 0` equals `L θ i₀ 0`. -/
theorem F_zero_eq_L (i₀ : Fin n) : F (R := R) θ 0 = L θ i₀ 0 := by
  refine le_antisymm (Submodule.span_le.2 ?_) (L_le_F θ i₀ 0)
  rintro _ ⟨K, hK, rfl⟩
  exact θK_mem_L θ hK (by simp [Finset.card_eq_zero.mp hK])

variable {θ}

section Signs

variable (hsq : ∀ i, θ i * θ i = 0) (hac : ∀ i j, θ i * θ j = -(θ j * θ i))

include hac

/-- `θᵢ θ_K = ± θ_{K ∪ {i}}` for `i ∉ K`. -/
theorem exists_sign_θ_mul_θK {i : Fin n} {K : Finset (Fin n)} (hi : i ∉ K) :
    ∃ ε : R, (ε = 1 ∨ ε = -1) ∧ θ i * θK θ K = ε • θK θ (insert i K) := by
  have hnd : (i :: K.sort (· ≤ ·)).Nodup :=
    List.nodup_cons.2 ⟨by simpa using hi, Finset.sort_nodup _ _⟩
  have hp : (i :: K.sort (· ≤ ·)).Perm ((insert i K).sort (· ≤ ·)) :=
    List.perm_of_nodup_nodup_toFinset_eq hnd (Finset.sort_nodup _ _) (by ext; simp)
  have e : θ i * θK θ K = ((i :: K.sort (· ≤ ·)).map θ).prod := by
    simp [θK]
  rcases prod_map_perm θ hac hp with h | h
  · exact ⟨1, Or.inl rfl, by rw [e, h, one_smul]; rfl⟩
  · exact ⟨-1, Or.inr rfl, by rw [e, h, neg_one_smul]; rfl⟩

include hsq in
/-- `θᵢ θ_K = 0` for `i ∈ K`. -/
theorem θ_mul_θK_eq_zero_of_mem {i : Fin n} {K : Finset (Fin n)} (hi : i ∈ K) :
    θ i * θK θ K = 0 := by
  have hnd : ¬ (i :: K.sort (· ≤ ·)).Nodup := by
    rw [List.nodup_cons]
    exact fun h => h.1 (by simpa using hi)
  have e : θ i * θK θ K = ((i :: K.sort (· ≤ ·)).map θ).prod := by
    simp [θK]
  rw [e]
  exact prod_map_eq_zero_of_not_nodup θ hsq hac hnd

include hsq in
/-- `θᵢ` maps the combinations of degree `q` to those of degree `q + 1`. -/
theorem θ_mul_mem_F (i : Fin n) {q : ℕ} {x : Λ} (hx : x ∈ F (R := R) θ q) :
    θ i * x ∈ F (R := R) θ (q + 1) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, hK, rfl⟩ := hx
    by_cases hi : i ∈ K
    · simp [θ_mul_θK_eq_zero_of_mem hsq hac hi]
    · obtain ⟨ε, -, he⟩ := exists_sign_θ_mul_θK (R := R) hac hi
      rw [he]
      refine Submodule.smul_mem _ _ (θK_mem_F θ ?_)
      rw [Finset.card_insert_of_notMem hi, hK]
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using add_mem hx hy
  | smul r x _ hx => simpa only [mul_smul_comm] using Submodule.smul_mem _ r hx

include hsq in
/-- `θᵢ`, `i ≠ i₀`, maps the `θ`-free combinations of degree `q` to those of degree `q + 1`. -/
theorem θ_mul_mem_L {i₀ i : Fin n} (hi₀ : i ≠ i₀) {q : ℕ} {x : Λ} (hx : x ∈ L (R := R) θ i₀ q) :
    θ i * x ∈ L (R := R) θ i₀ (q + 1) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, ⟨hK, hK₀⟩, rfl⟩ := hx
    by_cases hi : i ∈ K
    · simp [θ_mul_θK_eq_zero_of_mem hsq hac hi]
    · obtain ⟨ε, -, he⟩ := exists_sign_θ_mul_θK (R := R) hac hi
      rw [he]
      refine Submodule.smul_mem _ _ (θK_mem_L θ ?_ ?_)
      · rw [Finset.card_insert_of_notMem hi, hK]
      · rw [Finset.mem_insert]
        rintro (h | h)
        · exact hi₀ h.symm
        · exact hK₀ h
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using add_mem hx hy
  | smul r x _ hx => simpa only [mul_smul_comm] using Submodule.smul_mem _ r hx

/-- `θ = θ_{i₀}` maps the `θ`-free combinations to combinations of wedges containing `i₀`. -/
theorem θ_mul_mem_L' {i₀ : Fin n} {q : ℕ} {x : Λ} (hx : x ∈ L (R := R) θ i₀ q) :
    θ i₀ * x ∈ L' (R := R) θ i₀ (q + 1) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, ⟨hK, hK₀⟩, rfl⟩ := hx
    obtain ⟨ε, -, he⟩ := exists_sign_θ_mul_θK (R := R) hac hK₀
    rw [he]
    refine Submodule.smul_mem _ _ (θK_mem_L' θ ?_ (Finset.mem_insert_self _ _))
    rw [Finset.card_insert_of_notMem hK₀, hK]
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using add_mem hx hy
  | smul r x _ hx => simpa only [mul_smul_comm] using Submodule.smul_mem _ r hx

include hsq in
/-- A `θ`-free `1`-form times a `θ`-free `q`-form is `θ`-free. -/
theorem mul_mem_L {i₀ : Fin n} {q : ℕ} {ξ x : Λ} (hξ : ξ ∈ L (R := R) θ i₀ 1)
    (hx : x ∈ L (R := R) θ i₀ q) : ξ * x ∈ L (R := R) θ i₀ (q + 1) := by
  classical
  induction hξ using Submodule.span_induction with
  | mem ξ hξ =>
    obtain ⟨K, ⟨hK, hK₀⟩, rfl⟩ := hξ
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hK
    rw [θK_singleton]
    exact θ_mul_mem_L hsq hac (fun h => hK₀ (by simp [h])) hx
  | zero => simp
  | add x y _ _ hx hy => simpa only [add_mul] using add_mem hx hy
  | smul r x _ hx => simpa only [smul_mul_assoc] using Submodule.smul_mem _ r hx

/-- `θ` anticommutes with the `θ`-free `1`-forms. -/
theorem θ_mul_eq_neg_of_mem_L {i₀ : Fin n} {ξ : Λ} (hξ : ξ ∈ L (R := R) θ i₀ 1) :
    θ i₀ * ξ = -(ξ * θ i₀) := by
  classical
  induction hξ using Submodule.span_induction with
  | mem ξ hξ =>
    obtain ⟨K, ⟨hK, -⟩, rfl⟩ := hξ
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hK
    rw [θK_singleton]
    exact hac i₀ i
  | zero => rw [zero_mul, mul_zero, neg_zero]
  | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy, neg_add]
  | smul r x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx, smul_neg]

/-- **The `θ`-splitting of a wedge.** A wedge `θ_K` with `|K| = q + 1` is `α + θ β` with
`α ∈ L θ i₀ (q + 1)` and `β ∈ L θ i₀ q`. -/
theorem exists_θK_eq_add_θ_mul (i₀ : Fin n) {q : ℕ} {K : Finset (Fin n)}
    (hK : K.card = q + 1) :
    ∃ α ∈ L (R := R) θ i₀ (q + 1), ∃ β ∈ L (R := R) θ i₀ q, θK θ K = α + θ i₀ * β := by
  classical
  by_cases hi : i₀ ∈ K
  · have hK' : i₀ ∉ K.erase i₀ := Finset.notMem_erase _ _
    have hc : (K.erase i₀).card = q := by
      rw [Finset.card_erase_of_mem hi, hK, Nat.add_sub_cancel]
    obtain ⟨ε, hε, he⟩ := exists_sign_θ_mul_θK (R := R) hac hK'
    rw [Finset.insert_erase hi] at he
    refine ⟨0, zero_mem _, ε • θK θ (K.erase i₀),
      Submodule.smul_mem _ _ (θK_mem_L θ hc hK'), ?_⟩
    rw [zero_add, mul_smul_comm, he, smul_smul]
    rcases hε with rfl | rfl <;> simp
  · exact ⟨θK θ K, θK_mem_L θ hK hi, 0, zero_mem _, by simp⟩

/-- **The `θ`-splitting.** A combination of degree `q + 1` is `α + θ β` with `α`, `β` free of
`θ`. -/
theorem exists_eq_add_θ_mul (i₀ : Fin n) {q : ℕ} {x : Λ} (hx : x ∈ F (R := R) θ (q + 1)) :
    ∃ α ∈ L (R := R) θ i₀ (q + 1), ∃ β ∈ L (R := R) θ i₀ q, x = α + θ i₀ * β := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, hK, rfl⟩ := hx
    exact exists_θK_eq_add_θ_mul hac i₀ hK
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨α, hα, β, hβ, rfl⟩ := hx
    obtain ⟨α', hα', β', hβ', rfl⟩ := hy
    exact ⟨α + α', add_mem hα hα', β + β', add_mem hβ hβ', by rw [mul_add]; abel⟩
  | smul r x _ hx =>
    obtain ⟨α, hα, β, hβ, rfl⟩ := hx
    exact ⟨r • α, Submodule.smul_mem _ _ hα, r • β, Submodule.smul_mem _ _ hβ,
      by rw [smul_add, mul_smul_comm]⟩

/-- Conversely, `α + θ β` is a combination. -/
theorem add_θ_mul_mem_F {i₀ : Fin n} {q : ℕ} {α β : Λ} (hα : α ∈ L (R := R) θ i₀ (q + 1))
    (hβ : β ∈ L (R := R) θ i₀ q) : α + θ i₀ * β ∈ F (R := R) θ (q + 1) :=
  add_mem (L_le_F θ i₀ _ hα) (L'_le_F θ i₀ _ (θ_mul_mem_L' hac hβ))

end Signs

section Independence

/-- The combination `∑_K c_K θ_K` of the wedges of `q` of the `θᵢ`. -/
def combo (θ : Fin n → Λ) (q : ℕ) (c : {K : Finset (Fin n) // K.card = q} → R) : Λ :=
  ∑ K, c K • θK θ K.1

/-- `combo θ q` sends a difference of coefficient families to the difference of combinations. -/
theorem combo_sub (q : ℕ) (a b : {K : Finset (Fin n) // K.card = q} → R) :
    combo θ q (a - b) = combo θ q a - combo θ q b := by
  simp [combo, sub_smul, Finset.sum_sub_distrib]

/-- `combo θ q` commutes with finite `R`-linear combinations of coefficient families. -/
theorem combo_sum_smul {ι : Type*} (s : Finset ι) (q : ℕ) (r : ι → R)
    (a : ι → {K : Finset (Fin n) // K.card = q} → R) :
    combo θ q (∑ i ∈ s, r i • a i) = ∑ i ∈ s, r i • combo θ q (a i) := by
  simp only [combo, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul,
    Finset.smul_sum]
  exact Finset.sum_comm

/-- The combination with coefficient `1` at `K` and `0` elsewhere is `θ_K`. -/
theorem combo_single {q : ℕ} (K : {K : Finset (Fin n) // K.card = q}) :
    combo θ q (Pi.single K (1 : R)) = θK θ K.1 := by
  classical
  simp [combo, Pi.single_apply]

variable (P : Finset (Fin n) → Prop) in
/-- An element of the span of the wedges `θ_K`, `|K| = q`, with `K` satisfying `P`, is
`combo θ q c` for coefficients `c` vanishing off `P`. -/
theorem exists_combo_of_mem_span {q : ℕ} {x : Λ}
    (hx : x ∈ Submodule.span R (θK θ '' {K | K.card = q ∧ P K})) :
    ∃ c : {K : Finset (Fin n) // K.card = q} → R, (∀ K, ¬ P K.1 → c K = 0) ∧ combo θ q c = x := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, ⟨hK, hP⟩, rfl⟩ := hx
    refine ⟨Pi.single ⟨K, hK⟩ 1, fun K' hK' => ?_, ?_⟩
    · exact Pi.single_eq_of_ne (by rintro rfl; exact hK' hP) _
    · exact combo_single _
  | zero => exact ⟨0, fun _ _ => rfl, by simp [combo]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨c', hc', rfl⟩ := hy
    exact ⟨c + c', fun K hK => by simp [hc K hK, hc' K hK],
      by simp [combo, add_smul, Finset.sum_add_distrib]⟩
  | smul r x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨r • c, fun K hK => by simp [hc K hK], by simp [combo, Finset.smul_sum, smul_smul]⟩

/-- An element lies in `F θ q` if and only if it is `combo θ q c` for some coefficients `c`. -/
theorem mem_F_iff {q : ℕ} {x : Λ} :
    x ∈ F (R := R) θ q ↔ ∃ c : {K : Finset (Fin n) // K.card = q} → R, combo θ q c = x := by
  rw [F, Set.image_eq_range, Submodule.mem_span_range_iff_exists_fun]; rfl

/-- Reindexing a sum over the `q`-sets avoiding `i₀` by `K ↦ K ∪ {i₀}`. -/
theorem sum_insert_eq_sum_erase {M : Type*} [AddCommMonoid M] (i₀ : Fin n) (q : ℕ)
    (g : Finset (Fin n) → Finset (Fin n) → M) :
    ∑ K ∈ Finset.univ.filter (fun K : Finset (Fin n) => K.card = q ∧ i₀ ∉ K), g K (insert i₀ K) =
      ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => J.card = q + 1 ∧ i₀ ∈ J),
        g (J.erase i₀) J := by
  refine Finset.sum_nbij' (fun K => insert i₀ K) (fun J => J.erase i₀) ?_ ?_ ?_ ?_ ?_
  · intro K hK
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK ⊢
    exact ⟨by rw [Finset.card_insert_of_notMem hK.2, hK.1], Finset.mem_insert_self _ _⟩
  · intro J hJ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ ⊢
    exact ⟨by rw [Finset.card_erase_of_mem hJ.2, hJ.1, Nat.add_sub_cancel],
      Finset.notMem_erase _ _⟩
  · intro K hK
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK
    exact Finset.erase_insert hK.2
  · intro J hJ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ
    exact Finset.insert_erase hJ.2
  · intro K hK
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK
    rw [Finset.erase_insert hK.2]

/-- A sum over the wedges `θ_J`, `|J| = q`, `i₀ ∈ J`, as a combination. -/
theorem sum_filter_mem_smul_θK_eq_combo (i₀ : Fin n) (q : ℕ) (f : Finset (Fin n) → R) :
    ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => J.card = q ∧ i₀ ∈ J), f J • θK θ J =
      combo θ q (fun J => if i₀ ∈ J.1 then f J.1 else 0) := by
  unfold combo
  rw [← Finset.sum_subtype (p := fun J : Finset (Fin n) => J.card = q)
    (Finset.univ.filter fun J : Finset (Fin n) => J.card = q)
    (fun J => by simp) (fun J => (if i₀ ∈ J then f J else 0) • θK θ J), Finset.sum_filter,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun J _ => ?_
  by_cases hJ : J.card = q
  · by_cases hi : i₀ ∈ J <;> simp [hJ, hi]
  · simp [hJ]

variable (hind : ∀ (q : ℕ) (c : {K : Finset (Fin n) // K.card = q} → R), combo θ q c = 0 → c = 0)

include hind

/-- The `θ`-free combinations and the combinations of wedges containing `i₀` meet in `0`. -/
theorem eq_zero_of_mem_L_of_mem_L' {i₀ : Fin n} {q : ℕ} {x : Λ} (hx : x ∈ L (R := R) θ i₀ q)
    (hx' : x ∈ L' (R := R) θ i₀ q) : x = 0 := by
  classical
  obtain ⟨c, hc, rfl⟩ := exists_combo_of_mem_span (fun K => i₀ ∉ K) hx
  obtain ⟨c', hc', e⟩ := exists_combo_of_mem_span (fun K => i₀ ∈ K) hx'
  have hcc : c = c' := (sub_eq_zero.mp (hind q _ (by rw [combo_sub, e, sub_self]))).symm
  have : c = 0 := funext fun K => by
    by_cases h : i₀ ∈ K.1
    · exact hc K (not_not.mpr h)
    · rw [hcc]
      exact hc' K h
  simp [combo, this]

/-- `θ = θ_{i₀}` is injective on the `θ`-free combinations. -/
theorem eq_zero_of_θ_mul_eq_zero (hac : ∀ i j, θ i * θ j = -(θ j * θ i)) {i₀ : Fin n} {q : ℕ}
    {x : Λ} (hx : x ∈ L (R := R) θ i₀ q) (h : θ i₀ * x = 0) : x = 0 := by
  classical
  obtain ⟨c, hc, rfl⟩ := exists_combo_of_mem_span (fun K => i₀ ∉ K) hx
  let c' : Finset (Fin n) → R := fun K => if hK : K.card = q then c ⟨K, hK⟩ else 0
  have hsgn : ∀ K : Finset (Fin n), ∃ ε : R, (ε = 1 ∨ ε = -1) ∧
      (i₀ ∉ K → θ i₀ * θK θ K = ε • θK θ (insert i₀ K)) := fun K => by
    by_cases hK : i₀ ∈ K
    · exact ⟨1, Or.inl rfl, fun h => absurd hK h⟩
    · obtain ⟨ε, hε, he⟩ := exists_sign_θ_mul_θK (R := R) hac hK
      exact ⟨ε, hε, fun _ => he⟩
  choose ε hε he using hsgn
  let e : {J : Finset (Fin n) // J.card = q + 1} → R := fun J =>
    if i₀ ∈ J.1 then c' (J.1.erase i₀) * ε (J.1.erase i₀) else 0
  have hsum1 : θ i₀ * combo θ q c =
      ∑ K ∈ Finset.univ.filter (fun K : Finset (Fin n) => K.card = q ∧ i₀ ∉ K),
        (c' K * ε K) • θK θ (insert i₀ K) := by
    unfold combo
    rw [Finset.mul_sum]
    have e1 : ∑ K : {K : Finset (Fin n) // K.card = q}, θ i₀ * (c K • θK θ K.1) =
        ∑ K ∈ Finset.univ.filter (fun K : Finset (Fin n) => K.card = q),
          θ i₀ * (c' K • θK θ K) := by
      rw [Finset.sum_subtype (p := fun K : Finset (Fin n) => K.card = q)
        (Finset.univ.filter fun K : Finset (Fin n) => K.card = q)
        (fun K => by simp) (fun K => θ i₀ * (c' K • θK θ K))]
      refine Finset.sum_congr rfl fun K _ => ?_
      simp only [c', dite_eq_left K.2]
    rw [e1, ← Finset.sum_filter_of_ne (p := fun K => i₀ ∉ K), Finset.filter_filter]
    · refine Finset.sum_congr rfl fun K hK => ?_
      have hK' := (Finset.mem_filter.mp hK).2
      rw [mul_smul_comm, he K hK'.2, smul_smul, mul_comm]
    · intro K hK hne hi
      have hK' := (Finset.mem_filter.mp hK).2
      have : c' K = 0 := by
        simp only [c', dite_eq_left hK']
        exact hc ⟨K, hK'⟩ (not_not.mpr hi)
      exact hne (by rw [this, zero_smul, mul_zero])
  have hsum2 := sum_insert_eq_sum_erase (M := Λ) i₀ q fun K J => (c' K * ε K) • θK θ J
  have hsum3 := sum_filter_mem_smul_θK_eq_combo (θ := θ) i₀ (q + 1)
    fun J => c' (J.erase i₀) * ε (J.erase i₀)
  have he0 := hind (q + 1) e ((hsum1.trans (hsum2.trans hsum3)).symm.trans h)
  have hc0 : c = 0 := funext fun K => by
    by_cases hK : i₀ ∈ K.1
    · exact hc K (not_not.mpr hK)
    · have h1 := congrFun he0 ⟨insert i₀ K.1, by rw [Finset.card_insert_of_notMem hK, K.2]⟩
      simp only [e, Finset.mem_insert_self, ite_true, Finset.erase_insert hK, Pi.zero_apply,
        c', dite_eq_left K.2] at h1
      rcases hε K.1 with h2 | h2 <;> rw [h2] at h1 <;> simpa using h1
  simp [combo, hc0]

/-- **Divisibility of the `θ`-part.** If `α + θ β = t (α' + θ β')` with all four free of `θ`,
then `β = t β'`. -/
theorem eq_smul_of_add_θ_mul_eq_smul (hac : ∀ i j, θ i * θ j = -(θ j * θ i)) {i₀ : Fin n} {q : ℕ}
    (t : R) {a b a' b' : Λ} (ha : a ∈ L (R := R) θ i₀ (q + 1)) (hb : b ∈ L (R := R) θ i₀ q)
    (ha' : a' ∈ L (R := R) θ i₀ (q + 1)) (hb' : b' ∈ L (R := R) θ i₀ q)
    (h : a + θ i₀ * b = t • (a' + θ i₀ * b')) : b = t • b' := by
  have hmem : b - t • b' ∈ L (R := R) θ i₀ q := sub_mem hb (Submodule.smul_mem _ _ hb')
  have e : θ i₀ * (b - t • b') = t • a' - a := by
    rw [mul_sub, mul_smul_comm]
    rw [smul_add] at h
    linear_combination (norm := abel) h
  have h1 : θ i₀ * (b - t • b') = 0 :=
    eq_zero_of_mem_L_of_mem_L' hind (e ▸ sub_mem (Submodule.smul_mem _ _ ha') ha)
      (θ_mul_mem_L' hac hmem)
  exact sub_eq_zero.mp (eq_zero_of_θ_mul_eq_zero hind hac hmem h1)

end Independence

section Residue

variable (hsq : ∀ i, θ i * θ i = 0) (hac : ∀ i j, θ i * θ j = -(θ j * θ i))
  (hind : ∀ (q : ℕ) (c : {K : Finset (Fin n) // K.card = q} → R), combo θ q c = 0 → c = 0)
  (i₀ : Fin n) (t : R) (d : ℕ → Λ →+ Λ) (Dr : R →+ Λ)
  (hdK : ∀ (q : ℕ) (c : R) (K : Finset (Fin n)), K.card = q → d q (c • θK θ K) = Dr c * θK θ K)
  (hD : ∀ c, ∃ a₀ ∈ L (R := R) θ i₀ 1, ∃ a₁ : R, Dr c = a₀ + (t * a₁) • θ i₀)
  (hθD : ∀ c, θ i₀ * Dr c = -(Dr c * θ i₀))

include hsq hac hdK hD in
/-- For `a ∈ L θ i₀ q`, the differential `d q a` is `a₀ + t (θ a₁)` with
`a₀ ∈ L θ i₀ (q + 1)` and `a₁ ∈ L θ i₀ q`. -/
theorem d_mem_of_mem_L {q : ℕ} {a : Λ} (ha : a ∈ L (R := R) θ i₀ q) :
    ∃ a₀ ∈ L (R := R) θ i₀ (q + 1), ∃ a₁ ∈ L (R := R) θ i₀ q, d q a = a₀ + t • (θ i₀ * a₁) := by
  classical
  obtain ⟨c, hc, rfl⟩ := exists_combo_of_mem_span (fun K => i₀ ∉ K) ha
  unfold combo
  rw [map_sum]
  refine Finset.sum_induction _ (fun z => ∃ a₀ ∈ L (R := R) θ i₀ (q + 1),
    ∃ a₁ ∈ L (R := R) θ i₀ q, z = a₀ + t • (θ i₀ * a₁)) ?_ ?_ fun K _ => ?_
  · rintro _ _ ⟨a₀, ha₀, a₁, ha₁, rfl⟩ ⟨b₀, hb₀, b₁, hb₁, rfl⟩
    exact ⟨a₀ + b₀, add_mem ha₀ hb₀, a₁ + b₁, add_mem ha₁ hb₁, by rw [mul_add, smul_add]; abel⟩
  · exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  · by_cases hK : i₀ ∈ K.1
    · rw [hc K (not_not.mpr hK), zero_smul, map_zero]
      exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    · obtain ⟨a₀, ha₀, a₁, e⟩ := hD (c K)
      refine ⟨a₀ * θK θ K.1, mul_mem_L hsq hac ha₀ (θK_mem_L θ K.2 hK), a₁ • θK θ K.1,
        Submodule.smul_mem _ _ (θK_mem_L θ K.2 hK), ?_⟩
      rw [hdK q _ K.1 K.2, e, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul]

include hac hdK hθD in
/-- For `b ∈ L θ i₀ q`, `d (θ b) = -(θ d b)`, where `θ = θ_{i₀}`. -/
theorem d_θ_mul_of_mem_L {q : ℕ} {b : Λ} (hb : b ∈ L (R := R) θ i₀ q) :
    d (q + 1) (θ i₀ * b) = -(θ i₀ * d q b) := by
  classical
  obtain ⟨c, hc, rfl⟩ := exists_combo_of_mem_span (fun K => i₀ ∉ K) hb
  unfold combo
  rw [Finset.mul_sum, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  by_cases hK : i₀ ∈ K.1
  · rw [hc K (not_not.mpr hK), zero_smul, mul_zero, map_zero, map_zero, mul_zero, neg_zero]
  · obtain ⟨ε, hε, he⟩ := exists_sign_θ_mul_θK (R := R) hac hK
    have hcard : (insert i₀ K.1).card = q + 1 := by rw [Finset.card_insert_of_notMem hK, K.2]
    rw [mul_smul_comm, he, smul_smul, hdK _ _ _ hcard, hdK _ _ _ K.2, ← mul_assoc, hθD,
      neg_mul, mul_assoc, he, mul_smul_comm, neg_neg]
    rcases hε with rfl | rfl
    · rw [mul_one, one_smul]
    · rw [mul_neg_one, map_neg, neg_mul, neg_one_smul]

/-- **The residue data of a chart**: the `ResidueData` with `θ`-free forms `L θ i₀` and
`θ = θ_{i₀}`. -/
def toResidueData (ξ' : Λ) (hξ' : ξ' ∈ L (R := R) θ i₀ 1) (μ lam lamInv : R)
    (hlam : lamInv * lam = 1) (hdlam : ∀ q b, d q (lamInv • b) = lamInv • d q b) :
    ResidueData R Λ where
  L := L θ i₀
  θ := θ i₀
  ξ' := ξ'
  t := t
  μ := μ
  lam := lam
  lamInv := lamInv
  d := d
  θ_mul_self := hsq i₀
  θ_mul_ξ' := θ_mul_eq_neg_of_mem_L hac hξ'
  ξ'_mul_mem := fun _ _ ha => mul_mem_L hsq hac hξ' ha
  lamInv_mul_lam := hlam
  eq_smul_of_add_θ_mul := fun _ _ ha _ hb _ ha' b' hb' h =>
    ⟨b', hb', eq_smul_of_add_θ_mul_eq_smul hind hac t ha hb ha' hb' h⟩
  d_mem := fun _ _ ha => d_mem_of_mem_L hsq hac i₀ t d Dr hdK hD ha
  d_θ_mul := fun _ _ hb => d_θ_mul_of_mem_L hac i₀ d Dr hdK hθD hb
  d_lamInv_smul := hdlam

end Residue

/-- An additive map commutes with multiplication by `N / b`, `b` invertible. -/
theorem map_smul_of_mul_eq_one {M : Type*} [AddCommMonoid M] [Module R M] (φ : M →+ M) (N b : ℕ)
    {binv : R} (hbinv : binv * (b : R) = 1) (x : M) :
    φ (((N : R) * binv) • x) = ((N : R) * binv) • φ x := by
  have key : φ (binv • x) = binv • φ x := by
    have h2 : (b : R) • φ (binv • x) = φ x := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← Nat.cast_smul_eq_nsmul R, smul_smul, mul_comm,
        hbinv, one_smul]
    rw [← h2, smul_smul, hbinv, one_smul]
  rw [mul_smul, mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul, key]

end ChartAlgebra

end MMP.LcBpf
