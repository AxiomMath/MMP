module

public import MMP.AlgebraicTopology.FundamentalClass.Restriction
public import MMP.AlgebraicTopology.FundamentalClass.Product
/-!
# The fundamental class of the real line

The real line `ℝ`, with its standard orientation, has a Borel–Moore fundamental class
`μ_ℝ ∈ H_1 ℝ`: the class of the locally finite cycle `∑_{n ∈ ℤ} [n, n + 1]`, the sum of the affine
segments between consecutive integers. Its boundary is `∑_n ([n + 1] - [n]) = 0`, and near every
point only finitely many segments occur.

The local condition is a computation with a relative cocycle `φ` of `(ℝ, ℝ - x)`: writing
`φ[a, b]` for its value on the affine segment from `a` to `b`, the cocycle condition on the affine
`2`-simplex `[a, b, c]` gives `φ[a, b] + φ[b, c] = φ[a, c]`, and `φ[a, b] = 0` when `x` is not
between `a` and `b`. So `∑_n φ[n, n + 1] = φ[⌊x⌋ - 1, ⌊x⌋ + 1] = φ[a, b]` for every segment with
`a < x < b`.

## Main definitions

* `MMP.FundamentalClass.segSimplex`: the affine segment `[a, b]` of `ℝ`.
* `MMP.FundamentalClass.realLineCycle`: the locally finite cycle
  `∑_{n ∈ ℤ} [n, n + 1]`.
* `MMP.FundamentalClass.realLineClass`: its class `μ_ℝ ∈ H_1 ℝ`.

## Main results

* `MMP.FundamentalClass.relCocycle_segSimplex_add`: `φ[a, b] + φ[b, c] = φ[a, c]`.
* `MMP.FundamentalClass.finsum_relCocycle_segSimplex`: `∑_n φ[n, n + 1] = φ[a, b]`
  for `a < x < b`.
* `MMP.FundamentalClass.isFundamentalClass_realLineClass`: `μ_ℝ` is the fundamental
  class of `ℝ` for the orientation of the standard basis.

## References

* [B. Iversen, *Cohomology of Sheaves*][iversen1986], IX.4.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Opposite Simplicial
open MMP.SingularChain MMP.SingularCochain
  MMP.ThomClass MMP.LocallyFiniteChain
  MMP.borelMooreHomology

namespace MMP

namespace FundamentalClass

section Affine

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousSMul ℝ V]

/-- The faces of an affine simplex are the affine simplices on the remaining vertices. -/
lemma affineSimplex_comp_face {n : ℕ} (v : Fin (n + 2) → V) (i : Fin (n + 2)) :
    (affineSimplex v).comp (face n i) = affineSimplex (v ∘ i.succAbove) := by
  ext t
  exact sum_stdSimplex_map_smul i.succAbove t v

/-- An affine simplex sends the `i`-th vertex of `Δⁿ` to `vᵢ`. -/
lemma affineSimplex_vertex {n : ℕ} (v : Fin (n + 1) → V) (i : Fin (n + 1)) :
    affineSimplex v (stdSimplex.vertex i) = v i := by
  rw [affineSimplex_apply]
  simp [stdSimplex.vertex, Pi.single_apply]

end Affine

section Segment

/-- The affine segment `[a, b]` of `ℝ`, as a singular `1`-simplex. -/
def segSimplex (a b : ℝ) : Simplex ℝ 1 :=
  affineSimplex ![a, b]

/-- The image of the segment `[a, b]` lies in the interval `uIcc a b`. -/
lemma range_segSimplex_subset (a b : ℝ) : range (segSimplex a b) ⊆ uIcc a b := by
  rintro _ ⟨t, rfl⟩
  rw [← segment_eq_uIcc]
  refine ⟨(t : Fin 2 → ℝ) 0, (t : Fin 2 → ℝ) 1, t.2.1 0, t.2.1 1, ?_, ?_⟩
  · have h := t.2.2
    rwa [Fin.sum_univ_two] at h
  · simp [segSimplex, affineSimplex_apply, Fin.sum_univ_two]

/-- An affine `1`-simplex of `ℝ` with vertices `v 0`, `v 1` is the segment `[v 0, v 1]`. -/
lemma affineSimplex_eq_segSimplex (v : Fin 2 → ℝ) : affineSimplex v = segSimplex (v 0) (v 1) := by
  rw [segSimplex]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The segment `[a, b]` sends the vertex `0` of `Δ¹` to `a`. -/
lemma segSimplex_vertex_zero (a b : ℝ) : segSimplex a b (stdSimplex.vertex 0) = a :=
  affineSimplex_vertex _ 0

variable {R : Type*} [CommRing R] {x : ℝ} {φ : Simplex ℝ 1 → R}

/-- A relative cocycle of `(ℝ, ℝ - x)` vanishes on segments avoiding `x`. -/
lemma relCocycle_segSimplex_eq_zero (hφ : φ ∈ relCocycles R ({x}ᶜ : Set ℝ) 1) {a b : ℝ}
    (h : x ∉ uIcc a b) : φ (segSimplex a b) = 0 :=
  hφ.1 _ fun _ hy hyx ↦ h (hyx ▸ range_segSimplex_subset a b hy)

/-- **Additivity on segments.** For a cocycle `φ` of `ℝ`, `φ[a, b] + φ[b, c] = φ[a, c]`: the
cocycle condition on the affine `2`-simplex `[a, b, c]`. -/
lemma relCocycle_segSimplex_add (hφ : φ ∈ relCocycles R ({x}ᶜ : Set ℝ) 1) (a b c : ℝ) :
    φ (segSimplex a b) + φ (segSimplex b c) = φ (segSimplex a c) := by
  have h := congrFun (LinearMap.mem_ker.1 hφ.2) (affineSimplex ![a, b, c])
  rw [coboundary_apply, Fin.sum_univ_three] at h
  simp only [affineSimplex_comp_face] at h
  have h0 : (![a, b, c] ∘ (0 : Fin 3).succAbove) = ![b, c] := by
    funext j
    fin_cases j <;> rfl
  have h1 : (![a, b, c] ∘ (1 : Fin 3).succAbove) = ![a, c] := by
    funext j
    fin_cases j <;> rfl
  have h2 : (![a, b, c] ∘ (2 : Fin 3).succAbove) = ![a, b] := by
    funext j
    fin_cases j <;> rfl
  rw [h0, h1, h2] at h
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_mul, neg_one_mul,
    neg_one_sq, Pi.zero_apply] at h
  rw [segSimplex, segSimplex, segSimplex]
  linear_combination h

/-- **The local computation.** For a relative cocycle `φ` of `(ℝ, ℝ - x)` and `a < x < b`,
`∑_{n ∈ ℤ} φ[n, n + 1] = φ[a, b]`. -/
theorem finsum_relCocycle_segSimplex (hφ : φ ∈ relCocycles R ({x}ᶜ : Set ℝ) 1) {a b : ℝ}
    (ha : a < x) (hb : x < b) :
    ∑ᶠ n : ℤ, φ (segSimplex n (n + 1)) = φ (segSimplex a b) := by
  set K := ⌊x⌋
  have hKx : (K : ℝ) ≤ x := Int.floor_le x
  have hxK : x < K + 1 := Int.lt_floor_add_one x
  have hsupp : (Function.support fun n : ℤ ↦ φ (segSimplex n (n + 1))) ⊆
      (({K - 1, K} : Finset ℤ) : Set ℤ) := by
    intro n hn
    by_contra hnot
    apply hn
    refine relCocycle_segSimplex_eq_zero hφ fun hx ↦ hnot ?_
    rw [uIcc_of_le (by linarith)] at hx
    have h1 : n ≤ K := Int.le_floor.2 hx.1
    have h2 : K ≤ n + 1 := by exact_mod_cast hKx.trans hx.2
    have : n = K - 1 ∨ n = K := by omega
    simpa using this
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair (by omega)]
  have hK1 : (((K - 1 : ℤ) : ℝ) + 1) = K := by push_cast; ring
  rw [hK1, relCocycle_segSimplex_add hφ]
  set L := min a ((K - 1 : ℤ) : ℝ)
  set U := max b ((K : ℝ) + 1)
  have e1 := relCocycle_segSimplex_add hφ L a U
  have e2 := relCocycle_segSimplex_add hφ a b U
  have e3 := relCocycle_segSimplex_add hφ L ((K - 1 : ℤ) : ℝ) U
  have e4 := relCocycle_segSimplex_add hφ ((K - 1 : ℤ) : ℝ) ((K : ℝ) + 1) U
  have hL1 : L ≤ a := min_le_left _ _
  have hL2 : L ≤ ((K - 1 : ℤ) : ℝ) := min_le_right _ _
  have hU1 : b ≤ U := le_max_left _ _
  have hU2 : (K : ℝ) + 1 ≤ U := le_max_right _ _
  have hKm : ((K - 1 : ℤ) : ℝ) = K - 1 := by push_cast; ring
  have z1 : φ (segSimplex L a) = 0 := relCocycle_segSimplex_eq_zero hφ fun h ↦ by
    rw [uIcc_of_le hL1] at h
    linarith [h.2]
  have z2 : φ (segSimplex b U) = 0 := relCocycle_segSimplex_eq_zero hφ fun h ↦ by
    rw [uIcc_of_le hU1] at h
    linarith [h.1]
  have z3 : φ (segSimplex L ((K - 1 : ℤ) : ℝ)) = 0 := relCocycle_segSimplex_eq_zero hφ fun h ↦ by
    rw [uIcc_of_le hL2] at h
    linarith [h.2]
  have z4 : φ (segSimplex ((K : ℝ) + 1) U) = 0 := relCocycle_segSimplex_eq_zero hφ fun h ↦ by
    rw [uIcc_of_le hU2] at h
    linarith [h.1]
  linear_combination e4 - z4 + e3 - z3 - e1 + z1 - e2 + z2

end Segment

section Cycle

variable (R : Type) [CommRing R]

/-- The segment `[n, n + 1]`, as a `1`-simplex of the singular simplicial set of `ℝ`. -/
def integerSegment (n : ℤ) : (TopCat.toSSet.obj (TopCat.of ℝ)).obj (op ⦋1⦌) :=
  (SingularCochain.simplexEquiv (TopCat.of ℝ) 1).symm (segSimplex n (n + 1))

/-- Distinct integers `n` give distinct segments `[n, n + 1]`. -/
lemma integerSegment_injective : Function.Injective integerSegment := by
  intro m n h
  have h' := congrArg (fun σ ↦ (SingularCochain.simplexEquiv (TopCat.of ℝ) 1 σ : Simplex ℝ 1)
    (stdSimplex.vertex 0)) h
  simp only [integerSegment, Equiv.apply_symm_apply] at h'
  erw [segSimplex_vertex_zero, segSimplex_vertex_zero] at h'
  exact_mod_cast h'

/-- The image of the segment `[n, n + 1]` lies in the interval `Icc n (n + 1)`. -/
lemma singularSimplexImage_integerSegment_subset (n : ℤ) :
    singularSimplexImage (TopCat.of ℝ) (integerSegment n) ⊆ Icc (n : ℝ) (n + 1) := by
  rw [← uIcc_of_le (by linarith), ← range_simplexEquiv]
  rintro _ ⟨t, rfl⟩
  exact range_segSimplex_subset _ _ ⟨t, by rw [integerSegment, Equiv.apply_symm_apply]⟩

open Classical in
/-- The coefficients of `∑_{n ∈ ℤ} [n, n + 1]`. -/
def realLineCycleFun : (TopCat.toSSet.obj (TopCat.of ℝ)).obj (op ⦋1⦌) → R :=
  fun σ ↦ if σ ∈ range integerSegment then 1 else 0

/-- Every segment `[n, n + 1]` has coefficient `1` in `∑_{n ∈ ℤ} [n, n + 1]`. -/
lemma realLineCycleFun_integerSegment (n : ℤ) :
    realLineCycleFun R (integerSegment n) = 1 := by
  simp [realLineCycleFun]

/-- The support of `realLineCycleFun` consists of segments `[n, n + 1]`. -/
lemma support_realLineCycleFun_subset :
    Function.support (realLineCycleFun R) ⊆ range integerSegment := fun σ hσ ↦ by
  by_contra h
  exact hσ (by simp [realLineCycleFun, h])

/-- The support of `realLineCycleFun` is locally finite: near every point of `ℝ` only finitely
many segments `[n, n + 1]` occur. -/
lemma isLocallyFiniteSet_realLineCycleFun :
    IsLocallyFiniteSet (singularSimplexImage (TopCat.of ℝ))
      (Function.support (realLineCycleFun R)) := fun x ↦ by
  refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  refine ((Set.finite_Ioo (⌊x⌋ - 2) (⌊x⌋ + 2)).image integerSegment).subset ?_
  rintro σ ⟨hσ, y, hy, hyV⟩
  obtain ⟨n, rfl⟩ := support_realLineCycleFun_subset R hσ
  have hn := singularSimplexImage_integerSegment_subset n hy
  refine ⟨n, ⟨?_, ?_⟩, rfl⟩
  · have h1 : ((⌊x⌋ - 2 : ℤ) : ℝ) < n := by
      push_cast; linarith [Int.floor_le x, hn.2, hyV.1]
    exact_mod_cast h1
  · have h1 : (n : ℝ) < ((⌊x⌋ + 2 : ℤ) : ℝ) := by
      push_cast; linarith [Int.lt_floor_add_one x, hn.1, hyV.2]
    exact_mod_cast h1

/-- The locally finite chain `∑_{n ∈ ℤ} [n, n + 1]` of `ℝ`. -/
def realLineChain : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ℝ)).X 1 :=
  (⟨realLineCycleFun R, isLocallyFiniteSet_realLineCycleFun R⟩ :
    lfChains R (ModuleCat.of R R) (singularSimplexImage (TopCat.of ℝ)))

/-- The sum `∑ᶠ` over `1`-simplices of `ℝ` of a function supported on the segments
`[n, n + 1]` is the sum over `n ∈ ℤ` of its values on them. -/
lemma finsum_eq_finsum_integerSegment {M : Type*} [AddCommMonoid M]
    (f : (TopCat.toSSet.obj (TopCat.of ℝ)).obj (op ⦋1⦌) → M)
    (hf : Function.support f ⊆ range integerSegment) :
    ∑ᶠ σ, f σ = ∑ᶠ n : ℤ, f (integerSegment n) := by
  rw [← finsum_mem_range integerSegment_injective, finsum_mem_def, Set.indicator_eq_self.2 hf]

/-- The faces of `[n, n + 1]` are the points `n + 1` and `n`. -/
lemma δ_integerSegment (i : Fin 2) (n : ℤ) :
    (SingularCochain.simplexEquiv (TopCat.of ℝ) _ ((TopCat.toSSet.obj (TopCat.of ℝ)).δ i (integerSegment n)) :
      Simplex ℝ 0) = affineSimplex ![(n : ℝ) + i.rev] := by
  rw [toSSetObjEquiv_δ]
  simp only [integerSegment, Equiv.apply_symm_apply]
  erw [affineSimplex_comp_face]
  congr 1
  funext j
  fin_cases i <;> fin_cases j <;> simp

/-- `∑_{n ∈ ℤ} [n, n + 1]` is a cycle. -/
lemma d_realLineChain :
    ((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ℝ)).d 1 0).hom (realLineChain R) =
      0 := by
  classical
  apply Subtype.ext
  rw [borelMooreChainComplex_d_apply]
  funext τ
  have hpush : ∀ i : Fin 2, pushforwardFun ((TopCat.toSSet.obj (TopCat.of ℝ)).δ i)
      (realLineCycleFun R) τ = ∑ᶠ n : ℤ,
        if affineSimplex ![(n : ℝ) + i.rev] = (SingularCochain.simplexEquiv (TopCat.of ℝ) _ τ : Simplex ℝ 0)
        then (1 : R) else 0 := by
    intro i
    rw [pushforwardFun, finsum_eq_finsum_integerSegment]
    · refine finsum_congr fun n ↦ ?_
      rw [realLineCycleFun_integerSegment, ← δ_integerSegment]
      exact if_congr (SingularCochain.simplexEquiv (TopCat.of ℝ) _).apply_eq_iff_eq.symm rfl rfl
    · intro σ hσ
      by_contra h
      exact hσ (by simp [realLineCycleFun, h])
  change ∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) • pushforwardFun _ (realLineCycleFun R) τ = 0
  rw [Fin.sum_univ_two, hpush, hpush]
  have hshift : (∑ᶠ n : ℤ, if affineSimplex ![(n : ℝ) + (0 : Fin 2).rev] =
      (SingularCochain.simplexEquiv (TopCat.of ℝ) _ τ : Simplex ℝ 0) then (1 : R) else 0) =
      ∑ᶠ n : ℤ, if affineSimplex ![(n : ℝ) + (1 : Fin 2).rev] =
        (SingularCochain.simplexEquiv (TopCat.of ℝ) _ τ : Simplex ℝ 0) then (1 : R) else 0 := by
    conv_rhs => rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
    refine finsum_congr fun n ↦ ?_
    simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
    congr 3
    simp [Fin.rev]
  rw [hshift]
  simp

/-- The cycle `∑_{n ∈ ℤ} [n, n + 1]`. -/
def realLineCycle : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ℝ)).cycles 1 :=
  ((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ℝ)).sc 1).moduleCatCyclesIso.inv.hom
    ⟨realLineChain R, by
      change ((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ℝ)).d 1
        ((ComplexShape.down ℕ).next 1)).hom (realLineChain R) = 0
      rw [ChainComplex.next_nat_succ]
      exact d_realLineChain R⟩

/-- The underlying chain of the cycle `realLineCycle` is `realLineChain`. -/
lemma iCycles_realLineCycle :
    (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ℝ)).iCycles 1 (realLineCycle R) =
      realLineChain R := by
  rw [← coe_moduleCatCyclesIso_hom, realLineCycle]
  erw [Iso.inv_hom_id_apply]

/-- The fundamental class `μ_ℝ ∈ H_1 ℝ`: the class of `∑_{n ∈ ℤ} [n, n + 1]`. -/
def realLineClass : borelMooreHomology R (ModuleCat.of R R) (TopCat.of ℝ) (1 : ℕ) :=
  (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) (TopCat.of ℝ) 1).inv.hom
    ((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ℝ)).homologyπ 1 (realLineCycle R))

variable {R}

/-- The pairing of `∑_{n ∈ ℤ} [n, n + 1]` with a cochain is `∑_n φ[n, n + 1]`. -/
lemma localPairing_realLineChain (φ : Simplex (TopCat.of ℝ) 1 → R) :
    localPairing ((realLineChain R).1 : (TopCat.toSSet.obj (TopCat.of ℝ)).obj (op ⦋1⦌) → R) φ =
      ∑ᶠ n : ℤ, φ (segSimplex n (n + 1)) := by
  rw [localPairing, finsum_eq_finsum_integerSegment]
  · refine finsum_congr fun n ↦ ?_
    change realLineCycleFun R (integerSegment n) * _ = _
    rw [realLineCycleFun_integerSegment, one_mul]
    simp [integerSegment]
  · intro σ hσ
    by_contra h
    exact hσ (by simp [realLineChain, realLineCycleFun, h])

/-- `μ_ℝ` is locally, at every point `x`, the class of every segment `[a, b]` with
`a < x < b`. -/
theorem isLocallyClassOf_realLineClass {x a b : ℝ} (ha : a < x) (hb : x < b) :
    IsLocallyClassOf R (realLineClass R) (x : TopCat.of ℝ) (segSimplex a b) := by
  intro z hz φ hφ
  have hz' : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ℝ)).homologyπ 1 z =
      (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of ℝ)).homologyπ 1
        (realLineCycle R) := by
    rw [hz, realLineClass]
    exact Iso.inv_hom_id_apply _ _
  rw [localPairing_eq_of_homologyπ_eq hz' hφ, iCycles_realLineCycle,
    localPairing_realLineChain]
  exact finsum_relCocycle_segSimplex hφ ha hb

/-- **The fundamental class of the real line.** `μ_ℝ`, the class of `∑_{n ∈ ℤ} [n, n + 1]`, is
the fundamental class of `ℝ` for the orientation of the standard basis. -/
theorem isFundamentalClass_realLineClass :
    IsFundamentalClass (H := ℝ) (M := ℝ) R (Module.Basis.singleton (Fin 1) ℝ)
      (realLineClass R) := by
  intro e he x v hv hvt
  rw [chartedSpaceSelf_atlas] at he
  subst he
  apply IsLocallyClassOf.restrict
  have hΔ : inclChainSimplex (chartOpens (OpenPartialHomeomorph.refl ℝ))
      (chartSimplex (OpenPartialHomeomorph.refl ℝ) v hvt) = segSimplex (v 0) (v 1) := by
    rw [← affineSimplex_eq_segSimplex]
    rfl
  rw [hΔ]
  obtain ⟨⟨t, ht, hsum, hcomb⟩, hdet⟩ := hv
  simp only [OpenPartialHomeomorph.refl_apply, id_eq] at hcomb hdet
  rw [Module.Basis.det_apply, Matrix.det_unique] at hdet
  simp only [Module.Basis.toMatrix_apply, Module.Basis.singleton_repr] at hdet
  rw [Fin.sum_univ_two] at hsum hcomb
  simp only [smul_eq_mul] at hcomb
  have hd : 0 < v 1 - v 0 := by
    change 0 < v 1 - (x : ℝ) - (v 0 - x) at hdet
    linarith
  have hx0 : (x : ℝ) - v 0 = t 1 * (v 1 - v 0) := by
    linear_combination -hcomb - ((x : ℝ) - v 0) * hsum
  have hx1 : v 1 - (x : ℝ) = t 0 * (v 1 - v 0) := by
    linear_combination hcomb - (v 1 - (x : ℝ)) * hsum
  refine isLocallyClassOf_realLineClass (x := (x : ℝ)) ?_ ?_
  · nlinarith [mul_pos (ht 1) hd]
  · nlinarith [mul_pos (ht 0) hd]

end Cycle

end FundamentalClass

end MMP
