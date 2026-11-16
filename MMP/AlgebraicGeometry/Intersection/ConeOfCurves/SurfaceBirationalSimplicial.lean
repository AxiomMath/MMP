module

public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialPart
import MMP.AlgebraicGeometry.Morphisms.Birational.AntiAmpleExceptional
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus

/-!
# The relative cone of a birational morphism of `ℚ`-factorial surfaces is simplicial

Let `g : S ⟶ T` be a projective birational morphism of normal quasi-projective surfaces over a
field `k`, with `S` `ℚ`-factorial. Only finitely many irreducible curves `E₁, …, E_r ⊆ S` are
contracted by `g`, and every curve contracted by `g` is one of them. Since `S` is `ℚ`-factorial,
each `Eⱼ` is a `ℚ`-Cartier divisor, and the matrix `((Eᵢ · Eⱼ))` is negative definite; so the
classes `[Eᵢ] ∈ N₁(S/T)` are linearly independent. Hence the closed relative cone of curves
`NE̅(S/T)` is the simplicial cone spanned by the `[Eᵢ]`, and each `[Eᵢ]` spans an extremal ray
of it.

## Main results

* `MMP.Mori.relativeClosedConeOfCurves_eq_hull_of_isBirationalMorphism`: for such `g`, the
  contracted curves are finitely many, `NE̅(S/T)` is the cone they span, each of them spans an
  extremal ray of `NE̅(S/T)`, and their classes are linearly independent. In particular
  `NE̅(S/T)` is simplicial (`PointedCone.IsSimplicial.hull`).

## Implementation notes

The irreducible exceptional curves of `g` are the proper curves `C ⊆ S` contracted by `g`
(`MMP.Mori.ProperCurve.IsContractedBy`); for a proper birational morphism of surfaces these
are exactly the one-dimensional components of the exceptional locus. Their classes are taken in
`N₁(S/T)` (`MMP.Mori.RelativeNumericalCurveClasses`) via `MMP.Mori.ProperCurve.relativeClass`.
The source works over `ℂ`; the statement is made over an arbitrary field.

The proof avoids a smooth resolution, which need not exist over an arbitrary field. Kollár's
divisor gives a nonnegative weight vector on which the matrix `((Dᵢ · Cⱼ))` of Cartier multiples
`Dᵢ` of the contracted curves is strictly negative, so the matrix is invertible; a continuous
coordinate map then identifies the cone spanned by the classes with the closed orthant. Its
auxiliary lemmas live in the namespace `Proof_lem_mmp_surface_birational_cone_simplicial`,
opened only for the main result.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §4.1
* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 2.9–2.12
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_mmp_surface_birational_cone_simplicial

open MMP.Mori

/-! ### Linear algebra -/

section LinearAlgebra

/-- A real matrix with nonnegative off-diagonal entries that is negative on a nonnegative weight
vector, `∑ᵢ wᵢ Aᵢⱼ < 0` for every `j`, is invertible. -/
private theorem det_ne_zero_of_offDiag_nonneg_of_sum_mul_neg {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n ℝ) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hAw : ∀ j, ∑ i, w i * A i j < 0) : A.det ≠ 0 := by
  have hsplit : ∀ j, ∑ i, w i * A i j =
      w j * A j j + ∑ i ∈ Finset.univ.erase j, w i * A i j := fun j =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hrest : ∀ j, 0 ≤ ∑ i ∈ Finset.univ.erase j, w i * A i j := fun j =>
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i) (hoff i j (Finset.ne_of_mem_erase hi))
  have hdiag : ∀ j, w j * A j j < 0 := fun j => by linarith [hAw j, hsplit j, hrest j]
  set B : Matrix n n ℝ := Matrix.diagonal w * A with hB
  have hBapp : ∀ i j, B i j = w i * A i j := fun i j => by
    simp [hB, Matrix.diagonal_mul]
  have hBdet : B.det ≠ 0 := by
    refine det_ne_zero_of_sum_col_lt_diag fun k => ?_
    simp only [hBapp, Real.norm_eq_abs]
    rw [abs_of_neg (hdiag k)]
    have : ∑ i ∈ Finset.univ.erase k, |w i * A i k| = ∑ i ∈ Finset.univ.erase k, w i * A i k :=
      Finset.sum_congr rfl fun i hi =>
        abs_of_nonneg (mul_nonneg (hw i) (hoff i k (Finset.ne_of_mem_erase hi)))
    rw [this]
    linarith [hAw k, hsplit k]
  exact fun hA => hBdet (by rw [hB, Matrix.det_mul, hA, mul_zero])

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

/-- If `Ψ` sends the vectors `vⱼ` to the standard basis and `z = ∑ⱼ Ψ(z)ⱼ vⱼ` for every `z`, then
the cone spanned by the `vⱼ` is the set where every coordinate `Ψ(z)ⱼ` is nonnegative. -/
private theorem mem_hull_iff_of_leftInverse (v : ι → V) (Ψ : V →ₗ[ℝ] ι → ℝ)
    (hrec : ∀ z, ∑ j, Ψ z j • v j = z) (hΨv : ∀ j, Ψ (v j) = Pi.single j 1) (z : V) :
    z ∈ PointedCone.hull ℝ (Set.range v) ↔ ∀ j, 0 ≤ Ψ z j := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro j
      rw [hΨv]
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_apply, h]
    | zero => simp
    | add x y _ _ hx hy => intro j; simpa using add_nonneg (hx j) (hy j)
    | smul a x _ hx =>
      intro j
      have : Ψ (a • x) j = (a : ℝ) * Ψ x j := by
        rw [show a • x = (a : ℝ) • x from rfl, map_smul]
        rfl
      rw [this]
      exact mul_nonneg a.2 (hx j)
  · intro h
    rw [← hrec z]
    exact Submodule.sum_mem _ fun j _ =>
      PointedCone.smul_mem _ (h j) (PointedCone.subset_hull ⟨j, rfl⟩)

/-- **A cone with continuous coordinates is a closed simplicial cone.** If a continuous linear
map `Ψ : V → ℝ^ι` sends the vectors `vⱼ` to the standard basis and `z = ∑ⱼ Ψ(z)ⱼ vⱼ` for every
`z`, then the cone spanned by the `vⱼ` is closed, each `vⱼ` spans an extremal ray of it, and the
`vⱼ` are linearly independent. -/
private theorem cone_facts_of_leftInverse [TopologicalSpace V] (v : ι → V) (Ψ : V →ₗ[ℝ] ι → ℝ)
    (hΨ : Continuous Ψ) (hrec : ∀ z, ∑ j, Ψ z j • v j = z)
    (hΨv : ∀ j, Ψ (v j) = Pi.single j 1) :
    IsClosed (PointedCone.hull ℝ (Set.range v) : Set V) ∧
    (∀ j, IsExtremalRay ℝ (PointedCone.hull ℝ (Set.range v) : Set V)
      {w | ∃ c : ℝ, 0 ≤ c ∧ c • v j = w}) ∧
    LinearIndependent ℝ v := by
  have hmem := mem_hull_iff_of_leftInverse v Ψ hrec hΨv
  refine ⟨?_, fun j => ?_, ?_⟩
  · have : (PointedCone.hull ℝ (Set.range v) : Set V) =
        ⋂ j, (fun z => Ψ z j) ⁻¹' Set.Ici 0 := by
      ext z
      simp [hmem]
    rw [this]
    exact isClosed_iInter fun j => isClosed_Ici.preimage ((continuous_apply j).comp hΨ)
  · refine ⟨⟨?_, ⟨⟨0, le_rfl, zero_smul _ _⟩, ?_⟩, ?_, ?_⟩, v j, ?_, rfl⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact PointedCone.smul_mem _ hc (PointedCone.subset_hull ⟨j, rfl⟩)
    · rintro _ ⟨c, hc, rfl⟩ c' hc'
      exact ⟨c' * c, mul_nonneg hc'.le hc, by rw [mul_smul]⟩
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
      exact ⟨c + c', add_nonneg hc hc', add_smul _ _ _⟩
    · have key : ∀ x y : V, x ∈ PointedCone.hull ℝ (Set.range v) →
          y ∈ PointedCone.hull ℝ (Set.range v) → (∃ c : ℝ, 0 ≤ c ∧ c • v j = x + y) →
          ∃ c : ℝ, 0 ≤ c ∧ c • v j = x := by
        rintro x y hx hy ⟨c, -, hc⟩
        rw [hmem] at hx hy
        have hzero : ∀ i, i ≠ j → Ψ x i = 0 := fun i hi => by
          have h1 := congrArg (fun z => Ψ z i) hc
          simp only [map_smul, map_add, hΨv, Pi.smul_apply, Pi.add_apply, Pi.single_apply, hi,
            if_false, smul_zero] at h1
          linarith [hx i, hy i]
        refine ⟨Ψ x j, hx j, ?_⟩
        conv_rhs => rw [← hrec x]
        rw [Finset.sum_eq_single j (fun i _ hi => by rw [hzero i hi, zero_smul])
          (fun h => absurd (Finset.mem_univ j) h)]
      intro x hx y hy hxy
      exact ⟨key x y hx hy hxy, key y x hy hx (by rwa [add_comm])⟩
    · intro h
      have := congrArg (fun z => Ψ z j) h
      simp [hΨv] at this
  · refine LinearIndependent.of_comp Ψ ?_
    have : Ψ ∘ v = Pi.basisFun ℝ ι := by
      ext j : 1
      simp [hΨv, Pi.basisFun_apply]
    rw [this]
    exact (Pi.basisFun ℝ ι).linearIndependent

/-- From a continuous linear map `Φ : V → ℝ^ι` sending each `vⱼ` to the `j`-th column of an
invertible matrix `M`, and the spanning of `V` by the `vⱼ`, the map `Ψ = M⁻¹ ∘ Φ` is a continuous
coordinate map for the `vⱼ`. -/
private theorem exists_leftInverse_of_det_ne_zero [TopologicalSpace V] (v : ι → V)
    (hspan : ∀ z, ∃ c : ι → ℝ, ∑ j, c j • v j = z) (Φ : V →ₗ[ℝ] ι → ℝ) (hΦ : Continuous Φ)
    (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) (hΦv : ∀ j, Φ (v j) = fun i => M i j) :
    ∃ Ψ : V →ₗ[ℝ] ι → ℝ, Continuous Ψ ∧ (∀ z, ∑ j, Ψ z j • v j = z) ∧
      ∀ j, Ψ (v j) = Pi.single j 1 := by
  have hΨv : ∀ j, ((M⁻¹).mulVecLin ∘ₗ Φ) (v j) = Pi.single j 1 := fun j => by
    have hcol : (fun i => M i j) = M.mulVec (Pi.single j 1) := by
      ext i; simp [Matrix.mulVec_single_one]
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, hΦv, hcol, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  refine ⟨(M⁻¹).mulVecLin ∘ₗ Φ,
    (LinearMap.continuous_of_finiteDimensional (M⁻¹).mulVecLin).comp hΦ, fun z => ?_, hΨv⟩
  obtain ⟨c, rfl⟩ := hspan z
  have : ((M⁻¹).mulVecLin ∘ₗ Φ) (∑ j, c j • v j) = c := by
    ext i; simp [map_sum, hΨv, Pi.single_apply]
  rw [this]

end LinearAlgebra

/-- Given `W ≥ 0` and positive integers `mᵢ` attached to distinct points `Pᵢ`, some positive
multiple `N W` is `∑ᵢ wᵢ mᵢ Pᵢ + R` with every `wᵢ ≥ 0`, `R ≥ 0`, and `R` vanishing at every
`Pᵢ`. -/
private theorem exists_nsmul_eq_add_sum {α ι : Type*} [Fintype ι] (P : ι → α)
    (hP : Function.Injective P) (m : ι → ℕ) (hm : ∀ i, 0 < m i) (W : α →₀ ℤ) (hW : 0 ≤ W) :
    ∃ N : ℕ, 0 < N ∧ ∃ w : ι → ℤ, (∀ i, 0 ≤ w i) ∧ ∃ R : α →₀ ℤ, 0 ≤ R ∧ (∀ j, R (P j) = 0) ∧
      (N : ℤ) • W = R + ∑ i, w i • (m i : ℤ) • Finsupp.single (P i) 1 := by
  classical
  set N := ∏ i, m i
  set w : ι → ℤ := fun i => (∏ l ∈ Finset.univ.erase i, m l : ℕ) * W (P i)
  have happ : ∀ E, ((N : ℤ) • W - ∑ i, w i • (m i : ℤ) • Finsupp.single (P i) 1 : α →₀ ℤ) E =
      N * W E - ∑ i, if P i = E then w i * m i else 0 := fun E => by
    simp only [Finsupp.coe_sub, Finsupp.coe_smul, Finsupp.coe_finset_sum, Pi.sub_apply,
      Pi.smul_apply, Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, smul_ite, mul_one,
      smul_zero, mul_ite, mul_zero]
  have hRP : ∀ j,
      ((N : ℤ) • W - ∑ i, w i • (m i : ℤ) • Finsupp.single (P i) 1 : α →₀ ℤ) (P j) = 0 :=
    fun j => by
      rw [happ]
      simp only [hP.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true, w, N,
        ← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
      push_cast
      ring
  refine ⟨N, Finset.prod_pos fun i _ => hm i, w, fun i => mul_nonneg (by positivity) (hW _),
    _, fun E => ?_, hRP, (sub_add_cancel _ _).symm⟩
  change 0 ≤ (_ : α →₀ ℤ) E
  by_cases hE : E ∈ Set.range P
  · obtain ⟨j, rfl⟩ := hE
    rw [hRP]
  · rw [happ, Finset.sum_eq_zero fun i _ => if_neg fun h => hE ⟨i, h⟩, sub_zero]
    exact mul_nonneg (by positivity) (hW E)

section Geometry

variable {k : Type u} [Field k] {S T : Scheme.{u}} {sS : S ⟶ Spec (.of k)}

/-- On an integral surface the generic point of a proper curve has coheight one. -/
private theorem coheight_point_eq_one [IsIntegral S] [CompactSpace S]
    (hdim : topologicalKrullDim S = 2) (C : ProperCurve sS) : Order.coheight C.point = 1 := by
  have hK : Order.krullDim S = 2 := by
    rw [← hdim]
    exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S))).symm
  have hcl : topologicalKrullDim (closure {C.point} : Set S) = 1 := by
    have := C.dim_eq
    rwa [MMP.Mori.topologicalKrullDim_subscheme_eq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  have hnc : ¬ IsClosed ({C.point} : Set S) := by
    intro h
    rw [h.closure_eq] at hcl
    have : topologicalKrullDim ({C.point} : Set S) ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [hcl] at this
    exact absurd this (by decide)
  have hη : C.point ≠ genericPoint S := by
    intro h
    rw [h, (genericPoint_spec S).def,
      (Homeomorph.Set.univ S).isHomeomorph.topologicalKrullDim_eq, hdim] at hcl
    exact absurd hcl (by decide)
  obtain ⟨z, -, hxz, hne⟩ := MMP.Mori.exists_isClosed_singleton_specializes hnc
  have hzx : z < C.point := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hxz) fun h =>
    hne (hxz.antisymm (Scheme.le_iff_specializes.1 h)).eq
  have hηx : genericPoint S ⤳ C.point := (genericPoint_spec S).specializes trivial
  have hxη : C.point < genericPoint S := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hηx)
    fun h => hη (hηx.antisymm (Scheme.le_iff_specializes.1 h)).eq.symm
  have h1 := Order.height_add_one_le hzx
  have h2 := Order.coheight_add_one_le hxη
  have h3 : Order.height C.point + Order.coheight C.point ≤ 2 := by
    have := Order.height_add_coheight_le_krullDim C.point
    rw [hK] at this
    have h₄ : ((Order.height C.point + Order.coheight C.point : ℕ∞) : WithBot ℕ∞) ≤
        ((2 : ℕ∞) : WithBot ℕ∞) := by
      push_cast
      exact this
    exact WithBot.coe_le_coe.mp h₄
  generalize Order.height C.point = a at h1 h3
  generalize Order.coheight C.point = b at h2 h3 ⊢
  have ha : 1 ≤ a := le_trans le_add_self h1
  have hb : 1 ≤ b := le_trans le_add_self h2
  induction a using ENat.recTopCoe with
  | top => simp at h3
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h3
    | coe b =>
      norm_cast at ha hb h3 ⊢
      omega

/-- An effective Cartier divisor with no component through the generic point of a proper curve
has nonnegative degree on it. -/
private theorem degreeOn_nonneg_of_coeff_eq_zero [QuasiCompact sS] [IsLocallyNoetherian S]
    [IsNormal S] (D : Divisor S) (hDc : D.IsCartier) (hD : 0 ≤ D) (C : ProperCurve sS)
    (P : MMP.Mori.PrimeDivisor S) (hC : C.point = P.genericPoint) (hP : D P = 0) :
    0 ≤ D.degreeOn k sS C.ι C.dim_le hDc := by
  obtain ⟨c, hc⟩ := MMP.Threefold.Mori.exists_ι_eq_point C.point
  refine (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sS C.ι C.dim_le D hDc hD
    ⟨c, ?_⟩).1
  change curveSubschemeAtι C.point c ∉ _
  rw [hc, hC]
  intro hmem
  obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.1 hmem
  obtain rfl : E = P := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E P hxE
  exact hE hP

/-- A finite sum of Cartier divisors is Cartier. -/
private theorem isCartier_sum [IsLocallyNoetherian S] [IsNormal S] {ι : Type*} (s : Finset ι)
    (D : ι → Divisor S) (hD : ∀ i, (D i).IsCartier) : (∑ i ∈ s, D i).IsCartier :=
  Divisor.cartierSubgroup.sum_mem fun i _ => hD i

/-- The degree along a curve is additive over finite sums of Cartier divisors. -/
private theorem degreeOn_sum [QuasiCompact sS] [IsLocallyNoetherian S] [IsNormal S]
    (C : ProperCurve sS) {ι : Type*} (s : Finset ι) (D : ι → Divisor S)
    (hD : ∀ i, (D i).IsCartier) :
    (∑ i ∈ s, D i).degreeOn k sS C.ι C.dim_le (isCartier_sum s D hD) =
      ∑ i ∈ s, (D i).degreeOn k sS C.ι C.dim_le (hD i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Divisor.degreeOn_zero' k sS C.ι C.dim_le
  | insert a s ha ih =>
    rw [Divisor.degreeOn_congr (Finset.sum_insert ha) _ ((hD a).add (isCartier_sum s D hD)),
      Divisor.degreeOn_add k sS C.ι C.dim_le _ _ (hD a) (isCartier_sum s D hD), ih,
      Finset.sum_insert ha]

/-- The classes of the curves contracted by `g` span `N₁(S/T)`. -/
private theorem exists_sum_smul_relativeClass_eq (g : S ⟶ T)
    [Fintype {C : ProperCurve sS // C.IsContractedBy g}] (z : RelativeNumericalCurveClasses sS g) :
    ∃ c : {C : ProperCurve sS // C.IsContractedBy g} → ℝ,
      ∑ j, c j • j.1.relativeClass g j.2 = z := by
  classical
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sS g z
  refine ⟨fun j => (Z : OneCycle ℝ sS) j.1, ?_⟩
  simp only [ProperCurve.relativeClass, ← map_smul, ← map_sum]
  congr 1
  apply Subtype.ext
  ext C
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, ProperCurve.cycle, Finsupp.single_apply, smul_eq_mul]
  by_cases hC : C.IsContractedBy g
  · rw [Finset.sum_eq_single ⟨C, hC⟩ (fun j _ hj => by
      rw [if_neg (fun h => hj (Subtype.ext h)), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, mul_one]
  · rw [Finset.sum_eq_zero fun j _ => by
      rw [if_neg (fun h : j.1 = C => hC (h ▸ j.2)), mul_zero]]
    exact (Finsupp.notMem_support_iff.1 fun h =>
      hC ((Finsupp.mem_supported ℝ (Z : OneCycle ℝ sS)).1 Z.2 h)).symm

/-- **The intersection matrix of the contracted curves is invertible.** Let `C₁, …, C_r` be proper
curves on a normal surface whose generic points are those of distinct prime divisors `Pⱼ`, and let
`Dᵢ = mᵢ Pᵢ` with `mᵢ > 0` be Cartier. If an effective Cartier divisor `W` has negative degree on
every `Cⱼ`, the matrix `((Dᵢ · Cⱼ))` is invertible. -/
private theorem det_degreeOn_ne_zero [QuasiCompact sS] [IsLocallyNoetherian S] [IsNormal S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → ProperCurve sS)
    (P : ι → MMP.Mori.PrimeDivisor S) (hP : Function.Injective P)
    (hPC : ∀ j, (C j).point = (P j).genericPoint) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hD : ∀ i, ((m i : ℤ) • Finsupp.single (P i) 1 : Divisor S).IsCartier)
    {W : Divisor S} (hW0 : 0 ≤ W) (hWc : W.IsCartier)
    (hWneg : ∀ j, W.degreeOn k sS (C j).ι (C j).dim_le hWc < 0) :
    (Matrix.of fun i j => ((((m i : ℤ) • Finsupp.single (P i) 1 : Divisor S).degreeOn k sS
      (C j).ι (C j).dim_le (hD i) : ℤ) : ℝ)).det ≠ 0 := by
  obtain ⟨N, hN, w, hw0, R, hR0, hRP, hdec⟩ := exists_nsmul_eq_add_sum P hP m hm W hW0
  have hwD : ∀ i, (w i • (m i : ℤ) • Finsupp.single (P i) 1 : Divisor S).IsCartier :=
    fun i => (hD i).zsmul _
  have hRc : Divisor.IsCartier R :=
    eq_sub_of_add_eq hdec.symm ▸ (hWc.zsmul _).sub (isCartier_sum _ _ hwD)
  refine det_ne_zero_of_offDiag_nonneg_of_sum_mul_neg _ (fun i j hij => ?_) (fun i => (w i : ℝ))
    (fun i => by exact_mod_cast hw0 i) fun j => ?_
  · simp only [Matrix.of_apply]
    exact_mod_cast degreeOn_nonneg_of_coeff_eq_zero _ (hD i)
      (smul_nonneg (by positivity) (Finsupp.single_nonneg.2 zero_le_one)) (C j) (P j) (hPC j)
      (by simp [Finsupp.single_apply, hP.ne hij])
  · have h := Divisor.degreeOn_zsmul' k sS (C j).ι (C j).dim_le W hWc N
    rw [Divisor.degreeOn_congr hdec _ (hRc.add (isCartier_sum _ _ hwD)),
      Divisor.degreeOn_add k sS _ _ _ _ hRc (isCartier_sum _ _ hwD), degreeOn_sum (C j) _ _ hwD]
      at h
    simp only [fun i => Divisor.degreeOn_zsmul' k sS (C j).ι (C j).dim_le _ (hD i) (w i)] at h
    have := degreeOn_nonneg_of_coeff_eq_zero R hRc hR0 (C j) (P j) (hPC j) (hRP j)
    have hsum : ∑ i, w i * ((m i : ℤ) • Finsupp.single (P i) 1 : Divisor S).degreeOn k sS
        (C j).ι (C j).dim_le (hD i) < 0 := by
      nlinarith [hWneg j, (by exact_mod_cast hN : (0 : ℤ) < N)]
    simp only [Matrix.of_apply]
    exact_mod_cast hsum

end Geometry

end Proof_lem_mmp_surface_birational_cone_simplicial

namespace MMP.Mori

open Proof_lem_mmp_surface_birational_cone_simplicial

/-- **The relative cone of a birational morphism of `ℚ`-factorial surfaces is simplicial.** Let
`g : S ⟶ T` be a projective birational morphism of normal quasi-projective surfaces over `k`,
with `S` `ℚ`-factorial. Then only finitely many proper curves `C ⊆ S` are contracted by `g`;
the closed relative cone of curves `NE̅(S/T)` is the cone spanned by their classes `[C]`; each
`[C]` spans an extremal ray `ℝ_{≥0}·[C]` of `NE̅(S/T)`; and the classes `[C]` are linearly
independent in `N₁(S/T)`. -/
@[mmp "lem_mmp_surface_birational_cone_simplicial"]
public theorem relativeClosedConeOfCurves_eq_hull_of_isBirationalMorphism
    {k : Type u} [Field k] {S T : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
    [IsLocallyNoetherian S] [IsNormal S]
    (hS : MMP.Fourfold.IsQFactorial sS) (hT : IsNormalVariety k sT)
    (hSq : IsQuasiProjectiveVariety k sS) (hTq : IsQuasiProjectiveVariety k sT)
    (hSdim : topologicalKrullDim S = 2) (hTdim : topologicalKrullDim T = 2)
    (g : S ⟶ T) (hg : g ≫ sT = sS) (hgp : IsProjective g) (hgb : IsBirationalMorphism g) :
    {C : ProperCurve sS | C.IsContractedBy g}.Finite ∧
    relativeClosedConeOfCurves sS g =
      PointedCone.hull ℝ
        (Set.range fun C : {C : ProperCurve sS // C.IsContractedBy g} => C.1.relativeClass g C.2) ∧
    (∀ C : {C : ProperCurve sS // C.IsContractedBy g},
      IsExtremalRay ℝ (relativeClosedConeOfCurves sS g : Set (RelativeNumericalCurveClasses sS g))
        {w | ∃ c : ℝ, 0 ≤ c ∧ c • C.1.relativeClass g C.2 = w}) ∧
    LinearIndependent ℝ
      (fun C : {C : ProperCurve sS // C.IsContractedBy g} => C.1.relativeClass g C.2) := by
  classical
  have hSv : MMP.Mori.IsVariety k sS := hSq.toIsVariety
  have hTv : MMP.Mori.IsVariety k sT := hTq.toIsVariety
  haveI : IsIntegral S := hSv.toIsIntegral
  haveI : IsIntegral T := hTv.toIsIntegral
  haveI : QuasiCompact sS := hSv.toQuasiCompact
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  haveI : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  haveI : IsProper g := hgp.isProper
  have hgf := MMP.Threefold.Resolution.exists_isFinite_morphismRestrict_of_isBirationalMorphism hgb
  have hfin := MMP.Resolution.finite_setOf_isContractedBy hSv hSdim.le hgf
  have hTH : IsHQuasiProjective sT :=
    ((isQuasiProjectiveVariety_iff_isHQuasiProjective k sT).1 hTq).2
  obtain ⟨-, M, hMinv, hMamp⟩ := Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sT hTH
  have hproj : IsProjectiveMorphism g := isProjectiveMorphism_of_isProjective g M
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sT M hMamp) hgp
  obtain ⟨W, hW0, hWc, hWamp⟩ :=
    MMP.Threefold.Resolution.exists_isCartier_isRelativelyAmple_neg_of_isProjectiveMorphism
      hSv hTv hTH hproj hgf
  set ι := {C : ProperCurve sS // C.IsContractedBy g}
  haveI : Finite ι := hfin.to_subtype
  letI : Fintype ι := Fintype.ofFinite ι
  have hWneg : ∀ j : ι, W.degreeOn k sS j.1.ι j.1.dim_le hWc < 0 := fun j => by
    haveI := hWc.neg.isInvertibleModule_divisorialSheaf
    have : 0 < (-W).degreeOn k sS j.1.ι j.1.dim_le hWc.neg :=
      MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hSv g _ hWamp j.1 j.2
    rw [Divisor.degreeOn_neg' k sS j.1.ι j.1.dim_le W hWc] at this
    linarith
  choose P hPη using fun j : ι =>
    (⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (coheight_point_eq_one hSdim j.1),
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _⟩ :
      ∃ P : MMP.Mori.PrimeDivisor S, P.genericPoint = j.1.point)
  have hPinj : Function.Injective P := fun i j h =>
    Subtype.ext (ProperCurve.ext ((hPη i).symm.trans (h ▸ hPη j)))
  choose m hm hD using fun j => hS.2 (Finsupp.single (P j) 1)
  set v : ι → RelativeNumericalCurveClasses sS g := fun C => C.1.relativeClass g C.2 with hv
  let Φ : RelativeNumericalCurveClasses sS g →ₗ[ℝ] ι → ℝ := LinearMap.pi fun i =>
    haveI := (hD i).isInvertibleModule_divisorialSheaf
    RelativeNumericalCurveClasses.degree sS g (((m i : ℤ) • Finsupp.single (P i) 1 :
      Divisor S)).divisorialSheaf
  have hΦ : Continuous Φ := continuous_pi fun i => by
    haveI := (hD i).isInvertibleModule_divisorialSheaf
    exact RelativeNumericalCurveClasses.continuous_degree sS g _
  obtain ⟨Ψ, hΨ, hrec, hΨv⟩ := exists_leftInverse_of_det_ne_zero v
    (exists_sum_smul_relativeClass_eq g) Φ hΦ _
    (det_degreeOn_ne_zero (fun j : ι => j.1) P hPinj (fun j => (hPη j).symm) m hm hD hW0 hWc hWneg)
    fun j => by
      ext i
      simp only [Φ, LinearMap.pi_apply, Matrix.of_apply, hv, ProperCurve.relativeClass,
        RelativeNumericalCurveClasses.degree_relativeNumericalClass, OneCycle.degree_cycle]
      rfl
  obtain ⟨hcl, hext, hli⟩ := cone_facts_of_leftInverse v Ψ hΨ hrec hΨv
  have hNE : relativeClosedConeOfCurves sS g = PointedCone.hull ℝ (Set.range v) :=
    SetLike.coe_injective <| (coe_relativeClosedConeOfCurves sS g).trans hcl.closure_eq
  exact ⟨hfin, hNE, fun C => hNE ▸ hext C, hli⟩

end MMP.Mori
