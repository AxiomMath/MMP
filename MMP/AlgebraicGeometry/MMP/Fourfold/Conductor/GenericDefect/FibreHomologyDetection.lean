module

public import MMP.AlgebraicGeometry.Chow.CycleClassGenericPoint
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.VeryGeneralFibreLineBundles

/-!
# Restricted classes detect the second homology of a fibre

Let `r : Z ⟶ Y` be a curve-and-point exceptional model, `T ⊆ Sing Y` a curve with adapted open
`T₀`, and `F_t` the fibre of `r` over a point `t ∈ T₀(ℂ)`. A class `w ∈ H₂(F_t; ℚ)` with
`α|_{F_t} ∩ w = 0` in `H₀(F_t; ℚ)` for every class `α ∈ H²(r⁻¹(V); ℚ)` on a neighbourhood `V`
of `t` vanishes. Two facts give this:

* every class of `H²(F_t; ℚ)` is restricted from a tube `r⁻¹(V)`
  (`MMP.Fourfold.fibre_comparison`, for the proper map `r`);
* on a compact space `X`, with coefficients in a field `K`, the cap product pairing
  `H^n(X; K) × H_n(X; K) → H_0(X; K)` is nondegenerate in the homology argument (Kronecker
  duality): a cycle `z` which is not a boundary is a finite chain outside the finite boundaries,
  so a linear form `ψ` on finite `n`-chains kills the boundaries and not `z`; `ψ` is an
  `n`-cocycle, and the augmentation of `ψ ∩ z` is `ψ(z) ≠ 0`, so `ψ ∩ z` is not a boundary.

## Main results

* `MMP.Fourfold.eq_zero_of_forall_capProduct_eq_zero`: Kronecker duality for the cap product
  on a compact space.
* `MMP.Fourfold.IsCurvePointExceptionalModel.eq_zero_of_capProduct_restrict_eq_zero`: classes
  restricted from neighbourhoods of `F_t` detect `H₂(F_t; ℚ)`.

## Implementation notes

* On a compact space every locally finite chain is finite
  (`MMP.Fourfold.finite_support_coeff_of_compactSpace`), so Borel–Moore homology is computed by
  finite singular chains, where the augmentation is defined.
* The detection statement quantifies over the points `p` of `F_t`, as the pairing in
  `MMP.Fourfold.IsCurvePointExceptionalModel.injective_curveLocalSystemDual` does; a nonzero
  class lives on a nonempty fibre, which has a closed point.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.1 and §3.3.
* [B. Iversen, *Cohomology of sheaves*], VII.1 (proper base change).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace MMP.Fourfold

open MMP MMP.BorelMooreCap MMP.BorelMooreCross
  MMP.SingularChain MMP.SingularCochain MMP.LocallyFiniteChain MMP.borelMooreHomology

section Kronecker

variable {K : Type u} [Field K] {X : TopCat.{u}}

/-- On a compact space a locally finite chain has finite support. -/
theorem finite_support_coeff_of_compactSpace {R : Type u} [CommRing R] [CompactSpace X] {n : ℕ}
    (c : (BM R X).X n) : (Function.support (coeff R c)).Finite := by
  refine ((mem_lfChains.1 (coeff_mem R c)).finite_inter_compact isCompact_univ).subset
    fun σ hσ ↦ ⟨hσ, ?_⟩
  obtain ⟨x, hx⟩ := nonempty_singularSimplexImage σ
  exact ⟨x, hx, trivial⟩

/-- The augmentation of `φ ∩ c` for an `n`-cochain `φ` and a finite `n`-chain `c` is the
evaluation `φ(c)`. -/
theorem aug_capFin_eq_eval {n : ℕ} (h : n + 0 = n) (φ : Simplex X n → K) (c : Chain K X n) :
    aug K 0 (capFin K n 0 n h φ c) = SingularCochain.eval φ c := by
  have hb : back n n 0 (by omega) = id := funext fun j ↦ Fin.ext (by simp [back_val])
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add]
  | single σ a =>
    rw [capFin_single, aug_single, SingularCochain.eval, Finsupp.linearCombination_single,
      smul_eq_mul, hb, SingularChain.comp_smap_id]

/-- **Kronecker duality at the chain level.** On a compact space, an `m`-cycle `z` which is not
a boundary is detected by an `m`-cocycle `φ` with coefficients in a field: `φ ∩ z` is not a
boundary, because its augmentation is `φ(z) ≠ 0`. -/
theorem exists_coboundary_eq_zero_and_forall_d_ne_capChain [CompactSpace X] {m : ℕ} (z : Cyc (R := K) X m)
    (hz : z ∉ LinearMap.range ((BM K X).sc m).moduleCatToCycles) :
    ∃ φ : Simplex X m → K, coboundary K m φ = 0 ∧
      ∀ u : (BM K X).X 1, ((BM K X).d 1 0).hom u ≠ capChain K m 0 m (add_zero m) φ z.1 := by
  set f := toFinsupp z.1 (finite_support_coeff_of_compactSpace z.1)
  have hzf : ofFinsupp f = z.1 := ofFinsupp_toFinsupp _ _
  have hf : f ∉ LinearMap.range (bd K m) := by
    rintro ⟨g, hg⟩
    exact hz (mem_bdry_of z (ofFinsupp g) (by rw [d_ofFinsupp, hg, hzf]))
  obtain ⟨ψ, hψf, hψ⟩ := Submodule.exists_le_ker_of_notMem hf
  set φ : Simplex X m → K := fun σ ↦ ψ (Finsupp.single σ 1)
  have heval : ∀ c : Chain K X m, SingularCochain.eval φ c = ψ c := by
    intro c
    refine LinearMap.congr_fun (Finsupp.lhom_ext fun σ a ↦ ?_) c
    rw [SingularCochain.eval, Finsupp.linearCombination_single, smul_eq_mul, ← smul_eq_mul,
      ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine ⟨φ, ?_, fun u hu ↦ hψf ?_⟩
  · funext τ
    have h1 : coboundary K m φ τ =
        SingularCochain.eval (coboundary K m φ) (Finsupp.single τ 1) := by
      rw [SingularCochain.eval, Finsupp.linearCombination_single, one_smul]
    rw [h1, eval_coboundary, heval]
    exact hψ ⟨_, rfl⟩
  · set g := toFinsupp u (finite_support_coeff_of_compactSpace u)
    have hug : ofFinsupp g = u := ofFinsupp_toFinsupp _ _
    rw [← hug, ← hzf, d_ofFinsupp, ← ofFinsupp_capFin] at hu
    have := congrArg (aug K 0) (ofFinsupp_injective hu)
    rw [aug_bd_zero, aug_capFin_eq_eval, heval] at this
    exact this.symm

/-- A space with a nonzero Borel–Moore class is nonempty. -/
theorem nonempty_of_borelMooreHomology_ne_zero {R : Type u} [CommRing R] {n : ℕ}
    {w : borelMooreHomology R (ModuleCat.of R R) X n} (hw : w ≠ 0) : Nonempty X := by
  by_contra hX
  rw [not_nonempty_iff] at hX
  refine hw ((homologyEquiv R X n).injective ?_)
  rw [map_zero]
  generalize homologyEquiv R X n w = c
  induction c using Submodule.Quotient.induction_on with
  | H z =>
  have hz : z = 0 := Subtype.ext (coeff_injective R (funext fun σ ↦
    (hX.false (Set.range_nonempty (simplexEquiv X n σ)).some).elim))
  rw [hz]
  rfl

/-- **Kronecker duality on cycles modulo boundaries.** On a compact space, with coefficients in
a field, a class `c ∈ H_m` with `[φ] ∩ c = 0` for every `m`-cocycle `φ` is zero. -/
theorem eq_zero_of_forall_capHomQ_eq_zero [CompactSpace X] {A : Set X} (hA : A = ∅) (m q : ℕ)
    (h : m + q = m) (c : HomQ (R := K) X m)
    (hc : ∀ y : relCohomology K A m, capHomQ K A m q m h y c = 0) : c = 0 := by
  subst hA
  obtain rfl : q = 0 := by omega
  induction c using Submodule.Quotient.induction_on with
  | H z =>
  by_contra hz
  replace hz : z ∉ LinearMap.range ((BM K X).sc m).moduleCatToCycles :=
    fun h ↦ hz ((Submodule.Quotient.mk_eq_zero _).2 h)
  obtain ⟨φ, hφ, hne⟩ := exists_coboundary_eq_zero_and_forall_d_ne_capChain z hz
  have hφA : φ ∈ relCocycles K (∅ : Set X) m :=
    ⟨fun σ hσ ↦ absurd (Set.subset_empty_iff.1 hσ) (Set.range_nonempty σ).ne_empty, hφ⟩
  have := (capHomQ_mk (∅ : Set X) m 0 m h ⟨φ, hφA⟩ z).symm.trans
    (hc (Submodule.Quotient.mk ⟨φ, hφA⟩))
  obtain ⟨u, hu⟩ := exists_of_mem_bdry ((Submodule.Quotient.mk_eq_zero _).1 this)
  exact hne u hu

/-- **Kronecker duality for the cap product.** On a compact space, with coefficients in a
field `K`, a Borel–Moore class `w ∈ H_n(X; K)` with `x ∩ w = 0` in `H_0(X; K)` for every
`x ∈ H^n(X; K)` is zero. -/
theorem eq_zero_of_forall_capProduct_eq_zero [CompactSpace X] {n : ℕ}
    (w : borelMooreHomology K (ModuleCat.of K K) X n)
    (hw : ∀ x : cohomologyWithSupports K (ModuleCat.of K K) X Set.univ n,
      capProduct K X Set.univ n n x w = 0) : w = 0 := by
  have h : (0 : ℤ) ≤ n ∧ (n : ℤ) ≤ n := ⟨Int.natCast_nonneg n, le_rfl⟩
  have key := eq_zero_of_forall_capHomQ_eq_zero (K := K) Set.compl_univ (n : ℤ).toNat
    ((n : ℤ).toNat - (n : ℤ).toNat) (by omega)
    (((congrDegree K X (Int.toNat_of_nonneg (h.1.trans h.2)).symm).trans
      (homologyEquiv K X (n : ℤ).toNat)) w) fun y ↦ by
    have := hw (((cohomologyWithSupports.congrIndex K X rfl (Int.toNat_of_nonneg h.1).symm).trans
      (relativeSingularCohomologyEquiv K (Set.univ : Set X)ᶜ (n : ℤ).toNat)).symm y)
    simp only [borelMooreHomology.capProduct, h, and_self, dite_true] at this
    simpa using this
  simpa using key

end Kronecker

open AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Restricted classes detect `H₂(F_t; ℚ)`.** Let `r : Z ⟶ Y` be a curve-and-point exceptional
model, `T` a curve in `Sing Y` with adapted open `T₀`, and `t ∈ T₀(ℂ)`. A class
`w ∈ H₂(F_t; ℚ)` of the fibre `F_t` such that `α|_{F_t} ∩ w = 0` in `H₀(F_t; ℚ)` for every
class `α ∈ H²(r⁻¹(V); ℚ)` on a neighbourhood `V` of `t` (and every closed point `p` of `F_t`) is
zero. -/
theorem IsCurvePointExceptionalModel.eq_zero_of_capProduct_restrict_eq_zero
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D)
    (T₀ : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens)
    (T) (t : analyticSpace ((T₀ T).ι ≫ curveι T.1 ≫ sY))
    [IsComplexScheme (pointFibre sY r (T₀ T) t)]
    (w : MMP.Analytic.borelMooreHomology (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) (2 * 1))
    (hw : ∀ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY (T₀ T) t ∈ V)
      (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
      (p : pointFibre sY r (T₀ T) t)
      (hp : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) p = (0 : ℕ)),
      borelMooreHomology.capProduct ℚ
          (analyticSpace (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ))) Set.univ 2 2
          ((rationalCohomologyMap (pointFibreInclusion sY r (T₀ T) t hV) 2).hom α) w = 0) :
    w = 0 := by
  have : AlgebraicGeometry.IsVariety ℂ sY := hr.isProjectiveVariety.toIsVariety
  have : IsProper r := isProper_of_isProjectiveMorphism r hr.isResolution.2.2.2.1
  have H := IsPullback.of_hasPullback r (curveOpenInclusion sY (T₀ T) t).hom
  obtain ⟨hemb, hrange⟩ := isEmbedding_analyticMap_fibre r sY (curveOpenInclusion sY (T₀ T) t)
    (pointFibreFst sY r (T₀ T) t) (pointFibreSnd sY r (T₀ T) t) H
  have hK := (isProperMap_analyticMap r sY).isCompact_preimage
    (isCompact_singleton (x := curveOpenInclusion sY (T₀ T) t))
  rw [← hrange, ← Set.image_univ] at hK
  have : CompactSpace (analyticSpace (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ))) :=
    ⟨hemb.isCompact_iff.2 hK⟩
  by_contra hw0
  obtain ⟨x⟩ := nonempty_of_borelMooreHomology_ne_zero hw0
  have : IsSeparated (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))
  have : IsClosedImmersion x.hom := isClosedImmersion_of_comp_eq_id _ _ x.hom_comp_structure
  have hcl : IsClosed ({x.hom (IsLocalRing.closedPoint ℂ)} : Set (pointFibre sY r (T₀ T) t)) := by
    have h := x.hom.isClosedEmbedding.isClosedMap _ (IsLocalRing.isClosed_singleton_closedPoint ℂ)
    convert h using 1
    exact Set.image_singleton.symm
  refine hw0 (eq_zero_of_forall_capProduct_eq_zero (K := ℚ) w fun c ↦ ?_)
  obtain ⟨V, hV, α, hα⟩ := (fibre_comparison r sY (curveOpenInclusion sY (T₀ T) t)
    (pointFibreFst sY r (T₀ T) t) (pointFibreSnd sY r (T₀ T) t) H 2).1 c
  rw [← hα]
  exact hw V hV α _ (MMP.Chow.relativeDimension_eq_zero_of_isClosed ℂ hcl)

end MMP.Fourfold
