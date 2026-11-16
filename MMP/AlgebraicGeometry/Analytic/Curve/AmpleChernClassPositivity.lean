module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.SncFibreHomologyThree
public import MMP.AlgebraicTopology.FundamentalClass.Exists
public import MMP.AlgebraicTopology.BorelMoore.Suspension
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderSquare
public import MMP.AlgebraicTopology.BorelMoore.FiniteChains
public import MMP.AlgebraicTopology.PoincareDuality.TopDegree
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Vanishing.KodairaCharZero
public import MMP.AlgebraicGeometry.Chow.CycleClassGenericPoint
public import MMP.AlgebraicGeometry.SpecOverSpecSelf

/-!
# Positivity of an ample first Chern class on a fundamental cycle of a curve

Let `X` be a smooth projective complex curve and `z` a finite singular `2`-cycle of `X^an` with
complex coefficients whose homology class is the fundamental class `[X]` (Fulton, §19.1). For an
invertible module `L` and any singular cocycle `χ` representing the image of `c₁(L)` in
`H²(X^an; ℂ)`, the evaluation `⟨χ, z⟩ = ∑_σ z_σ χ(σ)` is the degree of `L`. In particular it is a
positive real number when `L` is ample.

**Proof.** Over `ℚ`, the fundamental class of `X` is the class of a finite rational cycle `w`
(`X(ℂ)` is compact), and Fulton's degree formula `p_*(c₁(L) ∩ [X]) = deg L · [pt]` reads, at the
level of chains, `⟨φ, w⟩ = deg L` for an integral cocycle `φ` of `c₁(L)`: the push-forward to the
point of the cap product of a `2`-cocycle with a finite `2`-cycle is the class of the point times
the evaluation. Over `ℂ`, the complexification `w_ℂ` of `w` is again a fundamental class, since
its local pairings with complex relative cocycles are detected by the `ℚ`-linear functionals
`ℂ → ℚ`; by uniqueness of the fundamental class, `[z] = [w_ℂ]`, and the same chain-level
computation gives `⟨χ, z⟩ = ⟨φ, w_ℂ⟩ = deg L`.

## Main definitions

* `MMP.Analytic.PolarizationPositivity.finiteCycleClass`: the Borel–Moore class of a finite
  singular cycle.

## Main results

* `MMP.Analytic.PolarizationPositivity.pushforward_capProduct_finiteCycleClass`: the push-forward
  to a point of `c ∩ [w]`, for `c` a class of degree `2` and `w` a finite `2`-cycle, is `⟨φ, w⟩`
  times the class of the point.
* `MMP.Analytic.PolarizationPositivity.isVarietyFundamentalClass_mapRange_ratCast`: the
  complexification of a rational fundamental cycle of a curve is a complex fundamental cycle.
* `MMP.Analytic.PolarizationPositivity.eval_eq_invertibleCurveDegree`: `⟨χ, z⟩ = deg L`.
* `MMP.Analytic.PolarizationPositivity.exists_pos_eval_eq_of_isAmple`: `⟨χ, z⟩` is a positive
  real number for `L` ample.

## Implementation notes

The fundamental class is Fulton's `IsVarietyFundamentalClass` on `X(ℂ)`; the cycle `z` lives on
`X^an`, and its class is taken after transport along the homeomorphism `X^an ≅ X(ℂ)`. Cycles have
degree `1 + 1`, the degree in which singular cocycles of `X^an` are written.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Simplicial MMP
open MMP.Intersection.Scheme (dimension)
open MMP.SingularChain MMP.SingularCochain
open MMP.BorelMooreCross MMP.borelMooreHomology
open MMP.FundamentalClass MMP.LocallyFiniteChain
open MMP.UnderlyingSpace MMP.SingularCross

namespace MMP.Analytic.PolarizationPositivity

section FiniteCycles

variable {R : Type} [CommRing R] {Y : TopCat.{0}}

/-- A finite chain with zero boundary is a locally finite cycle. -/
theorem ofFinsupp_mem_cyc {k : ℕ} (c : Chain R Y (k + 1)) (hc : bd R k c = 0) :
    ofFinsupp c ∈ Cyc (R := R) Y (k + 1) := by
  rw [mem_cyc_iff, Nat.add_sub_cancel, d_ofFinsupp, hc]
  rfl

/-- The Borel–Moore class `[c] ∈ H_{k+1}(Y)` of a finite singular cycle `c`. -/
def finiteCycleClass {k : ℕ} (c : Chain R Y (k + 1)) (hc : bd R k c = 0) :
    MMP.borelMooreHomology R (ModuleCat.of R R) Y ((k + 1 : ℕ) : ℤ) :=
  (homologyEquiv R Y (k + 1)).symm
    (Submodule.Quotient.mk ⟨ofFinsupp c, ofFinsupp_mem_cyc c hc⟩)

/-- On a compact space every Borel–Moore class is the class of a finite cycle. -/
theorem exists_finiteCycleClass_eq [CompactSpace Y] {k : ℕ}
    (μ : MMP.borelMooreHomology R (ModuleCat.of R R) Y ((k + 1 : ℕ) : ℤ)) :
    ∃ (c : Chain R Y (k + 1)) (hc : bd R k c = 0), finiteCycleClass c hc = μ := by
  obtain ⟨ζ₀, hζ⟩ := Submodule.Quotient.mk_surjective _ (homologyEquiv R Y (k + 1) μ)
  let ζ : Cyc (R := R) Y (k + 1) := ζ₀
  have hfin : (Function.support ζ.1.1).Finite := by
    have h := (coeff_mem R ζ.1).finite_inter_compact (K := Set.univ) isCompact_univ
    refine h.subset fun σ hσ ↦ ⟨hσ, ?_⟩
    obtain ⟨y, hy⟩ := nonempty_singularSimplexImage σ
    exact ⟨y, hy, trivial⟩
  have hc : bd R k (toFinsupp ζ.1 hfin) = 0 := by
    have h1 := d_ofFinsupp (R := R) (toFinsupp ζ.1 hfin)
    rw [show ofFinsupp (toFinsupp ζ.1 hfin) = ζ.1 from ofFinsupp_toFinsupp _ _] at h1
    have h2 : ((BM R Y).d (k + 1) k).hom ζ.1 = 0 := by
      have := (mem_cyc_iff ζ.1).1 ζ.2
      rwa [Nat.add_sub_cancel] at this
    rw [h2] at h1
    ext σ
    have := congrArg (fun x ↦ x.1 ((SingularCochain.simplexEquiv Y _).symm σ)) h1
    simp only [ofFinsupp_apply, Equiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨toFinsupp ζ.1 hfin, hc, ?_⟩
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  rw [← hζ]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (ofFinsupp_toFinsupp _ _))

end FiniteCycles

section Kronecker

open MMP.BorelMooreCap MMP.SingularCross

variable {R : Type} [CommRing R]

/-- The cap product of an `n`-cochain `φ` with a finite `n`-chain `w` is a finite `0`-chain
whose coefficients sum to `⟨φ, w⟩`. -/
theorem finsum_coeff_capChain_ofFinsupp {Y : TopCat.{0}} {n : ℕ} (φ : Simplex Y n → R)
    (w : Chain R Y n) :
    (Function.support (coeff R (capChain R n 0 n (add_zero n) φ (ofFinsupp w)))).Finite ∧
      ∑ᶠ τ, coeff R (capChain R n 0 n (add_zero n) φ (ofFinsupp w)) τ = eval φ w := by
  have hw : (Function.support (coeff R (ofFinsupp w))).Finite := by
    refine ((w.support.finite_toSet).preimage
      (SingularCochain.simplexEquiv Y _).injective.injOn).subset fun σ hσ ↦ ?_
    rw [Function.mem_support] at hσ
    exact Finsupp.mem_support_iff.2 hσ
  have hg : (Function.support fun σ ↦
      wt φ (back n n 0 (by omega)) σ * coeff R (ofFinsupp w) σ).Finite :=
    hw.subset fun σ hσ ↦ by
      rw [Function.mem_support] at hσ ⊢
      exact right_ne_zero_of_mul hσ
  have e : coeff R (capChain R n 0 n (add_zero n) φ (ofFinsupp w)) =
      pushforwardFun (opS (front 0 n (by omega)))
        (fun σ ↦ wt φ (back n n 0 (by omega)) σ * coeff R (ofFinsupp w) σ) := rfl
  refine ⟨e ▸ support_pushforwardFun_finite _ _ hg, ?_⟩
  rw [e, finsum_pushforwardFun _ _ hg, ← PoincareDuality.localPairing_ofFinsupp, localPairing]
  exact finsum_congr fun σ ↦ by rw [wt_back_self, mul_comm]; rfl

/-- Two transports of degree compose. -/
theorem congrDegree_apply_congrDegree {X : TopCat.{0}} {i j k : ℤ} (h : i = j) (h' : j = k)
    (v : MMP.borelMooreHomology R (ModuleCat.of R R) X i) :
    congrDegree R X h' (congrDegree R X h v) = congrDegree R X (h.trans h') v := by
  subst h h'
  rfl

/-- **The cap product into a point is the evaluation.** For a proper map `p` from `Y` to a space
with at most one point, a class `c` of degree `2` represented by the relative cocycle `φ` and a
finite `2`-cycle `w`, `p_*(c ∩ [w]) = ⟨φ, w⟩ · [d]` for every `0`-cycle `d` with coefficient `1`
on the point. -/
theorem pushforward_capProduct_finiteCycleClass {Y P : TopCat.{0}} [Subsingleton P]
    (p : Y ⟶ P) (hp : IsProperMap p) (A : Set Y)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y A ((2 : ℕ) : ℤ))
    (φ : Simplex Y 2 → R) (hφ : φ ∈ relCocycles R Aᶜ 2)
    (hcφ : relativeSingularCohomologyEquiv R Aᶜ 2 c = Submodule.Quotient.mk ⟨φ, hφ⟩)
    (w : Chain R Y (1 + 1)) (hw : bd R 1 w = 0)
    (d : Cyc (R := R) P 0) (τ : Simp P 0) (hd : coeff R d.1 τ = 1) :
    (pushforward R (ModuleCat.of R R) p hp ((0 : ℕ) : ℤ)).hom
      (congrDegree R Y (by norm_num : ((1 + 1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ) = ((0 : ℕ) : ℤ))
        (capProduct R Y A ((2 : ℕ) : ℤ) ((1 + 1 : ℕ) : ℤ) c (finiteCycleClass w hw))) =
      eval φ w • (homologyEquiv R P 0).symm (Submodule.Quotient.mk d) := by
  have hb : homologyEquiv R Y (1 + 1) (finiteCycleClass w hw) =
      Submodule.Quotient.mk ⟨ofFinsupp w, ofFinsupp_mem_cyc w hw⟩ :=
    LinearEquiv.apply_symm_apply _ _
  have hcap : capHomQ R Aᶜ 2 (1 + 1 - 2) (1 + 1) (by omega) (Submodule.Quotient.mk ⟨φ, hφ⟩)
      (homologyEquiv R Y (1 + 1) (finiteCycleClass w hw)) =
      Submodule.Quotient.mk ⟨capChain R 2 (1 + 1 - 2) (1 + 1) (by omega) φ (ofFinsupp w),
        capChain_mem_cyc Aᶜ 2 (1 + 1 - 2) (1 + 1) (by omega) ⟨φ, hφ⟩
          ⟨ofFinsupp w, ofFinsupp_mem_cyc w hw⟩⟩ := by
    rw [hb]
    exact capHomQ_mk _ _ _ _ _ _ _
  rw [capProduct_natCast Y A (by norm_num : 2 ≤ 1 + 1) c, hcφ, hcap, congrDegree_apply_congrDegree]
  have e0 : ∀ (h : (((1 + 1 - 2 : ℕ) : ℤ)) = ((0 : ℕ) : ℤ))
      (v : MMP.borelMooreHomology R (ModuleCat.of R R) Y ((1 + 1 - 2 : ℕ) : ℤ)),
      congrDegree R Y h v = v := fun _ _ ↦ rfl
  rw [e0, pushforward_eq_homologyMap]
  erw [homologyMap_homologyEquiv_symm_mk]
  refine (congrArg (homologyEquiv R P 0).symm ?_).trans
    (map_smul (homologyEquiv R P 0).symm _ _)
  refine (congrArg Submodule.Quotient.mk ?_).trans (Submodule.Quotient.mk_smul _ _ _)
  apply Subtype.ext
  apply coeff_injective R
  have hS : ∀ σ : Simp P 0, σ = τ := fun σ ↦
    (P.toSSetObjEquiv _).injective (ContinuousMap.ext fun _ ↦ Subsingleton.elim _ _)
  funext σ
  rw [hS σ]
  obtain ⟨h1, h2⟩ := finsum_coeff_capChain_ofFinsupp φ w
  obtain ⟨-, h3⟩ := finsum_coeff_chainMap p hp _ h1
  have key : ∑ᶠ σ, coeff R (((chainMap R (ModuleCat.of R R) p hp).f 0).hom
      (capChain R 2 0 2 (add_zero 2) φ (ofFinsupp w))) σ = eval φ w := h3.trans h2
  refine (finsum_eq_single _ τ (fun σ hσ ↦ absurd (hS σ) hσ)).symm.trans ?_
  refine key.trans ?_
  change _ = coeff R (eval φ w • d.1) τ
  rw [coeff_smul, Pi.smul_apply, hd, smul_eq_mul, mul_one]

/-- Two finite `2`-cycles with the same class, pushed forward properly to a point, have the same
evaluation on any two cocycles representing one class. -/
theorem eval_eq_of_finiteCycleClass_eq {Y P : TopCat.{0}} [Subsingleton P]
    (p : Y ⟶ P) (hp : IsProperMap p) {A : Set Y}
    {c : cohomologyWithSupports R (ModuleCat.of R R) Y A ((2 : ℕ) : ℤ)}
    {φ ψ : Simplex Y 2 → R} {hφ : φ ∈ relCocycles R Aᶜ 2} {hψ : ψ ∈ relCocycles R Aᶜ 2}
    (hcφ : relativeSingularCohomologyEquiv R Aᶜ 2 c = Submodule.Quotient.mk ⟨φ, hφ⟩)
    (hcψ : relativeSingularCohomologyEquiv R Aᶜ 2 c = Submodule.Quotient.mk ⟨ψ, hψ⟩)
    {w w' : Chain R Y (1 + 1)} {hw : bd R 1 w = 0} {hw' : bd R 1 w' = 0}
    (hww' : finiteCycleClass w hw = finiteCycleClass w' hw')
    (d : Cyc (R := R) P 0) (τ : Simp P 0) (hd : coeff R d.1 τ = 1)
    (hinj : Function.Injective fun r : R ↦
      r • (homologyEquiv R P 0).symm (Submodule.Quotient.mk d)) :
    eval φ w = eval ψ w' :=
  hinj <| (pushforward_capProduct_finiteCycleClass p hp A c φ hφ hcφ w hw d τ hd).symm.trans <|
    hww' ▸ pushforward_capProduct_finiteCycleClass p hp A c ψ hψ hcψ w' hw' d τ hd

end Kronecker

section Complexify

/-- The boundary commutes with the change of coefficients `ℚ → ℂ`. -/
theorem bd_mapRange_ratCast {Y : Type*} [TopologicalSpace Y] (k : ℕ) (w : Chain ℚ Y (k + 1)) :
    bd ℂ k (w.mapRange (fun q : ℚ ↦ (q : ℂ)) Rat.cast_zero) =
      (bd ℚ k w).mapRange (fun q : ℚ ↦ (q : ℂ)) Rat.cast_zero := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [Finsupp.mapRange_add (fun x y ↦ Rat.cast_add x y), map_add, ha, hb, map_add,
      Finsupp.mapRange_add (fun x y ↦ Rat.cast_add x y)]
  | single σ a =>
    ext τ
    simp [bd, Finsupp.linearCombination_single, Finsupp.finset_sum_apply]
    left
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h : σ.comp (face k i) = τ
    · subst h
      simp
    · simp [Finsupp.single_apply, h]

/-- A `ℚ`-linear functional `ℓ : ℂ → ℚ` carries `⟨φ, w_ℂ⟩` to `⟨ℓ ∘ φ, w⟩`. -/
theorem eval_mapRange_ratCast {Y : Type*} [TopologicalSpace Y] {n : ℕ} (φ : Simplex Y n → ℂ)
    (w : Chain ℚ Y n) (ℓ : ℂ →ₗ[ℚ] ℚ) :
    ℓ (eval φ (w.mapRange (fun q : ℚ ↦ (q : ℂ)) Rat.cast_zero)) = eval (fun σ ↦ ℓ (φ σ)) w := by
  simp only [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapRange_index (fun σ ↦ zero_smul ℂ (φ σ)), map_finsuppSum]
  refine Finsupp.sum_congr fun σ _ ↦ ?_
  rw [smul_eq_mul, smul_eq_mul, ← smul_eq_mul (a := (w σ : ℂ)), Rat.cast_smul_eq_qsmul, map_smul,
    smul_eq_mul]

/-- The composite of a complex relative cocycle with a `ℚ`-linear functional `ℂ → ℚ` is a
rational relative cocycle. -/
theorem mem_relCocycles_comp {Y : Type*} [TopologicalSpace Y] {A : Set Y} {n : ℕ}
    {φ : Simplex Y n → ℂ} (hφ : φ ∈ relCocycles ℂ A n) (ℓ : ℂ →ₗ[ℚ] ℚ) :
    (fun σ ↦ ℓ (φ σ)) ∈ relCocycles ℚ A n := by
  refine ⟨fun σ hσ ↦ by simp [hφ.1 σ hσ], ?_⟩
  change coboundary ℚ n _ = 0
  funext σ
  have := congrFun (show coboundary ℂ n φ = 0 from hφ.2) σ
  rw [coboundary_apply] at this ⊢
  simp only [Pi.zero_apply] at this ⊢
  have e := congrArg ℓ this
  rw [map_sum, map_zero] at e
  rw [← e]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases Nat.even_or_odd (i : ℕ) with h | h <;> simp [h.neg_one_pow]

/-- The finite cycle `c`, as a cycle of the complex of locally finite chains, represents
`finiteCycleClass c`. -/
theorem homologyπ_finiteCycleClass {R : Type} [CommRing R] {Y : TopCat.{0}} {k : ℕ}
    (c : Chain R Y (k + 1)) (hc : bd R k c = 0) :
    (borelMooreChainComplex R (ModuleCat.of R R) Y).homologyπ (k + 1)
        (((borelMooreChainComplex R (ModuleCat.of R R) Y).sc (k + 1)).moduleCatCyclesIso.inv.hom
          ⟨ofFinsupp c, ofFinsupp_mem_cyc c hc⟩) =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) Y (k + 1)).hom (finiteCycleClass c hc) := by
  rw [finiteCycleClass]
  erw [homologyEquiv_symm_mk_eq]
  exact (ConcreteCategory.congr_hom
    (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) Y (k + 1)).inv_hom_id _).symm

/-- If the class of a finite cycle `c` is locally the class of `Δ` at `x`, then `⟨φ, c⟩ = φ(Δ)`
for every relative cocycle `φ` of `(Y, Y - x)`. -/
theorem localPairing_of_isLocallyClassOf_finiteCycleClass {R : Type} [CommRing R]
    {Y : TopCat.{0}} {k : ℕ} {c : Chain R Y (k + 1)} {hc : bd R k c = 0} {x : Y}
    {Δ : Simplex Y (k + 1)} (h : IsLocallyClassOf R (finiteCycleClass c hc) x Δ)
    {φ : Simplex Y (k + 1) → R} (hφ : φ ∈ relCocycles R ({x}ᶜ : Set Y) (k + 1)) :
    eval φ c = φ Δ := by
  have h1 := h _ (homologyπ_finiteCycleClass c hc) φ hφ
  erw [iCycles_moduleCatCyclesIso_inv, PoincareDuality.localPairing_ofFinsupp] at h1
  exact h1

/-- The class of a finite cycle `c` is locally the class of `Δ` at `x` as soon as
`⟨φ, c⟩ = φ(Δ)` for every relative cocycle `φ` of `(Y, Y - x)`. -/
theorem isLocallyClassOf_finiteCycleClass_of_eval {R : Type} [CommRing R]
    {Y : TopCat.{0}} {k : ℕ} {c : Chain R Y (k + 1)} {hc : bd R k c = 0} {x : Y}
    {Δ : Simplex Y (k + 1)}
    (h : ∀ φ ∈ relCocycles R ({x}ᶜ : Set Y) (k + 1), eval φ c = φ Δ) :
    IsLocallyClassOf R (finiteCycleClass c hc) x Δ := by
  intro z hz φ hφ
  rw [localPairing_eq_of_homologyπ_eq (hz.trans (homologyπ_finiteCycleClass c hc).symm) hφ]
  erw [iCycles_moduleCatCyclesIso_inv, PoincareDuality.localPairing_ofFinsupp]
  exact h φ hφ

/-- If the class of a finite rational cycle `w` is locally the class of `Δ` at `x`, so is the
class of its complexification `w_ℂ`. -/
theorem IsLocallyClassOf.mapRange_ratCast {Y : TopCat.{0}} {k : ℕ} {w : Chain ℚ Y (k + 1)}
    {hw : bd ℚ k w = 0} {x : Y} {Δ : Simplex Y (k + 1)}
    (h : IsLocallyClassOf ℚ (finiteCycleClass w hw) x Δ) :
    IsLocallyClassOf ℂ (finiteCycleClass (w.mapRange (fun q : ℚ ↦ (q : ℂ)) Rat.cast_zero)
      (by rw [bd_mapRange_ratCast, hw, Finsupp.mapRange_zero])) x Δ := by
  refine isLocallyClassOf_finiteCycleClass_of_eval fun φ hφ ↦ ?_
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℚ _).1 fun ℓ ↦ ?_)
  rw [map_sub, sub_eq_zero, eval_mapRange_ratCast]
  exact localPairing_of_isLocallyClassOf_finiteCycleClass h (mem_relCocycles_comp hφ ℓ)

end Complexify

section Variety

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V]
  [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))]

/-- **Complexification of a fundamental cycle.** If the class of a finite rational `2`-cycle `w`
of a complex curve `V` is its fundamental class, so is the class of `w_ℂ` over `ℂ`. -/
theorem isVarietyFundamentalClass_mapRange_ratCast
    {hn : ((1 : ℕ) : WithBot ℕ∞) = dimension V}
    {w : Chain ℚ (TopCat.of (UnderlyingSpace ℂ V)) (1 + 1)} {hw : bd ℚ 1 w = 0}
    (h : IsVarietyFundamentalClass ℚ hn (finiteCycleClass w hw)) :
    IsVarietyFundamentalClass ℂ hn
      (finiteCycleClass (w.mapRange (fun q : ℚ ↦ (q : ℂ)) Rat.cast_zero)
        (by rw [bd_mapRange_ratCast, hw, Finsupp.mapRange_zero])) := by
  letI := regularChartedSpace (𝕜 := ℂ) hn
  intro e he x v hv hvt
  have h1 := h e he x v hv hvt
  haveI : T2Space (TopCat.of (regularOpens ℂ V)) := inferInstanceAs (T2Space (regularOpens ℂ V))
  haveI : T2Space (TopCat.of (UnderlyingSpace ℂ V)) :=
    inferInstanceAs (T2Space (UnderlyingSpace ℂ V))
  have h2 := IsLocallyClassOf.of_restrict (chartOpens e) h1
  have h3 := IsLocallyClassOf.of_restrict _ h2
  have h4 := IsLocallyClassOf.mapRange_ratCast h3
  exact IsLocallyClassOf.restrict _ (IsLocallyClassOf.restrict _ h4)

/-- On a complex variety with one point, the fundamental class is the class of any `0`-cycle
with coefficient `1` on the point. -/
theorem eq_homologyEquiv_symm_mk_of_isVarietyFundamentalClass_zero {R : Type} [CommRing R]
    [Subsingleton (UnderlyingSpace ℂ V)] [Nonempty (UnderlyingSpace ℂ V)]
    {hn : ((0 : ℕ) : WithBot ℕ∞) = dimension V}
    {c : MMP.borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ V)) ((2 * 0 : ℕ) : ℤ)}
    (hc : IsVarietyFundamentalClass R hn c)
    (d : Cyc (R := R) (TopCat.of (UnderlyingSpace ℂ V)) 0)
    (τ : Simp (TopCat.of (UnderlyingSpace ℂ V)) 0) (hd : coeff R d.1 τ = 1) :
    c = (homologyEquiv R (TopCat.of (UnderlyingSpace ℂ V)) 0).symm
      (Submodule.Quotient.mk d) := by
  letI := regularChartedSpace (𝕜 := ℂ) hn
  obtain ⟨x, hx⟩ := (UnderlyingSpace.dense_regularPart (X := V)).nonempty
  let x' : regularOpens ℂ V := ⟨x, hx⟩
  obtain ⟨e, he, hxe⟩ : ∃ e ∈ atlas (EuclideanSpace ℂ (Fin 0)) (regularOpens ℂ V),
      x' ∈ e.source :=
    ⟨_, chart_mem_atlas (EuclideanSpace ℂ (Fin 0)) x',
      mem_chart_source (EuclideanSpace ℂ (Fin 0)) x'⟩
  obtain ⟨v, hv, hvt⟩ := ThomClass.exists_isOrientedSimplexAroundZero_subset
    (euclideanComplexOrientationBasis 0) (e x')
    (e.open_target.mem_nhds (e.map_source hxe))
  have h1 := hc e he ⟨x', hxe⟩ v hv hvt
  haveI : T2Space (TopCat.of (regularOpens ℂ V)) := inferInstanceAs (T2Space (regularOpens ℂ V))
  haveI : T2Space (TopCat.of (UnderlyingSpace ℂ V)) :=
    inferInstanceAs (T2Space (UnderlyingSpace ℂ V))
  have h2 := IsLocallyClassOf.of_restrict (chartOpens e) h1
  have h3 := IsLocallyClassOf.of_restrict _ h2
  haveI : Subsingleton (TopCat.of (UnderlyingSpace ℂ V)) :=
    inferInstanceAs (Subsingleton (UnderlyingSpace ℂ V))
  exact eq_homologyEquiv_symm_mk_of_isLocallyClassOf R h3 τ d hd

end Variety

section Cochains

/-- The pull-back of the class of a cocycle `φ` is the class of `g^* φ`. -/
theorem relativeSingularCohomologyEquiv_pullback_ofCocycle {R : Type} [CommRing R]
    {Y' Y : TopCat.{0}} (g : Y' ⟶ Y) (n : ℕ) (φ : Simplex Y n → R)
    (hφ : φ ∈ relCocycles R (Set.univᶜ : Set Y) n) :
    relativeSingularCohomologyEquiv R (g ⁻¹' Set.univ)ᶜ n
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g Set.univ n).hom
          (cohomologyWithSupports.ofCocycle R Y n φ hφ)) =
      Submodule.Quotient.mk ⟨cochainPullback R g n φ,
        cochainPullback_mem_relCocycles g (fun _ hx ↦ hx) hφ⟩ := by
  rw [cohomologyWithSupports.pullback]
  erw [relativeSingularCohomologyEquiv_map]
  rw [cohomologyWithSupports.ofCocycle, LinearEquiv.apply_symm_apply]
  rfl

/-- Every `0`-simplex is the support of a `0`-cycle with coefficient `1`. -/
theorem exists_cyc_coeff_eq_one (R : Type) [CommRing R] {P : TopCat.{0}} (τ : Simp P 0) :
    ∃ d : Cyc (R := R) P 0, coeff R d.1 τ = 1 :=
  ⟨⟨FundamentalClass.singleChain R τ, by
    rw [mem_cyc_iff, (BM R P).shape 0 (0 - 1) (by simp)]
    rfl⟩, by simp [coeff, FundamentalClass.singleChain]⟩

/-- Evaluation on a push-forward of chains is evaluation of the pulled-back cochain. -/
theorem eval_postcomp {R : Type} [CommRing R] {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(Y, Z)) {n : ℕ} (φ : Simplex Z n → R) (c : Chain R Y n) :
    eval φ (postcomp R f n c) = eval (fun σ ↦ φ (f.comp σ)) c := by
  simp only [postcomp, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  rfl

/-- Evaluation of an integral cochain on the complexification of a rational chain is the image
in `ℂ` of the rational evaluation. -/
theorem eval_mapRange_intCast_ratCast {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (φ : Simplex Y n → ℤ) (w : Chain ℚ Y n) :
    eval (fun σ ↦ ((φ σ : ℤ) : ℂ)) (w.mapRange (fun q : ℚ ↦ (q : ℂ)) Rat.cast_zero) =
      ((eval (fun σ ↦ ((φ σ : ℤ) : ℚ)) w : ℚ) : ℂ) := by
  simp only [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapRange_index (fun σ ↦ zero_smul ℂ ((φ σ : ℤ) : ℂ)), Finsupp.sum,
    Finsupp.sum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp

end Cochains

section Curve

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))]

/-- A scheme of Krull dimension one has dimension `1`. -/
theorem natCast_one_eq_dimension (hdim1 : topologicalKrullDim X = 1) :
    ((1 : ℕ) : WithBot ℕ∞) = dimension X := by
  rw [dimension, hdim1]
  rfl

/-- The transport to `X(ℂ)` of a cycle of `X^an` is a cycle. -/
theorem bd_postcomp_homeomorphUnderlyingSpace_eq_zero
    {z : Chain ℂ (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1)} (hz : bd ℂ 1 z = 0) :
    bd ℂ 1 (postcomp ℂ ⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := X)).continuous⟩
      (1 + 1) z) = 0 := by
  rw [← postcomp_bd, hz, map_zero]

/-- The complex points of `Spec ℂ` form a single point. -/
instance subsingleton_underlyingSpace_spec : Subsingleton (UnderlyingSpace ℂ (Spec (.of ℂ))) :=
  ⟨fun p q ↦ UnderlyingSpace.ext (by
    have hp := p.toHom_comp_over
    have hq := q.toHom_comp_over
    rw [MMP.specOverSpec_over_self, Category.comp_id] at hp hq
    rw [hp, hq])⟩

/-- The identity of `Spec ℂ` is a complex point. -/
instance nonempty_underlyingSpace_spec : Nonempty (UnderlyingSpace ℂ (Spec (.of ℂ))) :=
  ⟨⟨𝟙 _, by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩⟩

/-- The point `Spec ℂ` has dimension `0`. -/
theorem natCast_zero_eq_dimension_spec : ((0 : ℕ) : WithBot ℕ∞) = dimension (Spec (.of ℂ)) := by
  change _ = topologicalKrullDim (PrimeSpectrum ℂ)
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  rfl

/-- **The rational degree computation.** On a smooth projective complex curve `X`, the rational
fundamental class is the class of a finite `2`-cycle `w` of `X(ℂ)`, and an integral cocycle `φ`
of `X^an` representing `c₁(L)` takes the value `deg L` on `w`. -/
theorem exists_finiteCycleClass_eval_eq_invertibleCurveDegree [IsProper (X ↘ Spec (.of ℂ))]
    (hsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) (hdim1 : topologicalKrullDim X = 1)
    (hproj : MMP.Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (φ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) 2 → ℤ)
    (hφ : φ ∈ relCocycles ℤ (Set.univᶜ : Set (Analytification.space (X ↘ Spec (.of ℂ)))) 2)
    (hφc : cohomologyWithSupports.ofCocycle ℤ _ 2 φ hφ = algebraicFirstChernClass L) :
    ∃ (w : Chain ℚ (TopCat.of (UnderlyingSpace ℂ X)) (1 + 1)) (hw : bd ℚ 1 w = 0),
      IsVarietyFundamentalClass ℚ (natCast_one_eq_dimension hdim1) (finiteCycleClass w hw) ∧
      eval (cochainPullback ℚ (TopCat.ofHom
          ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩ :
            TopCat.of (UnderlyingSpace ℂ X) ⟶ Analytification.space (X ↘ Spec (.of ℂ))) 2
          (singularCohomology.cochainMap (Int.castRingHom ℚ) 2 φ)) w =
        (invertibleCurveDegree ℂ (X ↘ Spec (.of ℂ)) hdim1.le L : ℚ) := by
  classical
  have hn := natCast_one_eq_dimension (X := X) hdim1
  let U : TopCat.{0} := TopCat.of (UnderlyingSpace ℂ X)
  let g : U ⟶ Analytification.space (X ↘ Spec (.of ℂ)) :=
    TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩
  haveI : (X ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) :=
    ⟨by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩
  let P : TopCat.{0} := TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ)))
  let p : U ⟶ P := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (X ↘ Spec (.of ℂ)))
  have hp : IsProperMap p := UnderlyingSpace.isProperMap_map (K := ℂ) _
  haveI : Subsingleton P := inferInstanceAs (Subsingleton (UnderlyingSpace ℂ (Spec (.of ℂ))))
  haveI : CompactSpace U := ⟨by simpa using hp.isCompact_preimage (isCompact_univ (X := P))⟩
  let τ : Simp P 0 := (P.toSSetObjEquiv _).symm
    (ContinuousMap.const _ (Classical.arbitrary (UnderlyingSpace ℂ (Spec (.of ℂ)))))
  have hn0 := natCast_zero_eq_dimension_spec
  obtain ⟨cWℚ, hcWℚ, -, hbijℚ⟩ := existsUnique_isVarietyFundamentalClass ℚ hn0
  obtain ⟨dℚ, hdℚ⟩ := exists_cyc_coeff_eq_one ℚ τ
  have hptℚ := eq_homologyEquiv_symm_mk_of_isVarietyFundamentalClass_zero hcWℚ dℚ τ hdℚ
  let p0 : Spec (.of ℂ) := Classical.choice inferInstance
  have hrpt := Chow.pointCycleClass_eq_of_closure_eq_univ p0
    (MMP.Fourfold.relativeDimension_spec_eq_zero p0)
    (Set.eq_univ_of_forall fun q ↦ by
      rw [Subsingleton.elim q p0]
      exact subset_closure rfl) hn0 hcWℚ
  have hξ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) (genericPoint X) = ((1 : ℕ) : ℤ) :=
    Chow.relativeDimension_genericPoint_eq ℂ _ (by rw [hdim1]; rfl)
  obtain ⟨cXℚ, hcXℚ, -, -⟩ := existsUnique_isVarietyFundamentalClass ℚ hn
  have hμ := Chow.pointCycleClass_eq_of_closure_eq_univ (genericPoint X) hξ
    (genericPoint_spec X).def hn hcXℚ
  obtain ⟨w, hw, hwμ⟩ := exists_finiteCycleClass_eq (R := ℚ) (Y := U) (k := 1) cXℚ
  have hc1ℚ : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L) =
      cohomologyWithSupports.ofCocycle ℚ _ 2
        (singularCohomology.cochainMap (Int.castRingHom ℚ) 2 φ)
        (singularCohomology.cochainMap_mem_relCocycles _ hφ) := by
    rw [← hφc, singularCohomology.mapCoeff_ofCocycle]
  have hdegℚ := MMP.Fourfold.pushforward_capProductPullback_eq_invertibleCurveDegree_smul hsm
    hdim1 hproj L (genericPoint X) hξ p0
  rw [hμ, ← hwμ, hrpt, hptℚ, hc1ℚ] at hdegℚ
  have hKℚ := pushforward_capProduct_finiteCycleClass p hp (g ⁻¹' Set.univ)
    ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g Set.univ 2).hom
      (cohomologyWithSupports.ofCocycle ℚ _ 2
        (singularCohomology.cochainMap (Int.castRingHom ℚ) 2 φ)
        (singularCohomology.cochainMap_mem_relCocycles _ hφ)))
    _ _ (relativeSingularCohomologyEquiv_pullback_ofCocycle g 2 _ _) w hw dℚ τ hdℚ
  have e1 := hKℚ.symm.trans hdegℚ
  rw [← hptℚ] at e1
  exact ⟨w, hw, by rwa [hwμ], hbijℚ.1 e1⟩

/-- **The degree as an evaluation on a fundamental cycle.** Let `X` be a smooth projective
complex curve and `z` a finite `2`-cycle of `X^an` whose class, transported to `X(ℂ)`, is the
fundamental class of `X`. For an invertible module `L` and a cocycle `χ` representing the image
of `c₁(L)` in `H²(X^an; ℂ)`, `⟨χ, z⟩ = deg L`. -/
theorem eval_eq_invertibleCurveDegree [IsProper (X ↘ Spec (.of ℂ))]
    (hsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) (hdim1 : topologicalKrullDim X = 1)
    (hproj : MMP.Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (z : Chain ℂ (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1)) (hz : bd ℂ 1 z = 0)
    (hfund : IsVarietyFundamentalClass ℂ (natCast_one_eq_dimension hdim1)
      (finiteCycleClass (Y := TopCat.of (UnderlyingSpace ℂ X))
        (postcomp ℂ ⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := X)).continuous⟩ (1 + 1) z)
        (bd_postcomp_homeomorphUnderlyingSpace_eq_zero hz)))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (χ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) → ℂ)
    (hχ : χ ∈ relCocycles ℂ (Set.univᶜ : Set (Analytification.space (X ↘ Spec (.of ℂ)))) (1 + 1))
    (hχc : cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) χ hχ =
      singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) :
    eval χ z = ((invertibleCurveDegree ℂ (X ↘ Spec (.of ℂ)) hdim1.le L : ℚ) : ℂ) := by
  classical
  let g : TopCat.of (UnderlyingSpace ℂ X) ⟶ Analytification.space (X ↘ Spec (.of ℂ)) :=
    TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩
  haveI : (X ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) :=
    ⟨by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩
  let P : TopCat.{0} := TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ)))
  let p : TopCat.of (UnderlyingSpace ℂ X) ⟶ P :=
    TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (X ↘ Spec (.of ℂ)))
  haveI : Subsingleton P := inferInstanceAs (Subsingleton (UnderlyingSpace ℂ (Spec (.of ℂ))))
  let τ : Simp P 0 := (P.toSSetObjEquiv _).symm
    (ContinuousMap.const _ (Classical.arbitrary (UnderlyingSpace ℂ (Spec (.of ℂ)))))
  obtain ⟨cWℂ, hcWℂ, -, hbijℂ⟩ :=
    existsUnique_isVarietyFundamentalClass ℂ natCast_zero_eq_dimension_spec
  obtain ⟨dℂ, hdℂ⟩ := exists_cyc_coeff_eq_one ℂ τ
  have hptℂ := eq_homologyEquiv_symm_mk_of_isVarietyFundamentalClass_zero hcWℂ dℂ τ hdℂ
  obtain ⟨φ, hφ, hφc⟩ := cohomologyWithSupports.exists_ofCocycle_eq 2 (algebraicFirstChernClass L)
  obtain ⟨w, hw, hwℚ, hdegw⟩ :=
    exists_finiteCycleClass_eval_eq_invertibleCurveDegree hsm hdim1 hproj L φ hφ hφc
  have hcz : relativeSingularCohomologyEquiv ℂ (g ⁻¹' Set.univ)ᶜ 2
      ((cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ) g Set.univ 2).hom
        (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))) =
      Submodule.Quotient.mk ⟨cochainPullback ℂ g 2 χ,
        cochainPullback_mem_relCocycles g (fun _ hx ↦ hx) hχ⟩ := by
    rw [← hχc]
    exact relativeSingularCohomologyEquiv_pullback_ofCocycle g 2 χ hχ
  have hcw : relativeSingularCohomologyEquiv ℂ (g ⁻¹' Set.univ)ᶜ 2
      ((cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ) g Set.univ 2).hom
        (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))) =
      Submodule.Quotient.mk ⟨cochainPullback ℂ g 2
          (singularCohomology.cochainMap (Int.castRingHom ℂ) 2 φ),
        cochainPullback_mem_relCocycles g (fun _ hx ↦ hx)
          (singularCohomology.cochainMap_mem_relCocycles _ hφ)⟩ := by
    rw [← hφc, singularCohomology.mapCoeff_ofCocycle]
    exact relativeSingularCohomologyEquiv_pullback_ofCocycle g 2 _ _
  have e3 := eval_eq_of_finiteCycleClass_eq p (UnderlyingSpace.isProperMap_map (K := ℂ) _) hcz
    hcw (hfund.eq (isVarietyFundamentalClass_mapRange_ratCast hwℚ)) dℂ τ hdℂ
    (by rw [← hptℂ]; exact hbijℂ.1)
  have e4 : (fun σ ↦ cochainPullback ℂ g 2 χ
      ((⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := X)).continuous⟩ :
        C(ComplexPoints (X ↘ Spec (.of ℂ)), UnderlyingSpace ℂ X)).comp σ)) = χ := by
    funext σ
    rw [cochainPullback_apply]
    congr 1
  rw [eval_postcomp, e4] at e3
  rw [e3, ← hdegw]
  exact eval_mapRange_intCast_ratCast (fun σ ↦ φ (g.hom.comp σ)) w

/-- A scheme smooth of relative dimension one over `ℂ` and projective has dimension one. -/
theorem topologicalKrullDim_eq_one [AlgebraicGeometry.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))] : topologicalKrullDim X = 1 := by
  exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of ℂ)) 1

/-- **Positivity of an ample class on a fundamental cycle.** On a smooth projective complex
curve `X`, for a finite `2`-cycle `z` of `X^an` representing the fundamental class, every cocycle
representing the image in `H²(X^an; ℂ)` of the first Chern class of an ample invertible module
takes a positive real value on `z`. -/
theorem exists_pos_eval_eq_of_isAmple
    [AlgebraicGeometry.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    (z : Chain ℂ (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1)) (hz : bd ℂ 1 z = 0)
    (hfund : IsVarietyFundamentalClass ℂ (natCast_one_eq_dimension (topologicalKrullDim_eq_one))
      (finiteCycleClass (Y := TopCat.of (UnderlyingSpace ℂ X))
        (postcomp ℂ ⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := X)).continuous⟩ (1 + 1) z)
        (bd_postcomp_homeomorphUnderlyingSpace_eq_zero hz))) :
    ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      MMP.Intersection.IsAmple ℂ L →
      ∀ (χ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) → ℂ)
        (hχ : χ ∈ relCocycles ℂ
          (Set.univᶜ : Set (Analytification.space (X ↘ Spec (.of ℂ)))) (1 + 1)),
        cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) χ hχ =
          singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L) →
        ∃ q : ℝ, 0 < q ∧ SingularCochain.eval χ z = q := by
  intro L _ hL χ hχ hχc
  haveI : IsProper (X ↘ Spec (.of ℂ)) :=
    isProper_of_isProjectiveMorphism _ (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ))
  have hdim1 : topologicalKrullDim X = 1 := topologicalKrullDim_eq_one
  haveI : IsCurve ℂ (X ↘ Spec (.of ℂ)) := (isCurve_iff ℂ _).2 ⟨inferInstance, hdim1⟩
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 1 _
  have hsm := MMP.Flips.isSmoothScheme_of_smooth (X ↘ Spec (.of ℂ))
  have : Stacks.Ample.IsInvertibleModule X L := ‹_›
  have hpos := invertibleCurveDegree_pos_of_isAmple_of_isCurve ℂ (X ↘ Spec (.of ℂ)) hdim1.le L
    ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).1 (MMP.Intersection.IsAmple.stacksIsAmple hL))
  refine ⟨(invertibleCurveDegree ℂ (X ↘ Spec (.of ℂ)) hdim1.le L : ℝ), by exact_mod_cast hpos, ?_⟩
  rw [eval_eq_invertibleCurveDegree hsm hdim1 inferInstance z hz hfund L χ hχ hχc]
  push_cast
  rfl

end Curve

end MMP.Analytic.PolarizationPositivity
